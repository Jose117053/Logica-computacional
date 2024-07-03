module Test where

import Intro
import Data.Char
import Data.List (nub)
import Test.QuickCheck

-------------- traduceF --------------
ocur :: [String] -> String -> Bool
ocur [] _ = True
ocur _ [] = False
ocur s@(x:xs) l@(y:ys) = if isPrefix x l then
                           ocur xs (drop (length x) l)
                         else
                           ocur s ys

prop_translateVowels :: String -> Bool
prop_translateVowels = ocur .
                       (map ((:) <*> ('f' :) . (: []) . toLower) .
                         filter (`elem` "AEIOUaeiou")) <*>
                       traduceF

prop_translateCons :: String -> Bool
prop_translateCons = ocur . splitCons <*> traduceF

splitCons [] = []
splitCons xs = first : splitCons second
  where
    (first,t) = span (not . (`elem` "AEIOUaeiou")) xs
    second = dropWhile (`elem` "AEIOUaeiou") t

loremIpsum = "Lorem ipsum dolor sit amet, consectetur adipiscing elit. Pellentesque facilisis est leo, id egestas augue posuere non. Suspendisse eget justo eu nisl volutpat bibendum. Sed vestibulum turpis urna, ut auctor turpis mattis a. Curabitur venenatis odio vestibulum risus iaculis malesuada. Donec ut libero dignissim, efficitur diam nec, pulvinar ex. Class aptent taciti sociosqu ad litora torquent per conubia nostra, per inceptos himenaeos. Vestibulum ante ipsum primis in faucibus orci luctus et ultrices posuere cubilia curae; Quisque rutrum placerat eros, et pretium felis tristique quis. Aliquam consectetur finibus tortor in vulputate. Curabitur lectus turpis, egestas et suscipit at, gravida id dolor. Curabitur pretium volutpat convallis."

loforefemIfipsufum = "Loforefem ifipsufum dofolofor sifit afamefet, cofonsefectefetufur afadifipifiscifing efelifit. Pefellefentefesqufuefe fafacifilifisifis efest lefeofo, ifid efegefestafas afaufugufuefe pofosufueferefe nofon. Sufuspefendifissefe efegefet jufustofo efeufu nifisl vofolufutpafat bifibefendufum. Sefed vefestifibufulufum tufurpifis ufurnafa, ufut afaufuctofor tufurpifis mafattifis afa. Cufurafabifitufur vefenefenafatifis ofodifiofo vefestifibufulufum rifisufus ifiafacufulifis mafalefesufuafadafa. Dofonefec ufut lifibeferofo difignifissifim, efeffificifitufur difiafam nefec, pufulvifinafar efex. Clafass afaptefent tafacifitifi sofocifiofosqufu afad lifitoforafa toforqufuefent pefer cofonufubifiafa nofostrafa, pefer ifincefeptofos hifimefenafaefeofos. Vefestifibufulufum afantefe ifipsufum prifimifis ifin fafaufucifibufus oforcifi lufuctufus efet ufultrificefes pofosufueferefe cufubifilifiafa cufurafaefe; Qufuifisqufuefe rufutrufum plafaceferafat eferofos, efet prefetifiufum fefelifis trifistifiqufuefe qufuifis. Afalifiqufuafam cofonsefectefetufur fifinifibufus tofortofor ifin vufulpufutafatefe. Cufurafabifitufur lefectufus tufurpifis, efegefestafas efet sufuscifipifit afat, grafavifidafa ifid dofolofor. Cufurafabifitufur prefetifiufum vofolufutpafat cofonvafallifis."

-------------- mezcla --------------
isOrdered :: Ord a => [a] -> Bool
isOrdered [] = True
isOrdered [x] = True
isOrdered (x:y:xs) = x <= y && isOrdered (y:xs)

prop_mergePreserves :: Property
prop_mergePreserves = forAll ((,) <$> orderedList <*> orderedList)
                      (isOrdered . uncurry mezcla)

prop_mergeElements :: [Int] -> [Int] -> Bool
prop_mergeElements xs ys = length result == length (xs ++ ys) &&
                           all (`elem` result) (xs ++ ys) &&
                           all (`elem` xs ++ ys) result
  where
    result = mezcla xs ys

-------------- palindromo --------------

insertSpaces :: String -> Gen String
insertSpaces [] = return []
insertSpaces (x:xs) = do
  b <- arbitrary
  rest <- insertSpaces xs
  return $ if b then (x  : ' ' : rest) else (x : rest)

changeCaps :: String -> Gen String
changeCaps [] = return []
changeCaps (x:xs) = do
  b <- arbitrary
  rest <- changeCaps xs
  return $ if b then (toUpper x : rest) else (x : rest)

palindromes :: Gen String
palindromes = do
  str <- listOf $ chooseEnum ('a', 'z')
  b <- arbitrary
  newstr <- if b then
              (++ foldl (flip (:)) [] str) . (str ++) . (: []) <$> choose ('a', 'z')
            else
              return $ str ++ foldl (flip (:)) [] str
  cap <- changeCaps newstr
  insertSpaces cap

notPalindromes :: Gen String
notPalindromes = do
  str <- listOf1 $ chooseEnum ('a', 'z')
  str2 <- vectorOf (length str) (chooseEnum ('a','z')) `suchThat` ((/= str) . foldl (flip (:)) [])
  b <- arbitrary
  notPal <- if b then
              (++ str2) . (str ++) . (: []) <$> choose ('a','z')
              else
              return $ str ++ str2
  cap <- changeCaps notPal
  insertSpaces cap

prop_palindromosOk :: Property
prop_palindromosOk = forAll palindromes palindromo

prop_palindromosNotOk :: Property
prop_palindromosNotOk = forAll notPalindromes (not . palindromo)

-------------- prefijoComun --------------

isPrefix :: String -> String -> Bool
isPrefix [] _ = True
isPrefix _ [] = False
isPrefix (x:xs) (y:ys) = x == y && isPrefix xs ys

commonPrefixes :: Gen (String, [String])
commonPrefixes = (.) . (,) <*> map . (++) <$> arbitrary <*> listOf1 arbitrary

prop_prefixIsCorrect :: Property
prop_prefixIsCorrect = forAll commonPrefixes (\(_,xs) -> all (isPrefix $ prefijoComun xs) xs)

prop_prefixIsIntended :: Property
prop_prefixIsIntended = forAll commonPrefixes (\(p,xs) -> p `isPrefix` prefijoComun xs)

-------------- diferencia --------------

intSet :: Gen [Int]
intSet = fmap nub $ arbitrary

prop_minusNone :: Property
prop_minusNone = forAll intSet fun
  where
    fun xs = let first = take (length xs `div` 2) xs
                 second = drop (length xs `div` 2) xs
             in
               diferencia first second == first

prop_minusOk :: Property
prop_minusOk = forAll ((,) <$> intSet <*> intSet) $ uncurry fun
  where
    fun xs ys = all (not . (`elem` diferencia xs ys)) ys

-------------- productoPunto --------------

prop_productoPunto :: [Integer] -> [Integer] -> Bool
prop_productoPunto xs ys = foldr (+) 0 ((*) <$> xs <*> ys) == productoPunto xs ys

-------------- triada --------------

prop_triadaOk :: Property
prop_triadaOk = forAll (chooseInt (0,100)) (\n -> all (\(a,b,c) -> a < b && b < c && c <= n && a^2 + b^2 == c^2) $ triada n)

prop_triadaElements :: Property
prop_triadaElements = forAll (chooseInt (0,100)) (\n -> triada n == nub (triada n))

-------------- combinaciones --------------

prop_combinationElements :: Property
prop_combinationElements = forAll intSet
                           (\xs -> let n = length xs
                                       result = combinaciones xs
                                   in
                                     length result == (n^3-3*n^2+2*n) `div` 6)

prop_combinationContains = forAll (intSet `suchThat` ((> 3) . length)) 
                           (\xs -> let comb = combinaciones xs
                                   in
                                     all (\x -> any (contains x) comb ) xs .&&.
                                     forAll ((,) <$> elements comb <*> elements comb)
                                     (\(x,y) -> x /= y ==> not $ equiv x y))
  where
    equiv (a,b,c) (d,e,f) = all (`elem` [a,b,c]) [d,e,f]
    contains x (a,b,c) = x == a || x == b || x == c

-------------- binHfold --------------

instance Arbitrary a => Arbitrary (BinH a) where
  arbitrary = do
    lv <- fmap abs $ chooseInt (0,30)
    arb lv
      where
        arb :: Int -> Gen (BinH a)
        arb n | n <= 0 = fmap Hoja arbitrary
              | otherwise = do
                  b <- arbitrary
                  first <- arb (n-1)
                  lv <- chooseInt (0,n-1)
                  second <- arb lv
                  return $ if b then
                             Rama first second
                           else
                             Rama second first
  shrink = genericShrink

instance Foldable BinH where
  foldr = binHfold

binHtoList :: BinH a -> [a]
binHtoList (Hoja a) = [a]
binHtoList (Rama l r) = binHtoList l ++ binHtoList r

prop_binHfold :: BinH Int -> Bool
prop_binHfold = (==) . binHtoList <*> foldr (:) []

-------------- binHenum --------------

prop_binHenumNums :: BinH Int -> Bool
prop_binHenumNums = all (uncurry (==)) . zip [0..] . map fst . binHtoList . binHenum

binHsameTopo :: BinH a -> BinH b -> Bool
binHsameTopo (Hoja _) (Hoja _) = True
binHsameTopo (Rama l1 r1) (Rama l2 r2) = binHsameTopo l1 l2 && binHsameTopo r1 r2
binHsameTopo _ _ = False

prop_binHenumPreservesTopo :: BinH Int -> Bool
prop_binHenumPreservesTopo = binHsameTopo <*> binHenum

-------------- binFold --------------

instance Arbitrary a => Arbitrary (Bin a) where
  arbitrary = do
    lv <- chooseInt (-1,30)
    arb lv
    where
      arb n | n <= -1 = return Vacio
            | otherwise = do
                b <- arbitrary
                first <- arb (n-1)
                lv <- chooseInt (-1,n-1)
                second <- arb lv
                elem <- arbitrary
                return $ if b then
                           Nodo elem first second
                         else
                           Nodo elem second first
  shrink = genericShrink

instance Foldable Bin where
  foldr = binFold

binToList :: Bin a -> [a]
binToList Vacio = []
binToList (Nodo a l r) = binToList l ++ [a] ++ binToList r

prop_binFold :: Bin Int -> Bool
prop_binFold = (==) . binToList <*> foldr (:) []

-------------- binEnum --------------

prop_binEnumNums :: Bin Int -> Bool
prop_binEnumNums = all (uncurry (==)) . zip [0..] . map fst . binToList . binEnum

binSameTopo :: Bin a -> Bin b -> Bool
binSameTopo Vacio Vacio = True
binSameTopo (Nodo _ l1 r1) (Nodo _ l2 r2) = binSameTopo l1 l2 && binSameTopo r1 r2
binSameTopo _ _ = False

prop_binEnumPreservesTopo :: Bin Int -> Bool
prop_binEnumPreservesTopo = binSameTopo <*> binEnum

-------------- ejecución de las pruebas  --------------

main :: IO ()
main = do
  let n = pruebas
  putStrLn "Pruebas traduceF:"
  ef1 <- quickCheckResult $ withMaxSuccess n $ prop_translateVowels
  ef2 <- quickCheckResult $ withMaxSuccess n $ prop_translateCons
  ef3 <- quickCheckResult $ traduceF loremIpsum === loforefemIfipsufum
  putStrLn "Pruebas palindromo:"
  pal1 <- quickCheckResult $ withMaxSuccess n $ prop_palindromosOk
  pal2 <- quickCheckResult $ withMaxSuccess n $ prop_palindromosNotOk
  putStrLn "Pruebas prefijoComun:"
  pre1 <- quickCheckResult $ withMaxSuccess n $ prop_prefixIsCorrect
  pre2 <- quickCheckResult $ withMaxSuccess n $ prop_prefixIsIntended
  putStrLn "Pruebas mezcla:"
  mg1 <- quickCheckResult $ withMaxSuccess n $ prop_mergePreserves
  mg2 <- quickCheckResult $ withMaxSuccess n $ prop_mergeElements
  putStrLn "Pruebas diferencia:"
  dif1 <- quickCheckResult $ withMaxSuccess n $ prop_minusNone
  dif2 <- quickCheckResult $ withMaxSuccess n $ prop_minusOk  
  putStrLn "Pruebas productoPunto:"
  dot1 <- quickCheckResult $ withMaxSuccess n $ prop_productoPunto
  putStrLn "Pruebas triada:"
  tr1 <- quickCheckResult $ withMaxSuccess n $ prop_triadaOk
  tr2 <- quickCheckResult $ withMaxSuccess n $ prop_triadaElements
  putStrLn "Pruebas combinaciones:"
  com1 <- quickCheckResult $ withMaxSuccess n $ prop_combinationElements
  com2 <- quickCheckResult $ withMaxSuccess n $ prop_combinationContains
  putStrLn "Pruebas binHfold:"
  hfold1 <- quickCheckResult $ withMaxSuccess n $ prop_binHfold
  putStrLn "Pruebas binHenum:"
  henum1 <- quickCheckResult $ withMaxSuccess n $ prop_binHenumNums
  henum2 <- quickCheckResult $ withMaxSuccess n $ prop_binHenumPreservesTopo
  putStrLn "Pruebas binFold:"
  fold1 <- quickCheckResult $ withMaxSuccess n $ prop_binFold
  putStrLn "Pruebas binEnum:"
  enum1 <- quickCheckResult $ withMaxSuccess n $ prop_binEnumNums
  enum2 <- quickCheckResult $ withMaxSuccess n $ prop_binEnumPreservesTopo
  let results = [ef1,ef2,ef3,pal1,pal2,pre1,pre2,mg1,mg2,dif1,dif2,dot1,tr1,tr2,com1,com2,hfold1,henum1,henum2,fold1,enum1,enum2]
  let success = length $ filter isSuccess results
  putStrLn $ "Pruebas exitosas: " ++ show success ++ "/22"
  let ef = fromIntegral $ length $ filter isSuccess [ef1,ef2,ef3]
  let pal = fromIntegral $ length $ filter isSuccess [pal1,pal2]
  let pre = fromIntegral $ length $ filter isSuccess [pre1,pre2]
  let mg = fromIntegral $ length $ filter isSuccess [mg1,mg2]
  let dif = fromIntegral $ length $ filter isSuccess [dif1,dif2]
  let dot = fromIntegral $ if isSuccess dot1 then 1 else 0
  let tr = fromIntegral $ length $ filter isSuccess [tr1,tr2]
  let com = fromIntegral $ length $ filter isSuccess [com1,com2]
  let hfold = fromIntegral $ if isSuccess hfold1 then 1 else 0
  let henum = fromIntegral $ length $ filter isSuccess [henum1,henum2]
  let fold = fromIntegral $ if isSuccess fold1 then 1 else 0
  let enum = fromIntegral $ length $ filter isSuccess [enum1,enum2]
  let calif = (ef/3+pal/2+pre/2+mg/2+dif/2+dot+tr/2+com/2+hfold+henum/2+fold+enum/2) / 12 * 10
  putStrLn $ "Calificación tentativa: " ++ show calif
