{-# LANGUAGE TemplateHaskell #-}

module Test where

import PrimerOrden as P

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.State.Lazy
import Data.Char
import Data.List

import Test.QuickCheck 

type Prs a = StateT String Maybe a

item = StateT (\str -> case str of {[] -> Nothing; x:xs -> Just (x,xs)})

sat :: (Char -> Bool) -> Prs Char
sat p = do
  c <- item
  if p c then return c else mzero

char :: Char -> Prs Char
char c = sat (== c)

space :: Prs String
space = many $ sat isSpace

str :: String -> Prs String
str [] = return ""
str (x:xs) = do
  c <- char x
  cs <- str xs
  return (c:cs)

tok :: Prs a -> Prs a
tok p = do
  space
  a <- p
  space
  return a

symb :: String -> Prs String
symb = tok . str

symprs :: String -> a -> Prs a
symprs xs a = symb xs >> return a

termP :: Prs Term
termP = fun <|> var

var :: Prs Term
var = fmap Var $ tok $ some $ sat isAlpha

fun :: Prs Term
fun = do
  f <- tok $ some $ sat isLower
  symb "("
  ts <- terms
  symb ")"
  return $ P.Fun f ts

terms :: Prs [Term]
terms = auxTerms <|> fmap (: []) termP <|> return []
  where
    auxTerms = do
      t <- termP
      symb ","
      (t :) <$> terms

formulaP :: Prs Formula
formulaP = bin <|>
           neg <|>
           cuant <|>
           predicado <|>
           symprs "V" Verdadero <|>
           symprs "F" Falso

predicado :: Prs Formula
predicado = do
  p <- tok $ some $ sat isUpper
  symb "("
  ts <- terms
  symb ")"
  return $ Predicado p ts

neg :: Prs Formula
neg = do
  symb "¬"
  No <$> formulaP

bin :: Prs Formula
bin = do
  symb "("
  f <- formulaP
  op <- symprs "/\\" Conj <|>
        symprs "\\/" Disy <|>
        symprs "->" Impl <|>
        symprs "<->" Equiv
  g <- formulaP
  symb ")"
  return $ op f g

cuant :: Prs Formula
cuant = do
  cua <- symprs "∀" ForAll <|> symprs "∃" Exist
  x <- tok $ some $ sat isAlpha
  symb "."
  f <- formulaP
  return $ cua x f

readTerm :: String -> Maybe Term
readTerm xs = case runStateT termP xs of
                Nothing -> Nothing
                Just (t,[]) -> Just t
                Just _ -> Nothing

readFormula :: String -> Maybe Formula
readFormula xs = case runStateT formulaP xs of
                   Nothing -> Nothing
                   Just (t,[]) -> Just t
                   Just _ -> Nothing

term :: Int -> Gen Term
term n = do
  lv <- chooseInt (0,n)
  genTerm lv
  where
    genTerm lv
      | lv <= 0 = do
          n <- chooseInt (1,3)
          b <- arbitrary
          if b then
            Var <$> vectorOf n (chooseEnum ('a','z'))
            else
            flip P.Fun [] <$> vectorOf n (chooseEnum ('a','z'))
      | otherwise = do
          ts <- listOf $ term (lv - 1)
          t <- genTerm (lv - 1)
          x <- chooseInt (0, length ts-1)
          let (t1,t2) = splitAt x ts
          n <- chooseInt (1,3)
          f <- vectorOf n (chooseEnum ('a','z'))
          return $ P.Fun f $ t1 ++ [t] ++ t2

formula :: Int -> Gen Formula
formula n = do
  lv <- chooseInt (0,n)
  genFormula lv
  where
    genFormula lv
      | lv <= 0 = do
          b <- arbitrary
          if b then
            elements [Verdadero,Falso]
            else do
            n <- chooseInt (1,3)
            Predicado <$> (vectorOf n $ chooseEnum ('A','Z')) <*> (vectorOf n $ term 2)
      | otherwise = do
          n <- chooseInt (1,3)
          case n of
            1 -> No <$> genFormula (lv-1)
            2 -> do
              op <- elements [Conj,Disy,Impl,Equiv]
              f <- genFormula (lv-1)
              g <- formula (lv-1)
              b <- arbitrary
              return $ if b then op f g else op g f
            3 -> do
              cuant <- elements [ForAll, Exist]
              n <- chooseInt (1,3)
              x <- vectorOf n $ chooseEnum ('a','z')
              cuant x <$> genFormula (lv - 1)

showTerm :: Property
showTerm = forAll (term 2) aux
  where
    aux t = case readTerm (show t) of
              Nothing -> False
              Just t' -> t == t'

check_showTerm :: Int -> IO ()
check_showTerm n = quickCheck $ withMaxSuccess n showTerm

prop_showTerm :: Property
prop_showTerm = withMaxSuccess pruebas showTerm

showFormula :: Property
showFormula = forAll (formula 15) aux
  where
    aux f = case readFormula (show f) of
              Nothing -> False
              Just f' -> f == f'

check_showFormula :: Int -> IO ()
check_showFormula n = quickCheck $ withMaxSuccess n showTerm

prop_showFormula :: Property
prop_showFormula = withMaxSuccess pruebas showFormula

termLk :: Int -> [Simbolo] -> Gen (Term, [Simbolo])
termLk n lk = do
  lv <- chooseInt (0,n)
  genTerm lv lk
  where
    genTerm lv lk
      | lv <= 0 = do
          b <- arbitrary
          n <- chooseInt (1,3)
          if b then
            if null lk then do
              x <- vectorOf n (chooseEnum ('a','z'))
              return $ (Var x, [x])
            else do
              x <- oneof [elements lk, vectorOf n (chooseEnum ('a','z')) `suchThat` (not . (`elem` lk))]
              return $ (Var x, if (x `elem` lk) then [] else [x])
            else do
            f <- vectorOf n $ chooseEnum ('a','z')
            return $ (P.Fun f [], [])
      | otherwise = do
          f <- vectorOf n $ chooseEnum ('a','z')
          (ts, vs) <- unzip <$> listOf (termLk (lv-1) lk)
          (t, vs') <- genTerm (lv-1) lk
          n <- chooseInt (0, length ts-1)
          let (ts1, ts2) = splitAt n ts
          return (P.Fun f (ts1 ++ [t] ++ ts2), (nub $ concat vs) `union` vs')

formulaVars :: Int -> Gen (Formula, [Simbolo], [Simbolo])
formulaVars n = do
  lv <- chooseInt (0,n)
  genFormula lv []
  where
    aux n xs = do
      lv <- chooseInt (0,n)
      genFormula lv xs
    genFormula lv lk
      | lv <= 0 = do
          b <- arbitrary
          if b then do
            e <- elements [Verdadero, Falso]
            return (e,lk,[])
            else do
            n <- chooseInt (1,3)
            p <- vectorOf n $ chooseEnum ('A','Z')
            (ts, vs) <- unzip <$> vectorOf n (termLk 2 lk)
            return (Predicado p ts, lk, nub $ concat vs)
      | otherwise = do
          n <- chooseInt (1,4)
          case n of
            1 -> do
              (f, lk', nlk) <- genFormula (lv-1) lk
              return (No f, lk', nlk)
            2 -> do
              op <- elements [Conj,Disy,Impl,Equiv]
              (f,lk1,nlk1) <- genFormula (lv-1) lk
              (g,lk2,nlk2) <- aux (lv-1) lk
              b <- arbitrary
              return $ (if b then op f g else op g f, lk1 `union` lk2, nlk1 `union` nlk2)
            _ -> do
              cuant <- elements [ForAll, Exist]
              n <- chooseInt (1,3)
              x <- vectorOf n (chooseEnum ('a','z')) `suchThat` (not . (`elem` lk))
              (f, lk', nlk) <- genFormula (lv-1) ([x] `union` lk)
              return (cuant x f, lk', nlk)

equiv :: (Eq a) => [a] -> [a] -> Bool
equiv xs ys = all (`elem` ys) xs && all (`elem` xs) ys

libresOk :: Property
libresOk = forAll (formulaVars 15) (\(f,_,free) -> equiv (libres f) free)

check_libres :: Int -> IO ()
check_libres n = quickCheck $ withMaxSuccess n libresOk

prop_libres :: Property
prop_libres = withMaxSuccess pruebas libresOk

ligadasOk :: Property
ligadasOk = forAll (formulaVars 15) (\(f,linked,_) -> equiv (ligadas f) linked)

check_ligadas :: Int -> IO ()
check_ligadas n = quickCheck $ withMaxSuccess n ligadasOk

prop_ligadas :: Property
prop_ligadas = withMaxSuccess pruebas ligadasOk

termWithNot :: Int -> [Simbolo] -> Gen Term
termWithNot n l = do
  lv <- chooseInt (0,n)
  genTerm lv l
  where
    genTerm lv xs
      | lv <= 0 = do
          n <- chooseInt (1,3)
          Var <$> (vectorOf n (chooseEnum ('a','z')) `suchThat` (not . (`elem` xs)))
      | otherwise = do
          ts <- listOf $ genTerm (lv - 1) xs
          n <- chooseInt (1,3)
          f <- vectorOf n $ chooseEnum ('a','z')
          return $ P.Fun f ts

subs :: Int -> Gen (Formula, Simbolo, Term)
subs n = do
  (f, linked, free) <- formulaVars n `suchThat` (\(_,linked,free) -> not $ null (free \\ linked))
  v <- elements (free \\ linked)
  t <- termWithNot 1 linked
  return (f,v,t)

subsOk :: Property
subsOk = forAll (subs 15) (\(f,v,t) -> ok f (subsv1 f (v,t)) v t)
  where
    ok Verdadero Verdadero _ _ = True
    ok Falso Falso _ _ = True
    ok (Predicado xs ts) (Predicado ys us) v t = xs == ys && chk ts us v t
    ok (No f) (No g) v t = ok f g v t
    ok (Conj f1 f2) (Conj g1 g2) v t = ok f1 g1 v t && ok f2 g2 v t
    ok (Disy f1 f2) (Disy g1 g2) v t = ok f1 g1 v t && ok f2 g2 v t
    ok (Impl f1 f2) (Impl g1 g2) v t = ok f1 g1 v t && ok f2 g2 v t
    ok (Equiv f1 f2) (Equiv g1 g2) v t = ok f1 g1 v t && ok f2 g2 v t
    ok (ForAll x f) (ForAll y g) v t = x == y && ok f g v t
    ok (Exist x f) (Exist y g) v t = x == y && ok f g v t
    ok _ _ _ _ = False
    chk [] [] _ _ = True
    chk (Var x:xs) (t':ys) v t
      | x == v = t' == t && chk xs ys v t
      | otherwise = Var x == t' && chk xs ys v t
    chk (P.Fun f ts:xs) (P.Fun g us:ys) v t = f == g && chk ts us v t && chk xs ys v t
    chk _ _ _ _ = False

check_subsv1 :: Int -> IO ()
check_subsv1 n = quickCheck $ withMaxSuccess n subsOk

prop_subsv1 :: Property
prop_subsv1 = withMaxSuccess pruebas subsOk

fvars :: Formula -> [String]
fvars (Predicado _ ts) = concatMap tvars ts
fvars (No f) = fvars f
fvars (Conj f g) = fvars f ++ fvars g
fvars (Disy f g) = fvars f ++ fvars g
fvars (Impl f g) = fvars f ++ fvars g
fvars (Equiv f g) = fvars f ++ fvars g
fvars (ForAll x f) = x : fvars f
fvars (Exist x f) = x : fvars f
fvars _ = []

tvars :: Term -> [String]
tvars (Var s) = [s]
tvars (P.Fun _ ts) = concatMap tvars ts

lvars :: Formula -> [String]
lvars (No f) = lvars f
lvars (Conj f g) = lvars f ++ lvars g
lvars (Disy f g) = lvars f ++ lvars g
lvars (Impl f g) = lvars f ++ lvars g
lvars (Equiv f g) = lvars f ++ lvars g
lvars (ForAll x f) = x : lvars f
lvars (Exist x f) = x : lvars f
lvars _ = []

eqFormula :: Formula -> Gen Formula
eqFormula p@(ForAll x f) = do
  y <- listOf1 (chooseEnum ('a','z')) `suchThat` (not . (`elem` fvars p)) 
  g <- susFormula f [(x,y)]
  return $ ForAll y g
eqFormula p@(Exist x f) = do
  y <- listOf1 (chooseEnum ('a','z')) `suchThat` (not . (`elem` fvars p))
  g <- susFormula f [(x,y)]
  return $ Exist y g
eqFormula (Conj f g) = Conj <$> eqFormula f <*> eqFormula g
eqFormula (Disy f g) = Disy <$> eqFormula f <*> eqFormula g
eqFormula (Impl f g) = Impl <$> eqFormula f <*> eqFormula g
eqFormula (Equiv f g) = Equiv <$> eqFormula f <*> eqFormula g
eqFormula (No f) = No <$> eqFormula f
eqFormula p = return p

susFormula :: Formula -> [(String,String)] -> Gen Formula
susFormula p@(ForAll x f) xs = do
  y <- listOf1 (chooseEnum ('a','z')) `suchThat` (not . (`elem` (uncurry union (unzip xs) `union` fvars p)))
  g <- susFormula f ((x,y):xs)
  return $ ForAll y g
susFormula p@(Exist x f) xs = do
  y <- listOf1 (chooseEnum ('a','z')) `suchThat` (not . (`elem` (uncurry union (unzip xs) `union` fvars p)))
  g <- susFormula f ((x,y):xs)
  return $ Exist y g
susFormula (Conj f g) xs = Conj <$> susFormula f xs <*> susFormula g xs
susFormula (Disy f g) xs = Disy <$> susFormula f xs <*> susFormula g xs
susFormula (Impl f g) xs = Impl <$> susFormula f xs <*> susFormula g xs
susFormula (Equiv f g) xs = Equiv <$> susFormula f xs <*> susFormula g xs
susFormula (No f) xs = No <$> susFormula f xs
susFormula (Predicado s ts) xs = return $ Predicado s $ map (aux xs) ts
  where
    aux xs (Var x) = case lookup x xs of
                       Nothing -> Var x
                       Just y -> Var y
    aux xs (P.Fun f ts) = P.Fun f $ map (aux xs) ts
susFormula p _ = return p

alfaFormulas :: Int -> Gen (Formula, Formula)
alfaFormulas n = do
  f <- formula n
  f' <- eqFormula f
  return (f,f')

notAlfaFormulas :: Int -> Gen (Formula, Formula)
notAlfaFormulas n = do
  f <- formula n
  f' <- formula n `suchThat` diff f
  return (f,f')
  where
    diff (ForAll _ _) (ForAll _ _) = False
    diff (Exist _ _) (Exist _ _) = False
    diff (Conj _ _) (Conj _ _) = False
    diff (Disy _ _) (Disy _ _) = False
    diff (Impl _ _) (Impl _ _) = False
    diff (Equiv _ _) (Equiv _ _) = False
    diff (No _) (No _) = False
    diff (Predicado _ _) (Predicado _ _) = False
    diff Verdadero Verdadero = False
    diff Falso Falso = False
    diff _ _ = True

alfaEquivalenciaOk :: Property
alfaEquivalenciaOk = forAll (alfaFormulas 15) (uncurry alfaEquivalencia)

alfaEquivalenciaNotOk :: Property
alfaEquivalenciaNotOk = forAll (notAlfaFormulas 15) (not . uncurry alfaEquivalencia)

check_alfaEquivalencia :: Int -> IO ()
check_alfaEquivalencia n = do
  quickCheck $ withMaxSuccess n alfaEquivalenciaOk
  quickCheck $ withMaxSuccess n alfaEquivalenciaNotOk

prop_alfaEquivalencia :: Property
prop_alfaEquivalencia = withMaxSuccess pruebas (alfaEquivalenciaOk .&&. alfaEquivalenciaNotOk)

unificables :: [(Formula, Formula)]
unificables = [ (Disy (Predicado "f" []) (Predicado "f" [Var "o",Var "l",P.Fun "i" [],P.Fun "v" []]), Disy (Predicado "f" []) (Predicado "f" [P.Fun "g" [Var "l"],P.Fun "i" [],P.Fun "i" [],P.Fun "v" []]))
              , (No (Predicado "e" [Var "l",Var "n"]), No (Predicado "e" [P.Fun "f" [Var "x",Var "y",Var "z"],Var "l"]))
              , (Predicado "f" [P.Fun "c" [],Var "o"], Predicado "f" [P.Fun "c" [],Var "o"])
              , (Predicado "f" [P.Fun "c" [],Var "o"], Predicado "f" [Var "x",Var "o"])
              , (Conj (Disy (Predicado "t" [Var "v",Var "j",Var "z"]) (Predicado "n" [Var "d",Var "v"])) (No (Predicado "h" [])), Conj (Disy (Predicado "t" [P.Fun "f" [Var "g"],Var "a",Var "v"]) (Predicado "n" [P.Fun "k" [Var "w", Var "z", P.Fun "c" []],Var "a"])) (No (Predicado "h" [])))]

noUnificables :: [(Formula, Formula)]
noUnificables = [ (Disy (Predicado "f" []) (Predicado "f" [Var "o",Var "l",P.Fun "i" [],P.Fun "v" []]), Disy (Predicado "f" []) (Predicado "f" [P.Fun "g" [Var "l"],P.Fun "i" [],P.Fun "i" [],P.Fun "w" []]))
                , (No (Predicado "e" [Var "l",Var "n"]), No (Predicado "e" [P.Fun "f" [Var "x",Var "y",Var "n"],Var "l"]))
                , (Predicado "f" [P.Fun "c" [Var "g"],Var "o"], Predicado "f" [Var "g",Var "o"])
                , (Predicado "f" [P.Fun "c" [],Var "o"], Predicado "g" [Var "x",Var "o"])
                , (Conj (Disy (Predicado "t" [Var "v",Var "j",Var "z"]) (Predicado "n" [Var "d",Var "v"])) (No (Predicado "h" [])), Conj (Disy (Predicado "t" [Var "v",Var "j",Var "z"]) (Predicado "n" [Var "v",P.Fun "x" [Var "u", Var "v", Var "w"]])) (No (Predicado "h" [])))]

aplicaUnificador :: Formula -> Unificador -> Formula
aplicaUnificador f [] = f
aplicaUnificador f (x:xs) = aplicaUnificador (subsv1 f x) xs

check_uni :: (Formula,Formula) -> Bool
check_uni (x,y) = case unifica x y of
                    Nothing -> False
                    Just xs -> aplicaUnificador x xs == aplicaUnificador y xs

unificables_ok :: Property
unificables_ok = once $ foldr (\x acc -> whenFail (putStrLn $ "Deberían ser unificables, o su unificación no es correcta:\n" ++ show (fst x) ++ "\n" ++ show (snd x)) (check_uni x) .&&. acc) (property True) unificables

check_not_uni :: (Formula,Formula) -> Bool
check_not_uni (x,y) = case unifica x y of {Nothing -> True; _ -> False}

no_unificables_ok :: Property
no_unificables_ok = once $ foldr (\x acc -> whenFail (putStrLn $ "No deberían ser unificables:\n" ++ show (fst x) ++ "\n" ++ show (snd x)) (check_not_uni x) .&&. acc) (property True) noUnificables

prop_unificacion :: Property
prop_unificacion = once $ unificables_ok .&&. no_unificables_ok

check_unificacion :: IO ()
check_unificacion = quickCheck prop_unificacion

tienen_resolvente :: [(Clausula,Clausula)]
tienen_resolvente = [ ([Predicado "P" [Var "x"], Predicado "Q" [P.Fun "f" [Var "x"]]]
                      ,[Predicado "P" [Var "z"], No (Predicado "Q" [P.Fun "f" [Var "y"]])])
                    , ([Predicado "P" [Var "x"], Predicado "Q" [Var "x"]]
                      ,[No (Predicado "P" [Var "y"]),Predicado "R" [Var "y"]])
                    , ([Predicado "O" [P.Fun "c" [Var "z"]], Predicado "P" [Var "x",Var "y"], No (Predicado "Q" [Var "z"])]
                      ,[Predicado "P" [Var "w"], Predicado "Q" [P.Fun "f" [Var "a", Var "b"]], Predicado "R" [Var "k"]])
                    , ([Predicado "P" [Var "x"]]
                      ,[No (Predicado "P" [P.Fun "f" [Var "a", Var "b", Var "c"]])])
                    , ([Predicado "P" [Var "x",Var "y"], Predicado "R" [Var "x",Var "y"]]
                      ,[No (Predicado "P" [P.Fun "f" [Var "y",Var "z"], P.Fun "c" []]), Predicado "R" [Var "w",P.Fun "a" []]])]

no_tienen_resolvente :: [(Clausula,Clausula)]
no_tienen_resolvente = [ ([Predicado "P" [Var "x"], Predicado "Q" [P.Fun "f" [Var "x"]]]
                         ,[Predicado "P" [Var "x"], No (Predicado "Q" [P.Fun "f" [Var "y"]])])
                       , ([Predicado "P" [Var "x"], Predicado "Q" [Var "x"]]
                         ,[No (Predicado "J" [Var "y"]),Predicado "R" [Var "y"]])
                       , ([Predicado "O" [P.Fun "c" [Var "z"]], Predicado "P" [Var "x",Var "y"], Predicado "Q" [Var "z"]]
                         ,[Predicado "P" [Var "w"], Predicado "Q" [P.Fun "f" [Var "a", Var "b"]], Predicado "R" [Var "k"]])
                       , ([Predicado "P" [Var "x"]]
                         ,[No (Predicado "P" [P.Fun "f" [Var "x", Var "y", Var "z"]])])
                       , ([Predicado "P" [Var "x",Var "y"], Predicado "R" [Var "x",Var "y"]]
                         ,[No (Predicado "P" [P.Fun "f" [Var "y",Var "z"], P.Fun "c" []]), Predicado "R" [Var "y",P.Fun "a" []]])]

resolvente_ok :: Property
resolvente_ok = once $ foldr (\x acc -> whenFail (putStrLn $ show x ++ "\nSí deben tener resolvente") (uncurry resolvente x) .&&. acc) (property True) tienen_resolvente

resolvente_no_ok :: Property
resolvente_no_ok = once $ foldr (\x acc -> whenFail (putStrLn $ show x ++ "\nNo deben tener resolvente") (not (uncurry resolvente x)) .&&. acc) (property True) no_tienen_resolvente

prop_resolvente :: Property
prop_resolvente = once $ resolvente_ok .&&. resolvente_no_ok

check_resolvente :: IO ()
check_resolvente = quickCheck $ once $ resolvente_ok .&&. resolvente_no_ok

resolventes :: [(Clausula,Clausula,Clausula)]
resolventes = [ ([Predicado "P" [Var "x"], Predicado "Q" [P.Fun "f" [Var "x"]]]
                ,[Predicado "P" [Var "z"], No (Predicado "Q" [P.Fun "f" [Var "y"]])]
                ,[Predicado "P" [Var "y"],Predicado "P" [Var "z"]])
              , ([Predicado "P" [Var "x"], Predicado "Q" [Var "x"]]
                ,[No (Predicado "P" [Var "y"]),Predicado "R" [Var "y"]]
                ,[Predicado "Q" [Var "y"],Predicado "R" [Var "y"]])
              , ([Predicado "O" [P.Fun "c" [Var "z"]], Predicado "P" [Var "x",Var "y"], No (Predicado "Q" [Var "z"])]
                ,[Predicado "P" [Var "w"], Predicado "Q" [P.Fun "f" [Var "a", Var "b"]], Predicado "R" [Var "k"]]
                ,[Predicado "O" [P.Fun "c" [P.Fun "f" [Var "a",Var "b"]]],Predicado "P" [Var "x",Var "y"],Predicado "P" [Var "w"],Predicado "R" [Var "k"]])
              , ([Predicado "P" [Var "x"]]
                ,[No (Predicado "P" [P.Fun "f" [Var "a", Var "b", Var "c"]])]
                ,[])
              , ([Predicado "P" [Var "x",Var "y"], Predicado "R" [Var "x",Var "y"]]
                ,[No (Predicado "P" [P.Fun "f" [Var "y",Var "z"], P.Fun "c" []]), Predicado "R" [Var "w",P.Fun "a" []]]
                ,[Predicado "R" [P.Fun "f" [P.Fun "c" [],Var "z"],P.Fun "c" []],Predicado "R" [Var "w",P.Fun "a" []]])]

sonUnificables :: Formula -> Formula -> Bool
sonUnificables f g = case unifica f g of
                       Nothing -> False
                       _ -> True

unifElem :: Formula -> Clausula -> Bool
unifElem f = foldr (\x acc -> if sonUnificables f x then True else acc) False

equivClauses :: Clausula -> Clausula -> Bool
equivClauses xs ys = all (`unifElem` xs) ys && all (`unifElem` ys) xs

res_check :: (Clausula, Clausula, Clausula) -> Bool
res_check (x,y,z) = resolucion x y `equivClauses` z

resolucion_ok :: Property
resolucion_ok = once $ foldr (\x acc -> whenFail (putStrLn $ "La resolución entre:\n" ++ show (fst' x) ++ "\ny\n" ++ show (snd' x) ++ "\nDebería ser:\n" ++ show (trd x)) $ res_check x .&&. acc) (property True) resolventes
  where
    fst' (x,_,_) = x
    snd' (_,x,_) = x
    trd (_,_,x) = x

prop_resolucion :: Property
prop_resolucion = resolucion_ok

check_resolucion :: IO ()
check_resolucion = quickCheck resolucion_ok

return []
runTests :: IO Bool
runTests = $quickCheckAll

main :: IO ()
main = const () <$> runTests
