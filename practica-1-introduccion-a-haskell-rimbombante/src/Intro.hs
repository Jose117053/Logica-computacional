-- | Práctica 1: Introducción a Haskell
-- Profesor: Manuel Soto Romero
-- Ayudante: José Alejandro Pérez Marquez
-- Laboratorio: Erik Rangel Limón

module Intro where

import Data.Char
import GHC.Generics -- Esto es únicamente para las pruebas


traduceF :: String -> String
traduceF [] = ""
traduceF (x:xs)
    | esVocal x = x : 'f' : toLower x : traduceF xs
    | otherwise = x : traduceF xs

esVocal :: Char -> Bool
esVocal x = toLower x `elem` "aeiou";

mezcla :: [Int] -> [Int] -> [Int]
mezcla xs [] = xs
mezcla [] ys = ys
mezcla (x:xs) (y:ys)|min x y == x = x : mezcla xs (y:ys)
                    |min x y == y = y : mezcla (x:xs) ys

palindromo :: String -> Bool
palindromo [] = True
palindromo (x:xs) = map toLower y == map toLower (reverse y)
    where 
          y = sin_espacios (x:xs)
          sin_espacios [] = []
          sin_espacios (x:xs) | x == ' ' = sin_espacios xs
                              | otherwise = x : sin_espacios xs


prefijoComun :: [String] -> String
prefijoComun [] = ""
prefijoComun [x] = x
prefijoComun (x:xs) = prefijoComunAux x xs

prefijoComunAux :: String -> [String] -> String
prefijoComunAux = foldl comun

--Devuelve el prefijo comun mas largo entre dos cadenas

comun :: String -> String -> String
comun [] _ = ""
comun _ [] = ""
comun (x:xs) (y:ys)
   | x == y = x : comun xs ys
   | otherwise = ""

diferencia :: (Eq a) => [a]-> [a] -> [a]
diferencia xs [] = xs
diferencia [] ys = []
diferencia (x:xs) ys  | elem x ys = diferencia xs ys
                      | otherwise = x : diferencia xs ys

productoPunto :: [Integer] -> [Integer] -> Integer
productoPunto xs ys = sum [x * y | x <- xs, y <- ys]

triada :: Int -> [(Int,Int,Int)]
triada n = [(a,b,c) | c <- [0..n]
                    , b <- [0..c-1]
                    , a <- [0..b-1]
                    , a^2 + b^2 == c^2]

combinaciones :: (Eq a) => [a] -> [(a,a,a)]
combinaciones [] =[]
combinaciones [_] = []
combinaciones (x:y:ys)
   | not (null ys) = dosFijos (x:y:ys) ++ combinaciones (y:ys)
   | otherwise = []

--Se establecen las primeras dos entradas como fijas y se
--devuelven todas las triplas posibles con el tercer elemento 
--que toma valores del resto de la lista,se hace recursion manteniendo 
--la primera entrada fija y cambiando la segunda entrada.

dosFijos :: (Eq a) => [a] -> [(a,a,a)]
dosFijos [] =[]
dosFijos (x:y:ys)
   | null ys = []
   | otherwise = [(x,y,c) | c<- ys] ++ dosFijos (x:ys)

data BinH a = Hoja a
            | Rama (BinH a) (BinH a) deriving (Show, Generic) -- Generic
                                                              -- es
                                                              -- úncamente
                                                              -- para
                                                              -- las
                                                              -- pruebas

binHfold :: (a -> b -> b) -> b -> BinH a -> b
binHfold func base_value (Hoja a) = func a base_value
binHfold func base_value (Rama left right) = binHfold func der left
  where
      der = binHfold func base_value right

binHenum :: BinH a -> BinH (Int,a)
binHenum tree = fst (binHenumAux 0 tree)

binHenumAux :: Int -> BinH a -> (BinH (Int,a),Int)
binHenumAux n (Hoja a) = (Hoja (n,a), n+1)
binHenumAux n (Rama l r) = (Rama (fst (binHenumAux n l)) (fst (binHenumAux m r)), snd (binHenumAux m r))
  where m = snd (binHenumAux n l)

data Bin a = Vacio
           | Nodo a (Bin a) (Bin a) deriving (Show, Generic) -- Generic
                                                             -- es
                                                             -- únicamente
                                                             -- para
                                                             -- las
                                                             -- pruebas

binFold :: (a -> b -> b) -> b -> Bin a -> b
binFold f b Vacio = b
binFold f b (Nodo a Vacio Vacio) = f a b
binFold f b (Nodo a left right) = binFold f (f a (binFold f b right)) left

binEnum :: Bin a -> Bin (Int,a)
binEnum tree = fst (aux 0 tree)
   where
      aux::Int -> Bin a -> (Bin (Int,a), Int)
      aux n Vacio = (Vacio, n)
      aux n (Nodo a l r) = let(izq,m) = aux n l
                              (der,z) = aux (m+1) r
                              in (Nodo (m,a) izq der,z)

-- | Número de pruebas

pruebas :: Int
pruebas = 1000 -- Este número indica el número de pruebas que se harán
               -- a cada función, lo pueden modificar siempre y cuando
               -- éste número sea mayor o igual a 100.
