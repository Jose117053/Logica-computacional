module Main where

import Sudoku (Sudoku, sudokuFormula)
import SAT.MiniSat (solve)
import Data.Map.Lazy (toList)
import Data.Char
import Data.List

sudoSolve :: Sudoku -> Int-> Maybe Sudoku
sudoSolve s tamanio = fmap (map fst . filter snd . toList) $
              solve $
              sudokuFormula s tamanio

parseLine :: Int -> Int -> String -> [(Int,Int,Int)]
parseLine n tamanio str = map (uncurry $ (,,) n) $
                  filter ((/= 0) . snd) $
                  zip [1..tamanio] $
                  map digitToInt str

printSol :: Int -> Int ->[(Int,Int,Int)] -> String 
printSol n tamanio xs
              | n > tamanio = ""
              | otherwise = (++ ("\n" ++ printSol (n+1) tamanio xs)) $
                            ((show n ++ espacios (show n) ++ " | ") ++) $ --IntToDigit imprime en formado hexadecimal
                            foldr (\x acc -> show (trd x) ++ espacios (show (trd x)) ++ acc) [] $
                            sortBy (\(_,a,_) (_,b,_) -> compare a b) $
                            filter ((== n) . fst') xs 
  where
    fst' (a,_,_) = a
    trd (_,_,c) = c

sudoReader :: [(Int,Int,Int)] -> Int -> Int -> IO [(Int,Int,Int)]
sudoReader xs n tamanio 
            | n > tamanio = return xs
            | otherwise = do
                putStrLn $
                  "Ingresa los números de la fila " ++
                  show n ++
                  " (los espacios en blanco se denotan con un 0):"
                x <- getLine
                if any (not . isDigit) x || length x /= tamanio then do
                  putStrLn "No es una fila válida"
                  sudoReader xs n tamanio
                  else
                  sudoReader (xs ++ parseLine n tamanio x) (n+1) tamanio

readSolve :: Int -> IO ()
readSolve tamanio = do
  xs <- sudoReader [] 1 tamanio
  case sudoSolve xs tamanio of
    Nothing -> putStrLn "El sudoku no tiene solucion"
    Just sol -> do
      putStrLn "La solución es la siguiente:"
      putStrLn (margenIzquierdo tamanio ++ "  | " ++ auxputStrl tamanio 1 )
      putStrLn ("-----"++margenSuperior tamanio)
      putStrLn $ printSol 1 tamanio sol

espacios :: String -> String 
espacios numero 
         | length numero == 1 = " " ++ espacios (tail numero)
         | otherwise = " "

margenIzquierdo :: Int -> String 
margenIzquierdo tamanio 
       | length (show tamanio ) == 1 = espacios (show tamanio)
       | length (show tamanio) == 2 = " " ++ espacios (show tamanio)
       | length (show tamanio ) == 3 = "  " ++ espacios (show tamanio)
       | otherwise = "esto no deberia pasar"                           -- solo cuando hay sudokus de 100x100(3digitos).
                                                                       -- todavia se pueden considerar mayores

margenSuperior :: Int -> String 
margenSuperior tamanio 
        | tamanio== 0 = ""
        | otherwise = "---" ++ margenSuperior(tamanio-1)

auxputStrl :: Int -> Int-> String 
auxputStrl tamanio actual
           | tamanio == 1 =show actual
           | otherwise = show actual ++ espacios(show actual) ++ auxputStrl (tamanio -1) (actual+1)

main :: IO ()
main = do
  putStrLn "==== Sudoku Solver 1.0.0. ===="
  putStrLn "1. Resolver Sudoku\n2. Salir"
  putStrLn "Elige una opción:"
  x <- getLine
  if any (not . isDigit) x then
    putStrLn "No es una opción válida" >> main
    else
    case read x :: Int of
      1 -> do
        putStrLn "Ingresa el tamaño del sudoku:"
        tamanio <- getLine
        case reads tamanio :: [(Int, String)] of
          [(tam, "")] -> readSolve (tam*tam) >> main
          _           -> putStrLn "Entrada no válida. Inténtalo de nuevo." >> main
      2 -> return ()
      _ -> putStrLn "No es una opción válida" >> main
