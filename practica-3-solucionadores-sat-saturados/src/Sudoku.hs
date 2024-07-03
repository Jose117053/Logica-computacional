{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module Sudoku where

import SAT.MiniSat
import Data.List
import Prelude hiding(sqrt)
import Prelude (sqrt)


type Sudoku = [(Int,Int,Int)]

sudokuFormula :: Sudoku -> Int -> Formula (Int,Int,Int)
sudokuFormula sudoku tamanio=
                     cada_elemento_ocurre sudoku               :&&:
                     cada_casilla_es_unica tamanio             :&&:
                     toda_fila_no_repite_numero tamanio        :&&:
                     toda_columna_no_repite_numero tamanio     :&&:
                     todo_cuadro_no_repite_numero (floor (sqrt (fromIntegral tamanio)))

cada_elemento_ocurre :: Sudoku -> Formula (Int, Int, Int)
cada_elemento_ocurre sudoku= All [ Var (i,j,n) | (i,j,n) <-sudoku]

un_numero_por_casilla ::Int ->Int -> Int-> Formula(Int, Int, Int)
un_numero_por_casilla i j tamanio= ExactlyOne [Var (i,j,n) | n<-[1..tamanio]]

cada_casilla_es_unica :: Int -> Formula (Int, Int, Int)
cada_casilla_es_unica tamanio= All [un_numero_por_casilla i j tamanio |i<-[1..tamanio], j<-[1..tamanio] ]

en_fila_no_se_repite_numero :: Int->Int-> Int->Formula (Int, Int, Int)
en_fila_no_se_repite_numero i n tamanio= ExactlyOne [Var (i,j,n) | j<-[1..tamanio]]

toda_fila_no_repite_numero :: Int ->Formula (Int, Int, Int)
toda_fila_no_repite_numero tamanio = All [en_fila_no_se_repite_numero i n tamanio| i<-[1..tamanio],n<-[1..tamanio]]

en_columna_no_se_repite_numero :: Int -> Int -> Int -> Formula (Int, Int, Int)
en_columna_no_se_repite_numero j n tamanio= ExactlyOne [Var (i,j,n) | i<-[1..tamanio]]

toda_columna_no_repite_numero :: Int -> Formula (Int, Int, Int)
toda_columna_no_repite_numero tamanio= All [en_columna_no_se_repite_numero j n tamanio| j<-[1..tamanio],n<-[1..tamanio]]

en_cuadrado_no_se_repite_numero :: Int -> Int-> Int -> Int-> Formula (Int, Int, Int)
en_cuadrado_no_se_repite_numero i j n base= ExactlyOne [Var (i+iterador,j+recorredor,n) | iterador<-[0..base-1], recorredor<-[0..base-1]]

todo_cuadro_no_repite_numero :: Int-> Formula (Int, Int, Int)
todo_cuadro_no_repite_numero base = All [en_cuadrado_no_se_repite_numero i j n base| i<-intervaloAux base, j<-intervaloAux base, n<-[1..(base*base)]]

intervaloAux :: Int -> [Int]
intervaloAux base = nub [1+(x*y) | x<-[0..base-1], y<-[1..base], mod (x*y) base == 0]
