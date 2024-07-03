module Prop where
import Data.List

-- ------------------------------------------------------------------------------
-- Definicion de los tipos de datos siguientes:
-- Prop para representar las fórmulas proporsicionales usando los
-- constructores T, F, Var, Neg, Conj, Disy, Impl y Equiv para formulas atomicas,
-- negaciones, conjunciones, implicaciones y equivalencias respectivamente.
-- ------------------------------------------------------------------------------

data Prop = T | F | Var String
          | Neg Prop
          | Conj Prop Prop | Disy Prop Prop
          | Impl Prop Prop | Equiv Prop Prop deriving Eq

type Estado = [String]


-- ------------------------------------------------------------------------------
-- Ejercicio 1.
-- Definir un ejemplar de la clase Show para el tipo de dato Prop que muestre una
-- cadena que represente las formulas proposicionales en notacion infija.
-- ------------------------------------------------------------------------------

instance Show Prop where
    show :: Prop -> String
    show (Var p) = p
    show T = " T "
    show F = " F "
    show (Neg prop) ="¬" ++ show prop
    show (Conj p q) = "( " ++ show p ++ " /\\ " ++ show q ++ " )"
    show (Disy p q) = "( " ++ show p ++ " \\/ " ++ show q ++ " )"
    show (Impl p q) = "( " ++ show p ++ " -> " ++ show q ++ " )"
    show (Equiv p q) = "( " ++ show p ++ " <-> " ++ show q ++ " )"

-- ------------------------------------------------------------------------------
-- Ejercicio 2
-- Definir la funcion conjPotencia, tal que la aplicación de la funcion es la
-- lista de todos los subconjuntos de x.
-- ------------------------------------------------------------------------------
conjPotencia :: [a] -> [[a]]
conjPotencia [] = [[]]
conjPotencia (x:xs) = [x:ys | ys<-aux] ++ aux
             where aux = conjPotencia xs

-- ------------------------------------------------------------------------------
-- Ejercicio 3.
-- Definir la función vars::Prop -> [String] que devuelve el conjunto de variables
-- proposicionales de una fórmula.
-- ------------------------------------------------------------------------------

vars :: Prop -> [String]
vars (Var p) = [p]
vars T = []
vars F = []
vars (Neg prop) = vars prop
vars (Conj p q) = vars p ++ vars q
vars (Disy p q) = vars p ++ vars q
vars (Impl p q) = vars p ++ vars q
vars (Equiv p q) = vars p ++ vars q

-- ------------------------------------------------------------------------------
-- Ejercicio 4.
-- Definir la función interpreta que dada una formula proposicional y un estado
-- regrese la interpretación obtenida de la fórmula en dicho estado.
-- ------------------------------------------------------------------------------

interpretacion :: Prop -> Estado -> Bool
interpretacion (Var p) e = if(p  `elem` e) then True else False
interpretacion T _ = True
interpretacion F _ = False
interpretacion (Neg prop) estado = not (interpretacion prop estado)
interpretacion (Conj p q) e = interpretacion p e && interpretacion q e
interpretacion (Disy p q) e = interpretacion p e || interpretacion q e
interpretacion (Impl p q) e = interpretacion (Disy (Neg p) q) e
interpretacion (Equiv p q) e = interpretacion p e == interpretacion q e



-- ------------------------------------------------------------------------------
-- Ejercicio 5.
-- Definir la funcion modelos :: Prop -> [Estado] que dada una fórmula devuelve
-- una lista de estados que satisfacen a dicha fórmula.
-- ------------------------------------------------------------------------------
modelos :: Prop -> [Estado]
modelos formula = [estados | estados <- conjPotencia (nub (vars formula)), interpretacion formula estados]

-- ------------------------------------------------------------------------------
-- Ejercicio 6.
-- Definir una función que dada una fórmula proposicional, indique si es una 
-- tautologia.
-- Firma de la funcion: tautologia:: Prop -> Bool
-- ------------------------------------------------------------------------------

tautologia :: Prop -> Bool
tautologia T = True
tautologia F = False
tautologia formula= length (modelos formula) == 2^length (nub (vars formula))

-- ------------------------------------------------------------------------------
-- Ejercicio 7.
-- Definir una funcion que dada una fórmula proposicional, indique si es una
-- contradicción.
-- firma de la funcion: contradiccion :: Prop -> Bool
-- ------------------------------------------------------------------------------
contradiccion :: Prop -> Bool
contradiccion formula = null (modelos formula)

-- ------------------------------------------------------------------------------
-- Ejercicio 8.
-- Definir una función que dada una fórmula proposicional phi, verifique si es 
-- satisfacible.
-- ------------------------------------------------------------------------------
esSatisfacible :: Prop -> Bool
esSatisfacible T = True
esSatisfacible F = False
esSatisfacible p = True `elem` [interpretacion p e | e <- conjPotencia (nub(vars p))]

-- ------------------------------------------------------------------------------
-- Ejercicio 9.

-- Definir una función que elimine dobles negaciones y aplique las
-- leyes de DeMorgan dada una fórmula proposicional phi.
-- ------------------------------------------------------------------------------
deMorgan :: Prop -> Prop
deMorgan T = T
deMorgan F = F
deMorgan (Var p) = Var p
deMorgan (Neg (Var p)) = Neg (Var p)
deMorgan (Neg (Neg prop)) = deMorgan prop

deMorgan (Neg (Conj p q)) = deMorgan ( Disy (Neg (deMorgan p)) (Neg (deMorgan q)))
deMorgan (Conj p q) = Conj (deMorgan p) (deMorgan q)

deMorgan (Neg (Disy p q)) = deMorgan ( Conj (Neg (deMorgan p)) (Neg (deMorgan q)))
deMorgan (Disy p q) = Disy (deMorgan p) (deMorgan q)

deMorgan (Neg (Impl p q)) = deMorgan (Neg (elimImplicacion (Impl p q)))
deMorgan (Impl p q) = deMorgan (elimImplicacion (Impl p q))

deMorgan (Neg (Equiv p q)) = deMorgan (Neg (elimEquivalencias (Equiv p q)))
deMorgan (Equiv p q) = deMorgan (elimEquivalencias (Equiv p q))

-- ------------------------------------------------------------------------------
-- Ejercicio 10.
-- Definir una función que elimine las implicaciones lógicas de una proposición
-- ------------------------------------------------------------------------------
elimImplicacion :: Prop -> Prop
elimImplicacion T = T
elimImplicacion F = F
elimImplicacion (Var p) = Var p
elimImplicacion (Neg prop) = Neg (elimImplicacion prop)
elimImplicacion (Conj p q) = Conj (elimImplicacion p) (elimImplicacion q)
elimImplicacion (Disy p q) = Disy (elimImplicacion p) (elimImplicacion q)
elimImplicacion (Impl p q) = Disy (Neg (elimImplicacion p)) (elimImplicacion q)
elimImplicacion (Equiv p q) = elimImplicacion (elimEquivalencias (Equiv p q))

-- ------------------------------------------------------------------------------
-- Ejercicio 11.
-- Definir una funcion que elimine las equivalencias lógicas de una proposición.
-- ------------------------------------------------------------------------------
elimEquivalencias :: Prop -> Prop
elimEquivalencias T = T
elimEquivalencias F = F
elimEquivalencias (Var p) = Var p
elimEquivalencias (Neg prop) = Neg (elimEquivalencias prop)
elimEquivalencias (Conj p q) = Conj (elimEquivalencias p) (elimEquivalencias q)
elimEquivalencias (Disy p q) = Disy (elimEquivalencias p) (elimEquivalencias q)
elimEquivalencias (Impl p q) =  Impl (elimEquivalencias p) (elimEquivalencias q)
elimEquivalencias (Equiv p q) = Conj (Impl (elimEquivalencias p) (elimEquivalencias q)) (Impl (elimEquivalencias q) (elimEquivalencias p))


-- ------------------------------------------------------------------------------
-- Número de pruebas a hacer.
-- Puedes cambiar este valor siempre y cuando éste sea mayor o igual a 100.
-- ------------------------------------------------------------------------------
pruebas :: Int
pruebas = 1000
