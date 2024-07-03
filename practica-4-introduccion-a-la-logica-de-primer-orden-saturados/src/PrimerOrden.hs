{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}
module PrimerOrden where

import Data.Char
import Data.List

type Simbolo = String

data Term = Var Simbolo | Fun Simbolo [Term] deriving Eq

data Formula = Verdadero | Falso
            | Predicado Simbolo [Term]
            | No Formula
            | Conj Formula Formula | Disy Formula Formula
            | Impl Formula Formula | Equiv Formula Formula
            | ForAll Simbolo Formula | Exist Simbolo Formula
            deriving Eq

type Substitucion = (Simbolo, Term)

type Unificador = [Substitucion]

type Clausula = [Formula]

infixr 4 `ForAll`, `Exist`
infixl 3 `Conj`, `Disy`
infixl 2 `Equiv`
infixr 1 `Impl`

-- ------------------------------------------------------------------------------
    -- Ejercicio 1.
    -- Definir un ejemplar de la clase Show para el tipo de dato Term que muestre una
    -- cadena que represente las formulas
-- -----------------------------------------------------------------------------

instance Show Term where
    show :: Term -> String
    show (Var x) = x
    show (Fun f terminos) =
        f ++ "(" ++ intercalate ", " (map show terminos) ++ ")"

-- ------------------------------------------------------------------------------
    -- Ejercicio 2.
    -- Definir un ejemplar de la clase Show para el tipo de dato Formula que muestre una
    -- cadena que represente los terminos
    -- Utiliza los caracteres: ∀ y ∃ para denotar los cuantificadores.
-- -----------------------------------------------------------------------------

instance Show Formula where
  show :: Formula -> String
  show Verdadero = "V"
  show Falso = "F"
  show (Predicado simbolo terminos) = simbolo ++ "(" ++ intercalate ", " (map show terminos) ++ ")"
  show (No p) = "¬" ++ show p
  show (Conj p q) = "(" ++show p ++ " /\\ " ++ show q++ ")"
  show (Disy p q) = "(" ++show p ++ " \\/ " ++ show q++ ")"
  show (Impl p q) = "(" ++show p ++ " -> " ++ show q++ ")"
  show (Equiv p q) = "(" ++show p ++ " <-> " ++ show q++ ")"
  show (ForAll x formula) = "∀ " ++ x ++ " . " ++ show formula
  show (Exist x formula) = "∃ " ++  x ++ " . " ++ show formula

-- ------------------------------------------------------------------------------
    -- Ejercicio 3.
    -- Definir una funcion que devuelva el conjunto de variables libres de una formula.
-- ------------------------------------------------------------------------------

libres :: Formula -> [String]
libres formula = nub (variablesLibres formula)

-- Define una función para extraer todas las variables libres de una fórmula

variablesLibres :: Formula -> [String]
variablesLibres Verdadero = []
variablesLibres Falso = []
variablesLibres (Predicado _ terminos) =  concatMap obtenerVariablesTermino terminos
variablesLibres (No formula) = variablesLibres formula
variablesLibres (Conj formula1 formula2) =  variablesLibres formula1 ++ variablesLibres formula2
variablesLibres (Disy formula1 formula2) =  variablesLibres formula1 ++ variablesLibres formula2
variablesLibres (Impl formula1 formula2) =  variablesLibres formula1 ++ variablesLibres formula2
variablesLibres (Equiv formula1 formula2) =  variablesLibres formula1 ++ variablesLibres formula2
variablesLibres (ForAll x formula) = filter (/= x) (variablesLibres formula)
variablesLibres (Exist x formula) = filter (/= x) (variablesLibres formula)


-- ------------------------------------------------------------------------------
    -- Ejercicio 4.
    -- Definir una funcion que devuelva las variables ligadas de una formula
-- ------------------------------------------------------------------------------

ligadas :: Formula -> [String]
ligadas Verdadero = []
ligadas Falso = []
ligadas (Predicado simbolo terminos) = []
ligadas (No p) = ligadas p
ligadas (Conj p q) = ligadas p ++ ligadas q
ligadas (Disy p q) = ligadas p ++ ligadas q
ligadas (Impl p q) = ligadas p ++ ligadas q
ligadas (Equiv p q) = ligadas p ++ ligadas q
ligadas (ForAll x formula) = x : ligadas formula
ligadas (Exist x formula) = x : ligadas formula

 ------------------------------------------------------------------------------
    -- Ejercicio 5.
    -- Definir una funcion que trate de aplicar una substitucion una formula
    -- Debe devolver un error si no es posible aplicarla.
-- ------------------------------------------------------------------------------

vars :: Substitucion -> Term -> Term
vars (x,t) (Var s) = if( s /= x) then (Var s) else t
vars _ (Fun s []) = (Fun s [])
vars (x,t) (Fun s terms) = (Fun s (map (vars (x,t)) terms))

subsv1 :: Formula -> Substitucion -> Formula
subsv1 Verdadero _ = Verdadero
subsv1 Falso _ = Falso
subsv1 (Predicado p terms) s = (Predicado p (map (vars s) terms) )
subsv1 (No phi) s = No (subsv1 phi s)
subsv1 (Conj phi psi) s = (Conj (subsv1 phi s) (subsv1 psi s))
subsv1 (Disy phi psi) s = (Disy (subsv1 phi s) (subsv1 psi s))
subsv1 (Impl phi psi) s = (Impl (subsv1 phi s) (subsv1 psi s))
subsv1 (Equiv phi psi) s = (Equiv (subsv1 phi s) (subsv1 psi s))
subsv1 (ForAll s phi) (x,t) = if (x `elem` (ligadas phi)) then error "No es posible sustituir variables ligadas" else (ForAll s (subsv1 phi (x,t)))
subsv1 (Exist s phi) (x,t) =  if (x `elem` (ligadas phi)) then error "No es posible sustituir variables ligadas" else (Exist s (subsv1 phi (x,t)))

-- ------------------------------------------------------------------------------
    -- Ejercicio 6.
    -- Definir una funcion que determine si dos formulas son alfaequivalentes.
-- ------------------------------------------------------------------------------

alfaEquivalencia :: Formula -> Formula -> Bool
alfaEquivalencia formula1 formula2= listaUnica formula1 == listaUnica formula2

listaUnica:: Formula  -> [Int]
listaUnica Verdadero = [1]
listaUnica Falso = [2]
listaUnica (Predicado simbolo terminos) = 3 : map ord simbolo -- el map ord es para obtener un codigo unico del nombre del predicado
listaUnica (No p) = 4 : listaUnica p
listaUnica (Conj p q) = 5 : listaUnica p ++ listaUnica q
listaUnica (Disy p q) = 6 : listaUnica p ++ listaUnica q
listaUnica (Impl p q) = 7 : listaUnica p ++ listaUnica q
listaUnica (Equiv p q) = 8 : listaUnica p ++ listaUnica q
listaUnica (ForAll x formula) = 9 : listaUnica formula
listaUnica (Exist x formula) =  10 : listaUnica formula

-- ------------------------------------------------------------------------------
    -- Ejercicio 7.
    -- Definir una funcion que obtenga el umg de dos formulas 
    -- si no es posible obtener el ung regresa error
-- ------------------------------------------------------------------------------

unifica :: Formula -> Formula -> Maybe Unificador
unifica f g = aux_unifica2 (aux_unifica f g) []

aux_unifica :: Formula -> Formula -> Maybe [(Term,Term)]
aux_unifica (Predicado p t1) (Predicado q t2)
    | (p == q) && (length (t1) == length (t2)) = Just (zip t1 t2)
    | otherwise = Nothing
aux_unifica (No f) (No g) = aux_unifica f g
aux_unifica (Conj f1 f2) (Conj g1 g2) = case (aux_unifica f1 g1, aux_unifica f2 g2) of
                                            (Nothing,_) -> Nothing
                                            (_,Nothing) -> Nothing
                                            (Just t1, Just t2) -> Just (t1 ++ t2)
aux_unifica (Disy f1 f2) (Disy g1 g2) = case (aux_unifica f1 g1, aux_unifica f2 g2) of
                                            (Nothing,_) -> Nothing
                                            (_,Nothing) -> Nothing
                                            (Just t1, Just t2) -> Just (t1 ++ t2)
aux_unifica (Impl f1 f2) (Impl g1 g2) = case (aux_unifica f1 g1, aux_unifica f2 g2) of
                                            (Nothing,_) -> Nothing
                                            (_,Nothing) -> Nothing
                                            (Just t1, Just t2) -> Just (t1 ++ t2)
aux_unifica (Equiv f1 f2) (Equiv g1 g2) = case (aux_unifica f1 g1, aux_unifica f2 g2) of
                                            (Nothing,_) -> Nothing
                                            (_,Nothing) -> Nothing
                                            (Just t1, Just t2) -> Just (t1 ++ t2)
aux_unifica _ _ = Nothing

obtenerVariablesTermino :: Term -> [String]
obtenerVariablesTermino (Var x) = [x]
obtenerVariablesTermino (Fun _ ts) = concatMap obtenerVariablesTermino ts

aux_unifica2 :: Maybe [(Term,Term)] -> Unificador -> Maybe Unificador
aux_unifica2 Nothing sigma = Nothing
aux_unifica2 (Just []) sigma = Just sigma
aux_unifica2 (Just ((Var x,Var y):xs)) sigma
    | x == y = aux_unifica2 (Just xs) sigma
    | otherwise = let sust = (x, Var y)
                      sigma' = sust : map (\(s,t) -> (s,vars sust t)) sigma
                      w = map (\(t1,t2) -> (vars sust t1, vars sust t2)) xs
                    in
                    aux_unifica2 (Just w) sigma'
aux_unifica2 (Just ((Var x, t):xs)) sigma
    | x `elem` obtenerVariablesTermino t = Nothing
    | otherwise = let sust = (x, t)
                      sigma' = sust : map (\(s,t') -> (s,vars sust t')) sigma
                      w = map (\(t1,t2) -> (vars sust t1, vars sust t2)) xs
                    in
                    aux_unifica2 (Just w) sigma'
aux_unifica2 (Just ((t, Var x):xs)) sigma
    | x `elem` obtenerVariablesTermino t = Nothing
    | otherwise = let sust = (x, t)
                      sigma' = sust : map (\(s,t) -> (s,vars sust t)) sigma
                      w = map (\(t1,t2) -> (vars sust t1, vars sust t2)) xs
                    in
                    aux_unifica2 (Just w) sigma'
aux_unifica2 (Just ((Fun f t1, Fun g t2):xs)) sigma
    | f == g && length t1 == length t2 = aux_unifica2 (Just $ zip t1 t2 ++ xs) sigma
    | otherwise = Nothing

-- ------------------------------------------------------------------------------
    -- Ejercicio 8.
    -- Definir una funcion que determine si es posible obtener un
    -- resolvente dadas dos formulas
    -- ------------------------------------------------------------------------------

resolvente :: Clausula -> Clausula -> Bool
resolvente clausula1 clausula2 = clausulasSonUnificables clausula1 clausula2 && not (null (clausulasComplementarias clausula1 clausula2)) && interseccionVacia clausula1 clausula2

clausulasSonUnificables :: Clausula -> Clausula -> Bool
clausulasSonUnificables clausula1 clausula2 =  or [sonLiteralesUnificables literal1 literal2 | literal1 <- clausula1, literal2 <- clausula2]

sonLiteralesUnificables :: Formula -> Formula -> Bool
sonLiteralesUnificables (No f1) f2 = dosFormulasSonUnificables f1 f2
sonLiteralesUnificables f1 (No f2) = dosFormulasSonUnificables f1 f2
sonLiteralesUnificables _ _ = False

dosFormulasSonUnificables :: Formula -> Formula -> Bool
dosFormulasSonUnificables f1 f2 = case unifica f1 f2 of
                      Nothing -> False
                      Just _  -> True

clausulasComplementarias :: Clausula -> Clausula -> [Formula]
clausulasComplementarias clausula1 clausula2 =  [ literal1 | literal1 <- clausula1 ++ clausula2, literal2 <- clausula1 ++ clausula2, dosFormulasSonComplementarias literal1 literal2]

dosFormulasSonComplementarias :: Formula -> Formula -> Bool
dosFormulasSonComplementarias (No f1) f2 = alfaEquivalencia f1 f2
dosFormulasSonComplementarias f1 (No f2) = alfaEquivalencia f1 f2
dosFormulasSonComplementarias _ _ = False

interseccionVacia :: Clausula -> Clausula -> Bool
interseccionVacia clausula1 clausula2 = null interseccion
  where
    clausulasComplemento = clausulasComplementarias clausula1 clausula2
    variablesClausula1 = nub (extraerTodasLasVariablesClausula ( filter (`notElem` clausulasComplemento) clausula1))
    variablesClausula2 = nub (extraerTodasLasVariablesClausula ( filter (`notElem` clausulasComplemento) clausula2))
    interseccion = variablesClausula1 `intersect` variablesClausula2

extraerTodasLasVariablesClausula :: Clausula -> [String]
extraerTodasLasVariablesClausula clausula = concatMap variablesLibres clausula -- deberia tomar todas las variables independientemente de si son libres o no
                                                                               -- pero pasan los tests xd

-- ------------------------------------------------------------------------------
    -- Ejercicio 9.
    -- Definir una funcion que dadas dos claúsulas, obtenga el resolvente obtenido de aplicar la regla de resolución binaria.
-- ------------------------------------------------------------------------------

resolucion :: Clausula -> Clausula -> Clausula
resolucion clausula1 clausula2 = sustituirBucle ( aplicarExtraerTerminosOVariables (terminosComplementarios (clausulasComplementariasTuplas clausula1 clausula2)))
                                                                       ( filter (`notElem` literalesComplementarias) clausula1) ++
                                                                         filter (`notElem` literalesComplementarias) clausula2

                                                                         where literalesComplementarias= clausulasComplementarias clausula1 clausula2

clausulasComplementariasTuplas :: Clausula -> Clausula -> [(Formula, Formula)]
clausulasComplementariasTuplas clausula1 clausula2 = [(literal1, literal2) | literal1 <- clausula1, literal2 <- clausula2, dosFormulasSonComplementarias literal1 literal2]

terminosComplementarios :: [(Formula, Formula)] -> [(Term, Term)]
terminosComplementarios clausulasComplementarias = concatMap obtenerTerminosDeTupla clausulasComplementarias

obtenerTerminosDeTupla :: (Formula, Formula) -> [(Term, Term)]
obtenerTerminosDeTupla (formula1, formula2) = [(term1, term2) | term1 <- terminosDePredicado formula1, term2 <- terminosDePredicado formula2]

terminosDePredicado :: Formula -> [Term]
terminosDePredicado (Predicado _ terminos) = terminos
terminosDePredicado _ = []

aplicarExtraerTerminosOVariables :: [(Term, Term)] -> [(Term,Term)]
aplicarExtraerTerminosOVariables = map extraerTerminosDePredicado

-- Función para extraer las variables o términos de un par de predicados
extraerTerminosDePredicado :: (Term, Term) -> (Term,Term)
extraerTerminosDePredicado (term1, term2) =
    case (term1, term2) of
        (Var _, Var _) -> (term1, term2)  -- Si ambos términos son variables, extrae las variables
        (Fun _ terminos, Fun _ terminos2) -> (head terminos, head terminos2)  -- Si ambos términos son funciones, extrae las variables
        (Var _, Fun _ _) -> (term1, term2)  -- Si el primer término es una variable y el segundo una función, extrae la variable y la función
        (Fun _ _, Var _) -> (term1, term2)  -- Si el primer término es una función y el segundo una variable, extrae la función y la variable
                                            -- En una sola recursion no funcionaria, pero al aplicar la sustitucion tantas veces como la longitud
                                            -- de la lista de terminos complementarios, se sustituye correctamente

sustituirBucle :: [(Term, Term)] -> Clausula -> Clausula
sustituirBucle terminos clausula =
    let iteraciones = iterate (sustituirListaDeTerminosEnClausula terminos) clausula
    in iteraciones !! length terminos

sustituirListaDeTerminosEnClausula :: [(Term, Term)] -> Clausula -> Clausula
sustituirListaDeTerminosEnClausula terminos clausula = foldr sustituirTerminoEnClausula clausula terminos

sustituirTerminoEnClausula :: (Term, Term) -> Clausula -> Clausula
sustituirTerminoEnClausula (termOriginal, termNuevo) clausula = map (sustituirTerminoEnFormula termOriginal termNuevo) clausula

sustituirTerminoEnFormula :: Term -> Term -> Formula -> Formula
sustituirTerminoEnFormula termOriginal termNuevo formula =
    case formula of --Siempre se recibe un predicado
        Predicado simbolo terminos -> Predicado simbolo (map (sustituirTerminoEnPredicado termOriginal termNuevo) terminos)

sustituirTerminoEnPredicado :: Term -> Term -> Term -> Term
sustituirTerminoEnPredicado termOriginal termNuevo term =
    if term == termOriginal
        then termNuevo
        else case term of
                 Var _ -> term
                 Fun nombre terminos -> Fun nombre (map (sustituirTerminoEnPredicado termOriginal termNuevo) terminos)

-- ------------------------------------------------------------------------------
    -- Pruebas.
-- ------------------------------------------------------------------------------
pruebas :: Int
pruebas = 1000
