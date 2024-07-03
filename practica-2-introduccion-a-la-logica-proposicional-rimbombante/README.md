1. Show

Por cada conectivo logico (negacion, disyuncion, conjuncion, implicacion, equivalencia) se define su propia representacion, haciendo recursion sobre las proposiciones de cada uno de estos casos, hasta llegar a un caso base (que la proposicion sea una Variable o una constante).

2. ConjPotencia

Dado una lista de tipo a, se regresan todas las combinaciones que resultan de concatenar la cabeza x de la lista con el resultado de hacer recursion sobre la cola xs de la lista, luego a este resultado se le concatena la recursion sobre la cola xs, asegurando así que la cabeza sea distinta en cada llamada recursiva

3. Vars

Dada una proposicion se "ignoran" los conectivos logicos y se hace recursion sobre las proposiciones que conforman dichos conectivos,  hasta llegar al caso base en que la proposicion es una Variable proposicional, de ser así se agrega esta variable a la lista.

4. Interpretacion

Por cada conectivo logico se devuelve el valor de verdad que lo define, en el caso de la negacion de una proposicion, se devuelve la negacion del resultado de hacer recursion sobre la proposicion, para la conjuncion, la interpretacion del resultado de hacer recursion sobre cada proposicion que lo conforma, lo mismo para los demas conectivos, en el caso de la implicacion, primero se pasa a su equivalente en disyuncion.

5. Modelos

Se genera una lista de estados, estos se generan a partir del conjunto potencia de las variables de la formula, pero solo se consideran aquellas en que la interpretacion de la proposicion en ese estado es verdadero

6. Tautologia

Para que una proposicion sea una tautologia, el numero de modelos de la proposicion debe ser igual a 2 elevado al numero de variables proposicionales de la formula

7. Contradiccion

Si la lista generada a partir de la funcion modelos es vacia, quiere decir que ningun estado de las variables hace verdadera a la proposicion, y por lo tanto es una contradiccion

8. esSatisfacible

Se genera una lista de interpretaciones, solo se consideran aquellas que hacen verdadera a la proposicion, si True es parte de esta lista, entonces la proposicion es satisfacible

9. deMorgan

Se considera cada conectivo logico y su negacion, si la formula no está negada se hace recursion sobre las proposiciones que lo conforman, en el caso de la implicacion y equivalencia, se pasa a su forma equivalente que no tenga estos conectivos, si la formula está negada, se hace recursion sobre la negacion de la recursion de cada variable proposicional, al igual que el caso anterior, primero se eliminan las implicaciones y bicondicionales.

10. elimImplicacion

En el caso de la negacion, conjuncion y conjuncion se hace recursion sobre las proposiciones que lo conforman, manteniendo el conectivo logico que lo define, en el caso de la implicacion, se pasa a su forma equivalente de disyuncion, negando la primera proposicion y manteniendo la segunda, pero se hace recursion sobre cada uno de estos, en el caso de la equivalencia, primero se eliminan las equivalencias usando la funcion elimEquivalencias, se hace recursion sobre el resultado.

11. elimEquivalencias

Es analogo a la funcion elimImplicacion, a excepcion de la implicacion y la equivalencia, en la implicacion se mantiene el conectivo pero se hace recursion sobre cada proposicion que lo conforma, en la equivalencia se pasa a su forma equivalente de conjuncion de implicaciones, haciendo recursion sobre cada proposicion.

