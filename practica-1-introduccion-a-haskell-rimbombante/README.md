Luna Rivera Carlos Alonso	318076814
Vázquez Dávila José Adolfo 	423033366


1. 	Traductor a "f"

Se recorre el string recibido de manera recursiva, verificando si el caracter actual es una vocal, de ser así se concatenará esta vocal con 'f' y con esa vocal actual en su forma minuscula, para luego concatenarlo con la llamada recursiva de la siguiente letra. Si no es una vocal, simplemente se concatena esa letra con la llamada recursiva de la siguiente letra.

2. 	Mezcla

El algoritmo asume que las dos listas ya estan ordenadas, compara las cabezas de ambas listas y con el elemento minimo construye la lista mezclada, luego construye el resto de la lista mezclada llamando a la misma función, sin incluir la cabeza que fue elemento mínimo, si una de las listas que recibe es vacía agrega en su totalidad la lista no-vacia
El algoritmo concluye cuando reciba dos listas vacias

3. 	Palíndromo

El algoritmo genera una versión de la cadena sin espacios ya que estos no se consideran en un palindromo, luego convirtiendo las mayusculas a minuscilas por el mismo motivo, compara esta cadena con su reverso, si son iguales la cadena original es un palíndromo

4. 	Prefijo Común

Se utilizan 2 algoritmos auxiliares, "comun" se encarga de regresar el prefijo comun mas largo entre dos cadenas, "prefijoComunAux" ocupa este ultimo para devolver el prefijo comun mas largo de una lista de Strings, se utiliza foldl pues es una misma verificacion para cada elemento de la lista, en este caso la funcion que recibe foldl es "comun", y como base toma el primer elemento de la lista, luego se recorre la lista de izquierda a derecha, regresando el prefijo comun mas largo entre estos 2, se hace recursivamente hasta el ultimo elemento de la lista.

5. 	Diferencia

El algoritmo recibe dos listas, selecciona la cabeza de la primer lista y verifica si es un elemento en la segunda, de no serlo lo agrega a una tercer lista y se vuelve a llamar con las mismas listas, menos la cabeza de la primer lista. Si la cabeza es un elemento de la segunda lista, hace la llamada recursiva sin agregar la cabeza.
El algoritmo concluye cuando la primer lista que recibe es vacía

6. 	Producto Punto


El algoritmo recibe dos vectores en forma de listas y calcula su producto punto. Para eso construye una tercer lista multiplicando cada elemnto de la primer lista con cada elemento de la segunda y sumando todos los elementos de la tercer lista

7. 	Triadas Pitagóricas

Recibiendo un numero 'n' , sse genera una lista de triadas, donde sus 3 elementos cumplen con las propiedades de que el tercer elemento 'c' existe entre 0 y n, el segundo elemento 'b' existe entre 0 y c-1 y el primer elemento 'a' existe entre 0 y b-1 y además a^2 + b^2 = c^2

8. 	Combinaciones

Se utiliza el algoritmo auxiliar "dosFijos", se encarga de regresar todas las triplas posibles cuando el primer valor de la tripla es fija, para esto, además del primer valor, en cada recursion la segunda entrada va tomando valores que no ha tomado antes, teniendo estos 2 valores, la tercera entrada recorrerá la cola de la segunda entrada de la tripla, asegurando así que no se repitan triplas. Luego en la funcion principal simplemente se asegura de que la primera entrada tome todos los posibles valores de la lista, a excepcion de los ultimos 2, pues la ultima tripla tiene los ultimos 3 elementos

9. 	binHfold

Si el arbol recibido es una Hoja con valor "a", se regresa el resultado de aplicar la funcion f al valor "a" con la base "b" Si el arbol recibido es una Rama con árbol izquierdo y derecho, se hace recursion sobre la rama derecha hasta llegar al caso base, cuando esto suceda, se hará recursion sobre la rama izquierda.

10.	binHenum

Usamos un método auxiliar "binHenumAux" que recibe un entero 'n' y un arbol, regresando una tupla de un arbol y un entero.
Si se llega a una Hoja genera una nueva Hoja con una tupla del elemento de la hoja original y el numero recibido regresando la tupla de la nueva Hoja y n+1
Si se llega a una Rama se genera una nueva Rama con el elemento izquierdo siendo el resultado de aplicar "binHenumAux" al elemento izquierdo original y el numero 'n' y el elemnto derecho siendo el resultado de aplicar "binHenumAux" al elemento derecho original y el numero 'm', donde m es el numero en la tupla que regresa binHenumAux en el elemento izquierdo, regresa la tupla con la nueva Rama y el numero m+1.
binHenum toma el arbol de la tupla que regresa binHenumAux con el numero 0 y el arbol que recibió

11.	binFold

Si se llega a un nodo sin ambos hijos, se regresara la base de f Si el arbol recibido tiene ambos hijos, se hará recursion primero sobre el hijo derecho utilizandola funcion de la forma f a (binFold f b right) asegurando así de que lleguemos hasta el nodo que está mas a la derecha, en este caso el nodo a representa el padre del hijo derecho, por lo que nos aseguramos de que "a" sea la base para la funcion f, el valor regresado en esta recursion será usado como valor base en la recursion del hijo izquierdo, asegurando así, que el recorrido se haga in-order.

12. 	binEnum

Este algoritmo sigue el mismo principio que el de binHenum con un método auxiliar "aux" que recibe un entero 'n' y un arbol, regresando una tupla de un arbol y un entero.
Pero ahora como hay nodos intermedios, además de los de las Hojas el escape de la recursión no es una Hoja, si no un Nodo Vacío, en cuyo caso regresa una tupla con el Nodo Vacío y 'n'.
En caso de no recibir un nodo vacío se aplica aux primero al elemento izquierdo del nodo, luego al contenido del nodo, con 'n' en este caso siendo la 'm' que regresa aux en el lado izquierdo, y por ultimo aplicamos aux al nodo derecho con la 'n' siendo m+1, al final aux regresa la tupla del nuevo (Nodo a left right) con el numero ' m' ' que regreso aux del lado derecho.
