Luna Rivera Carlos Alonso 318076814

Vázquez Dávila José Adolfo 423033366

1. BuenFin

Se definen qué cosas son articulos, colores y descuentos. se tiene que encontrar tuplas de la forma (nombre,articulo, color,descuento), se verifica que el articulo sea un Articulo definido, lo mismo para el color y descuento, el tercer color se asume que es amarillo, pues solo se especifican 2. Dado que cada persona compro un solo articulo, estos tienen que ser diferentes(tambien el color y descuento). Se modelan los hechos asegurando que se excluyan los demás (definiciones de rojo_descuento y pantalon_descuento). 

Al hacer la consulta tuplas(X,Y,Z) se devuelve

X = t(curry, sombrilla, amarillo, 10), Y = t(kleene, chamarra, azul, 50), Z = t(russell, pantalon, rojo, 25).

Es el resultado esperado.

2. Particion

se calcula la mitad de la longitud de la lista recibida y se le asigna a L2, L2 aun no tiene elementos, append se asegura de que L2 concatenado con L3 resulte en L1, esto sucede solo si L2 tiene los elementos de la primera mitad de L1 y L3 el resto.

3. Combina

Si alguna lista es vacia, se regresa la otra lista. Si ambos tienen elementos, el caso en que X es menor o igual a Y se agrega X a la lista final, luego se hace recursion sobre la cola XS y la lista Y:YS, el caso en que X es mayor a Y es analogo.

4. Gcd

si alguno de los dos numeros recibidos es 0, se devuelve el otro numero, de lo contrario se procede a hacer uso del algoritmo de Euclides de forma recursiva. Se hace uso de un predicado auxiliar para no tener que estar calculando el valor absoluto de los valores en cada recursión, solo es necesario calcularlos una sola vez. 

Dos numeros son coprimos si el maximo comun divisor de ambos es 1.

5. Agrupa

Se devuelve la lista vacia si la lista recibida es vacia, si la lista tiene un solo elemento, se regresa una lista con la lista que contiene al elemento, si hay más elementos tenemos dos casos, si la cabeza de la lista y la cabeza de la cola son iguales se concatenan en una sola lista, en un principio la lista resultante es la cabeza de la lista de listas, la cola es el resto de la lista a evaluar. Si la cabeza de la lista y la cabeza de la cola son diferentes, se procede a crear una nueva lista con el elemento diferente, haciendo recursion.

6. Pertenece

Si el elemento recibido es la cabeza de la lista se regresa true, de lo contrario se procede a hacer recurssion sobre la cola de la lista.

7. Elimina

Si la lista es vacia no hay nada que eliminar y se regresa la lista vacia. 
Si el elemento recibido no es la cabeza de la lista, se añade la cabeza a la lista final y se hace recursion sobre la cola hasta encontrar el elemento, cuando lo encuentra simplemente se regresa el resto de la lista.

8. Camino

Primero se definen qué cuartos están conectados, se hace uso de una funcion auxiliar, el cual registra los cuartos por los que ya se pasó. Dado los cuartos x,y se buscan todos los z's tales que hay una puerta de x a z, se toma en consideracion si es de la forma (x,z) o (z,x), en principio se añade x a la lista de visitados, si hay una puerta de x a z, se añade z a la lista de visitados (verificando primero que z no haya sido visitado antes), se hace esto de manera recursiva hasta que hallemos una puerta que vaya de z a y, en dado caso, en la siguiente recursion se llegara al caso base (y,y) y por lo tanto sí hay un camino de x a y, se regresa la lista hasta el momento.
