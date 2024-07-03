`1. Lemma imp_conj : (P -> Q -> R) <-> (P /\ Q -> R).`

Se divide la demostracion en la ida y la vuelta usando la tactica split.

`2. Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.`

`3. Lemma or_and_not :P \/ Q) /\ ~P -> Q.`

`4. Lemma deMorgan : ~(P \/ Q) <-> (~P /\ ~Q).`

En los ejercicios del 1 al 4 se demuestra igual que en la logica proposicional, pero implementado en coq. Para la disyuncion se hace uso de left o right para demostrar la parte izquierda y derecha respectivamente.

`5. Lemma suma_suc : n + 1 = S n.`

Se utiliza induccion sobre n para su demostracion.

`6. Lemma suma_conm : n + m = m + n.`

Se hace induccion sobre n, se utilizan los lemas auxiliares: 
- neutro (n+0=0)
- suma_n_Sm ( n + S m = S (n + m)).

`7. Lemma mult_dist : p * (n + m) = p * n + p * m. `

Se hace induccion sobre n haciendo uso de los lemas auxiliares:
- mult_0_derecha (n*0=0)
- suma_0_derecha (n+0=n)
- suma_asociativa
- mult_n_Sm (n * (S m) = n * m + n).

`8. gauss`

Si el numero es 0, se regresa 0, en otro caso se suma suma el numero con la recursion de su predecesor.

`9. Lemma gauss_eq : 2 * gauss n = n * (n + 1)`

Se hace induccion sobre n, reescribiendola hasta llegar a la expresion buscada, se hace uso de lemas auxiliares:

- mult_1_derecha : n*1 = n.
- gauss_Sn : gauss (S n) = gauss n + (n+1)
- mult_conm : n*m =m*n
- uno_mas_uno : n + 1 + 1 = n + 2. Se podria generalizar, pero solo lo ocupo una vez.


`10. Lemma concat_assoc : xs ++ ys ++ zs = (xs ++ ys) ++ zs`

Se hace induccion sobre la lista xs.

`11. Lemma rev_concat : reversa (xs ++ ys) = reversa ys ++ reversa xs`

Se hace induccion sobre la lista xs, se hace uso del lema auxiliar concat_nil_derecha el cual prueba que xs ++ [] = xs.

`12. take `

Se regresa la lista vacia si el numero es 0 o si la lista es vacia, en otro caso se concatena la cabeza de la lista con el resultado de hacer recursion sobre el predecesor del numero y la cola de la lista.

`13. drop `

si el numero es 0 se regresa la lista, si la lista es vacia se regresa la lista vacia, en otro caso, al tener la cabeza de la lista, se ignora para despues hacer recursion sobre el predecesor del numero y la cola de la lista.

`14. tdn : xs = take n xs ++ drop n xs`

Se hace induccion sobre n. Si se introduce xs al mismo tiempo que n no funciona, en el paso inductivo se hace un destruct xs para considerar el caso en que es vacia y cuando tiene al menos un elemento.

`15. Lemma ts: take m (drop n xs) = drop n (take (m + n) xs)`

Se hace induccion sobre n, en el paso inductivo se consideran 2 casos más: cuando n es 0 y cuando es distinto de 0. Se hace uso de los siguientes lemas auxiliares:

- take_nil : take n [] = [].
- drop_nil : drop n [] = [].
- drop_Sn : drop (S n) (x :: xs) = drop n xs.
- take_Sn : take (S n) (x :: xs) = x :: take n xs.

`16. Lemma min: take m (take n xs) = take (min m n) xs.`

Se hace induccion sobre la lista xs, en el paso inductivo se consideran 2 casos: cuando n es 0 y cuando es distinto de 0, en este ultimo tambien se considera cuando m es o no 0.


En la mayoria de los ejercicios se hace uso de la induccion, además del reuso de lemas anteriormente definidos.

