1. Show Term

Se define como se mostraran los terminos dependiendo de si es variable o funcion.

2. Show Formula

Por cada conectivo logico se define su propia representacion, haciendo recursion sobre las formulas, tambien se define la representacion de los cuantificadores.

3. VariablesLibres

Por cada conectivo logico y cuantificador, se hace recursion sobre sus formulas hasta llegar a un predicado, al cual se le extraen los terminos, se excluyen aquellos ligados a los cuantificadores.

4. Libres

Solo se quitan las variables repetidas de aplicar la funcion VariablesLibres a una formula.

5. Ligadas

Por cada conectivo logico, se hace recursion hasta llegar a un cuantificador, al cual se le extraen los terminos que están asociados a él.

6. Vars

Dado una sustitucion y un termino, se aplica la sustitucion al termino.

7. Subsv1

Por cada conectivo logico se hace recursion sobre sus formulas hasta llegar a un predicado, al cual se le aplica la sustitucion recibida.

8.ListaUnica

Dado una formula se regresa una lista unica de enteros que lo representa, esto se logra asignando valores a cada conectivo logico, cuantificador y tipo de termino que está asociado al predicado.

9. AlfaEquivalencia

Se comparan las listas unicas de cada formula, si resultan ser iguales, son alfaequivalentes, en caso contrario no lo son.

10. ObtenerVariablesTermino

Se obtienen las variables de un termino.

11. Unifica

Se intenta encontrar el unificador de dos formulas.

12. aux_unifica

Dados dos formulas, se buscan pares de terminos que pueden ser unificados, esto pasa cuando los predicados tienen el mismo nombre y tienen la misma longitud, de no ser posible se devuelve Nothing.

13. aux_unifica2

Se intenta aplicar la unificacion a cada par de terminos, de no ser posible, se devuelve Nothing.

14. Resolvente

Dados dos clausulas, se comprueba que tenga al menos 2 literales unificables, sean complementarias una de otra y que la interseccion del resto de variables sea vacia.

15. ClausulasSonUnificables

Por cada literal de las clausulas recibidas, se comprueba si al menos un par es unificable.

16. SonLiteralesUnificables

Dados dos Formulas (Literales) complementarias, se comprueba si son unificables o no.

17. dosFormulasSonUnificables

Auxiliar para la funcion de arriba, pues para comprobar si dos literales son unificables, se deben de pasar dos formulas no negadas.

18. ClausulasComplementarias

Dado dos clausulas se devuelve una lista de formulas complementarias.

19. DosFormulasSonComplementarias

Se comprueba si son complementarias, si las dos no están negadas, se devuelve falso, si se recibe una negada y el otro no, se comprueba si son alfaequivalentes.

20. InterseccionVacia

Dados dos formulas se comprueba si las variables no complementarias comparten o no variables.

21. ExtraerTodasLasVariablesClausula

Se extraen todas las variables de una clausula.

22. Resolucion

Dados dos clausulas, se les aplica resolucion binaria.

23. ClausulasComplementariasTuplas

Lo mismo que la funcion ClausulasComplementarias, pero en este caso se devuelven tuplas para conservar la informacion de que literal es complemento de quien.

24. TerminosComplementarios

Dado una lista de tuplas de formulas (se asume uno es el complemento del otro) , se devuelve una lista de tuplas de terminos complementarios.

25. ObtenerTerminosDeTupla

Se extraen los terminos de una tupla de formulas.

26. TerminosDePredicado

Se extraen los terminos de un predicado

27. AplicarExtraerTerminosOVariables

A cada par de terminos se le extraen terminos, pues en el caso de una funcion, es un termino, pero tambien tiene una lista de terminos asociado a él.

28. ExtraerTerminosDePredicado

Auxiliar para la funcion de arriba, esta funcion maneja los 4 casos en que se pueden recibir un par de terminos, el caso diferente es cuando se reciben dos Funciones, se extraen las variables de estas funciones, para hacer la sustitucion de estas variables.

29. SustituirBucle

Se aplican las sutituciones tantas veces como la longitud de la lista de tuplas de terminos a sustituir.

30. SustituirListaDeTerminosEnClausula

Dado una lista de terminos (sustituciones), se aplican las sustituciones a la clausula.

31. SustituirTerminoEnClausula

Se aplica una sustitucion a una clausula.

32. SustituirTerminoEnFormula

Se aplica una sustituccion a una formula.

33. SustituirTerminoEnPredicado

Se aplica una sustitucion a un predicado.
