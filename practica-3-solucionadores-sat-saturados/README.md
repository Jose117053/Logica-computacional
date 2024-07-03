Luna Rivera Carlos Alonso 318076814 Vázquez Dávila José Adolfo 423033366

Importante: El programa puede solucionar sudokus de cualquier dimension, se pide el tamaño del sudoku. Para solucionar un sudoku tradicional (9x9), a la hora de que se pida el tamaño del sudoku se debe ingresar el numero 3, si se ingresa un numero mayor a 3, digamos el 4, entonces se estára solucionando un sudoku de (16x16), el cual está subdividido en 16 cuadros 4x4 cada uno, con el 5 un sudoku 25x25, subdividido en 25 cuadros 5x5 cada 1, etc. (mi laptop de cartón crasheo con n=7)

A la hora de ingresar los numeros de la fila se deben ingresar nxn digitos. Si n=3, 9 numeros, si n=5, 25 numeros.

Modificaciones de la clase Main:
Ajustes en general para aceptar sudokus de nxn
Se agregan algunos metodos para correjir la "estetica" a la hora de imprimir sudokus :

-Espacios

Metodo que dependiendo la longitud del string recibido se imprimen espacios

-MargenIzquierdo

Dependiendo de la longitud del entero recibido se imprimen espacios

-MargenSuperior

Es la linea "divisora" superior, la longitud cambia en funcion del tamaño del sudoku

-auxPutStrl

Forma parte del margen de la parte izquierda, se imprime el numero de fila, seguido de uno o dos espacios dependiendo de la longitud del entero actual

Sea n=(tamaño*tamaño), con tamaño como el numero ingresado a la hora de pedir el tamaño del sudoku
Ejemplo: si se ingreso 3, entonces n=9.

Para la funcion principal SudokuFormula se deben cumplir los siguientes puntos:

1. cada_elemento_ocurre

Dados los datos ingresados, se asegura que estos aparezcan en la solucion.

2. un_numero_por_casilla 

Dado una casilla en la posicion i,j, se asegura que tenga exactamente un numero del 1 a n.

3. cada_casilla_es_unica

Se verifica que toda casilla del sudoku cumpla la funcion un_numero_por_casilla.

4.en_fila_no_se_repite_numero 

Dado una fila y un numero h, se verifica que este numero aparezca una sola vez en toda la fila

5. toda_fila_no_repite_numero

Se verifica que toda fila cumpla la funcion en_fila_no_se_repite_numero , los numeros a verificar son del 1 a n

6. en_columna_no_se_repite_numero y toda_columna_no_repite_numero

Analogo al caso de las filas, pero aplicado a las columnas

7. en_cuadrado_no_se_repite_numero y todo_cuadro_no_repite_numero

sea r=raiz cuadrada de n

Analogo al caso de filas y columnas, solo que en esta la manera de recorrer las casillas es un poco diferente, dado una fila i, se recorre hasta r posiciones adelante, lo mismo para la entrada j (columna); tanto i como j toman los valores 1+(0*r), 1+(0*r),1+(2*r),1+(3*r), los valores se detienen hasta que halla r-1 valores, pues ese es el intervalo de cada cuadro rxr.

Sudoku de entrada 4 (16x16)
Aunque funciona dandole todo el cuadro de jalón, se recomienda ingresar linea por linea, pues lo primero causa una excepcion despues de imprimir la solucion.

1234567890000000

0000000000000010

0000000001000000

0000000000000000

0000000000000000

2000004000000000

3000000000000000

4000000000000000

5000000000000000

6000000000000000

7000000000000000

0000000000000000

0000000000000000

0000000000000000

0000000000000000

0000000123456789

Sudoku con entrada 5 (25x25)

1234567890000000000000000

0000000000000000000000001

0000000000000000000000002

0000000000000000000000003

0000000000000000000000004

0000000000000000000000005

2000000000000000000000006

3000000000000000000000007

4000000000000000000000008

5000000000000000000000000

6000000000000000000000000

7000000000000000000000000

8000000000000000000000000

9000000000000000000000000

0000000000000000000000000

0000000000000000000000000

0000000000000000000000000

0000000000000000000000000

0000000000000000000000000

0000000000000000000000000

0000000000000000000000000

0000000000000000000000000

0000000000000000000000000

0000000000000000000000000

0000000000000000123456789


Puede que la ultima linea no se copie






