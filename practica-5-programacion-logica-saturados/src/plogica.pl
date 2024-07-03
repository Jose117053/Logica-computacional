%% Ejercicio 1: Buen Fin

articulo(pantalon).
articulo(chamarra).
articulo(sombrilla).

color(azul).
color(rojo).
color(amarillo).

descuento(10).
descuento(25).
descuento(50).

distintos(X,Y,Z) :- X \= Y, X \= Z, Y \= Z.

chamarra_azul(Articulo, _) :- Articulo \= chamarra.
chamarra_azul(chamarra, azul).

rojo_descuento(C, _, _, _) :- C \= rojo.
rojo_descuento(_, _, A, _) :- A \= sombrilla.
rojo_descuento(rojo, D1, sombrilla, D2) :- D1 > D2.

pantalon_descuento(Articulo,_) :- Articulo \= pantalon.
pantalon_descuento(pantalon, Descuento) :- Descuento \= 10.

tuplas(T1,T2,T3) :-
    T1 = t(curry, Articulo1, Color1, Descuento1),
    T2 = t(kleene, Articulo2, Color2, Descuento2),
    T3 = t(russell, Articulo3, Color3, Descuento3),
    articulo(Articulo1),
    articulo(Articulo2),
    articulo(Articulo3),
    color(Color1),
    color(Color2),
    color(Color3),
    descuento(Descuento1),
    descuento(Descuento2),
    descuento(Descuento3),
    distintos(Articulo1, Articulo2, Articulo3),
    distintos(Color1,Color2,Color3),
    distintos(Descuento1,Descuento2,Descuento3),
    chamarra_azul(Articulo1,Color1),
    chamarra_azul(Articulo2,Color2),
    chamarra_azul(Articulo3,Color3),
    Articulo1 \= chamarra,
    Descuento3 = 25,
    rojo_descuento(Color1, Descuento1, Articulo1, Descuento1),
    rojo_descuento(Color1, Descuento1, Articulo2, Descuento2),
    rojo_descuento(Color1, Descuento1, Articulo3, Descuento3),
    rojo_descuento(Color2, Descuento2, Articulo1, Descuento1),
    rojo_descuento(Color2, Descuento2, Articulo2, Descuento2),
    rojo_descuento(Color2, Descuento2, Articulo3, Descuento3),
    rojo_descuento(Color3, Descuento3, Articulo1, Descuento1),
    rojo_descuento(Color3, Descuento3, Articulo2, Descuento2),
    rojo_descuento(Color3, Descuento3, Articulo3, Descuento3),
    pantalon_descuento(Articulo1,Descuento1),
    pantalon_descuento(Articulo2,Descuento2),
    pantalon_descuento(Articulo3,Descuento3),
    Articulo1 \= pantalon,
    Articulo2 \= pantalon,
    !.

%% Ejercicio 2:

particion(L1, L2, L3) :-
    length(L1, Longitud),  
    Mitad is Longitud // 2, 
    length(L2, Mitad),  
    append(L2, L3, L1). %% en el caso en que se le da una lista definida calcula todos los casos en que l1 concatenado con l2 restulta en L
                        %% pero como l1 tiene la mitad de la longitud solo hay un caso.

%% Ejercicio 3:

combina([], L, L). 
combina(L, [], L).  

combina([X|XS], [Y|YS], [X|Cola]) :-
    X =< Y, 
    combina(XS, [Y|YS], Cola).  

combina([X|XS], [Y|YS], [Y|Cola]) :-
    X > Y, 
    combina([X|XS], YS, Cola). 


%% Ejercicio 4:

gcd(0,0,0). %%no deberia ser 0, pero para que no truene
gcd(X, Y, Z) :-
AbsX is abs(X), 
AbsY is abs(Y), 
gcd_abs(AbsX, AbsY, Z). 

gcd_abs(0, Y, Y) :- Y > 0, !.
gcd_abs(X, 0, X) :- X > 0, !.
gcd_abs(X, Y, Z) :-
Resto is X mod Y,
gcd_abs(Y, Resto, Z).


coprimos(X, Y) :- gcd(X, Y, Z),
                  Z =:= 1.  


%% Ejercicio 5:

agrupa([], []).
agrupa([X], [[X]]).

agrupa([X, X | Cola], [[X | Grupo] | ColaAgrupado]) :-
    agrupa([X | Cola],
    [Grupo | ColaAgrupado]),
    !.

agrupa([X, Y | Cola], [[X] | ColaAgrupado]) :-
    X \= Y,
    agrupa([Y | Cola], ColaAgrupado),
    !.

%% Ejercicio 6:

pertenece(X, [X | _]).
pertenece(X, [_ | XS]) :- pertenece(X, XS), !. 


%% Ejercicio 7:


elimina(_, [], []). 
elimina(E, [E|XS], XS). 
elimina(E, [X|XS], [X|YS]) :- 
    E \= X,
    elimina(E, XS, YS), !.


%% Ejercicio 8:

%% camino().

conectado(d,c).
conectado(d,e).
conectado(c,b).
conectado(f,e).
conectado(e,g).
conectado(e,b).
conectado(b,a).

camino(X, Y, [X|XS]) :-
    camino(X, Y, [X], XS).

camino(X, X, _, []). 

camino(X, Y, Visitados, [Z|XS]) :-
    (conectado(X, Z); conectado(Z, X)),  
    \+ member(Z, Visitados),           
    camino(Z, Y, [Z|Visitados], XS). 
