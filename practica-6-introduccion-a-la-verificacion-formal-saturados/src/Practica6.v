Require Import Nat.
Require Import List.

(* Ejercicio 1 *)

Lemma imp_conj : 
  forall P Q R : Prop, (P -> Q -> R) <-> (P /\ Q -> R).
Proof.
  intros P Q R. 
  split.
  - intros H [HP HQ].
    apply H.
    assumption.
    assumption.
  - intros H P' Q'.
    apply H.         (*apply H; assumption. Se aplica assumption ( lo que se quiere probar ya está en el contexto) a las metas
                     producidas de hacer apply H*) 
    split; assumption.
Qed.

(* Ejercicio 2 *)

Lemma imp_trans : 
  forall P Q R : Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R.
  intros S T P'.
  apply T.
  apply S.
  assumption.
Qed.

(* Ejercicio 3 *)

Lemma or_and_not : 
  forall P Q : Prop, (P \/ Q) /\ ~P -> Q.
Proof.
  intros P Q.
  intros [ [soloP | soloQ] noP]. (* es como un destruct para la disyuncion *)
  - contradiction.
  - assumption.
Qed.

(* Ejercicio 4 *)

Lemma deMorgan : 
  forall P Q : Prop, ~(P \/ Q) <-> (~P /\ ~Q).
Proof.
  intros P Q.
  split.
  - intros noDisyPQ.
    split.
    + intro HP.
      apply noDisyPQ.
      left.
      assumption.
    + intro HQ.
      apply noDisyPQ.
      right.
      assumption.
  - intros [noP noQ] [siP | siQ].
    + contradiction.
    + contradiction.
Qed.

(* Ejercicio 5 *)

Lemma suma_suc :
  forall n : nat, n + 1 = S n.
Proof.
  intros n.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

(* Ejercicio 6 *)

Lemma neutro :
  forall n : nat, n + 0 = n.
Proof.
  intros n.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma suma_n_Sm:
  forall n m : nat, n + S m = S (n + m).
Proof.
  intros n m.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.


Lemma suma_conm :
  forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n.
  - simpl.
    rewrite neutro.
    reflexivity.
  - simpl.
    rewrite IHn.
    rewrite suma_n_Sm.
    reflexivity.
Qed.

(* Ejercicio 7 *)

Lemma mult_0_derecha :
  forall n : nat, n * 0 = 0.
Proof.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma suma_0_derecha : forall n: nat, n + 0 = n.

Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl.
    rewrite -> IHn.
    reflexivity.
Qed.

Lemma suma_asociativa : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma mult_n_Sm : forall n m : nat, n * (S m) = n * m + n.
Proof.
  intros n m.
  induction n.
  - simpl. reflexivity.
  - simpl.
    rewrite IHn.
    rewrite suma_n_Sm.
    rewrite suma_asociativa.
    reflexivity.
Qed.

Lemma mult_dist :
  forall n m p : nat, p * (n + m) = p * n + p * m.
Proof.
  intros n m p.
  induction m.
  - rewrite suma_0_derecha.
    rewrite mult_0_derecha.
    rewrite suma_0_derecha. reflexivity.
  - rewrite suma_n_Sm.
    rewrite mult_n_Sm.
    rewrite IHm.
    rewrite mult_n_Sm.
    rewrite suma_asociativa.
    reflexivity.
Qed.

(* Ejercicio 8 *)

Fixpoint gauss (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => S k + gauss k
  end.

(* Ejercicio 9 *)

Lemma mult_1_derecha : forall n: nat, n * 1 = n.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.


Lemma gauss_Sn: forall n : nat, gauss (S n) = gauss n + (n+1).
Proof.
  intros n.
  simpl.
  rewrite suma_conm.
  rewrite suma_suc.
  rewrite <- suma_n_Sm.
  reflexivity.
Qed.

Lemma mult_conm : forall n m: nat, n*m = m*n.
Proof.
  intros n m.
  induction n.
  - simpl.
    rewrite -> mult_0_derecha.
    reflexivity.
  - simpl.
    rewrite IHn.
    rewrite <- suma_suc.
    rewrite -> mult_dist.
    rewrite -> mult_1_derecha.
    rewrite suma_conm.
    reflexivity.
Qed.

Lemma uno_mas_uno: forall n : nat, n + 1 + 1 = n + 2.
Proof.
  intros n.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHn.
    reflexivity.
Qed.

Lemma gauss_eq :
  forall n : nat, 2 * gauss n = n * (n + 1).
Proof.
  intros n.
  induction n.
  - reflexivity.
  - rewrite -> gauss_Sn.
    rewrite -> mult_dist.
    rewrite -> IHn.
    rewrite  mult_conm with (n:=2) (m:=n+1).
    rewrite mult_conm.
    rewrite <- mult_dist.
    rewrite <- suma_suc with (n:=n).
    rewrite uno_mas_uno.
    reflexivity.
Qed.

(* Ejercicio 10 *)

Lemma concat_assoc :
  forall (A : Type) (xs ys zs : list A), xs ++ ys ++ zs = (xs ++ ys) ++ zs.
Proof.
  intros A xs ys zs.
  induction xs.
  - reflexivity.
  - simpl.
    rewrite IHxs.
    reflexivity.
Qed.


(* Ejercicio 11 *)

Fixpoint reversa {A : Type} (l : list A) :=
  match l with
  | nil => nil
  | cons x xs => reversa xs ++ (x :: nil)
  end.

Theorem concat_nil_derecha : forall (A : Type) (l : list A), l ++ nil = l.
Proof.
  intros A l.
  induction l.
  - reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Qed.

Lemma rev_concat :
  forall (A : Type) (xs ys : list A), reversa (xs ++ ys) = reversa ys ++ reversa xs.
Proof.
  intros A xs ys.
  induction xs.
  - simpl.
    rewrite concat_nil_derecha.
    reflexivity.
  - simpl.
    rewrite IHxs.
    rewrite concat_assoc.
        reflexivity.
Qed.

Import ListNotations. (* para que detecte "L" *)

(* Ejercicio 12 *)
Fixpoint take {A : Type} (n : nat) (L : list A) : list A := 
  match n, L with
  | 0, _ => []
  | _, [] => nil
  | S m, x :: xs => x :: take m xs
  end.

(* Ejercicio 13 *)

Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
match n, l with
  | 0, _ => l
  | _, [] => []
  | S m, x :: xs => drop m xs
  end.

(* Ejercicio 14 *)

Lemma tdn:
  forall (A : Type) (n : nat) (xs : list A), xs = take n xs ++ drop n xs.
Proof.
  intros A n.
  induction n.
  - intros xs.
    reflexivity.
  - intros xs.
    destruct xs.
    + simpl.
      reflexivity.
    + simpl.
      rewrite <- IHn.
      reflexivity.
Qed.

(* Ejercicio 15 *)

Lemma take_nil : forall (A : Type) (n : nat), take n (@nil A) = @nil A.
Proof.
  intros A n.
  induction n.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma drop_nil : forall (A : Type) (n : nat), drop n (@nil A) = @nil A.
Proof.
  intros A n.
  induction n.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma drop_Sn : forall (A : Type) (n : nat) (x : A) (xs : list A), drop (S n) (x :: xs) = drop n xs.
Proof.
  intros A n x xs.
  simpl.
  reflexivity.
Qed.

Lemma take_Sn : forall (A : Type) (n : nat) (x : A) (xs : list A), take (S n) (x :: xs) = x :: take n xs.
Proof.
  intros A n x xs.
  simpl.
  reflexivity.
Qed.

Lemma ts:
  forall (A : Type) (xs : list A) (n m : nat), 
    take m (drop n xs) = drop n (take (m + n) xs).
Proof.
  intros A xs.
  induction xs. (* hacia intros n m desde aqui y no queria funcionar :( *)
  - intros n m.
    rewrite drop_nil.
    rewrite take_nil.
    rewrite take_nil.
    rewrite drop_nil.
    reflexivity.
  - intros n m.
    destruct n.
    + simpl.
      rewrite suma_0_derecha.
      reflexivity.
    + rewrite drop_Sn.
      rewrite suma_n_Sm.
      rewrite take_Sn.
      rewrite drop_Sn.
      rewrite IHxs.
      reflexivity.
Qed.

(* Ejercicio 16 *)
Lemma min_n_0 : forall n : nat, min n 0 = 0.
Proof.
  intros n.
  destruct n.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma min:
  forall (A : Type) (xs : list A) (n m : nat),
    take m (take n xs) = take (min m n) xs.
Proof.
  intros A xs.
  induction xs.
  - intros n m. 
    rewrite take_nil.
    rewrite take_nil.
    rewrite take_nil.
    reflexivity.
  - intros n m.
    destruct n.
    + rewrite min_n_0.
      simpl.
      rewrite take_nil. 
      reflexivity.
    + destruct m.
      * reflexivity.
      * rewrite take_Sn.
        simpl.
        rewrite IHxs.
        reflexivity.
Qed.





















