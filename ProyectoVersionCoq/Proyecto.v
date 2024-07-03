Inductive bin : Type :=
  | Zero : bin
  | Doble : bin -> bin
  | Suc : bin -> bin.

Definition incrementa (b : bin) : bin :=
  match b with
  | Zero => Suc Zero
  | Doble n => Suc (Doble n)
  | Suc n => Suc (Suc n)
  end.

Fixpoint bin2nat (b:bin) : nat :=
  match b with
  | Zero => 0
  | Doble n => 2*(bin2nat n)
  | Suc n => S (bin2nat n)
  end.

Lemma suma_0_derecha : forall n: nat, n + 0 = n.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl.
    rewrite -> IHn.
    reflexivity.
Qed.

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


Theorem conmuta : forall ( b : bin ) ,bin2nat ( incrementa b) = ( bin2nat b) + 1.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - simpl.
    rewrite suma_0_derecha.
    rewrite suma_suc.
    reflexivity.
  - simpl.
    rewrite suma_suc.
    reflexivity.
Qed.

Fixpoint nat2bin (b : nat) : bin :=
  match b with
  | 0 => Zero
  | S n => incrementa (nat2bin n)
  end.

Theorem inversa : forall ( n : nat ) ,bin2nat ( nat2bin n ) = n.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl.
    rewrite conmuta.
    rewrite IHn.
    rewrite suma_suc.
    reflexivity.
Qed.

Theorem inversa2 : forall ( b : bin ) ,nat2bin ( bin2nat b ) = b .
Proof.
Abort.
(* El teorema es falso, un contraejemplo es cuando n= Doble Zero
entonces nat2bin(bin2nat (Doble Zero)) = Zero, lo cual es falso
 *)


Fixpoint doble (b : bin) : bin :=
  match b with
  | Zero => Zero
  | Doble n => Doble (doble n)
  | Suc n => Suc (Suc (doble n))
  end.

Theorem incrementa_incrementa_doble : forall (b : bin), incrementa (incrementa (doble b)) = doble (incrementa b).
Proof.
  intros b.
  destruct b; reflexivity.
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

Theorem n_mas_n : forall (n : nat), nat2bin (n + n) = doble (nat2bin n).
Proof.
    intros n.
    induction n.
    - simpl. reflexivity.
    - simpl.
      rewrite suma_n_Sm.
      simpl.
      rewrite IHn.
      rewrite incrementa_incrementa_doble.
      reflexivity.
Qed.

Theorem n_mas_n_mas_1 : forall (n : nat), nat2bin (n + n + 1) = incrementa (doble (nat2bin n)).
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl.
    rewrite suma_n_Sm with (n:=n) (m:= n).
    simpl.
    rewrite IHn.
    rewrite incrementa_incrementa_doble.
    reflexivity.
Qed.

Fixpoint normaliza (b : bin) : bin :=
  match b with
  | Zero => Zero
  | Suc n => Suc (normaliza n)
  | Doble n => match normaliza n with
               | Zero => Zero
               | n' => Doble n'
               end
  end.

Lemma n_mas_n_2n : forall a: nat, a + a = 2 * a.
Proof.
  induction a as [| a' IH].
  - reflexivity.
  - simpl. rewrite <- plus_n_Sm. rewrite suma_0_derecha. rewrite suma_n_Sm. reflexivity.
Qed.

Theorem doble_nat : forall b: nat, nat2bin(2*b) = doble (nat2bin b).
Proof.
intros b.
induction b.
  - simpl. reflexivity.
  - simpl. rewrite suma_0_derecha. rewrite suma_n_Sm. simpl. rewrite n_mas_n_2n.
    rewrite IHb. rewrite incrementa_incrementa_doble. reflexivity.
Qed.

Theorem normaliza_correcta : forall b : bin, nat2bin (bin2nat b) = normaliza b.
Proof.
  intros b.
  induction b.
  - reflexivity.
  - simpl.
    rewrite suma_0_derecha.
    rewrite n_mas_n_2n.
    rewrite doble_nat.
    rewrite IHb.
    destruct (normaliza b).
    * reflexivity.
    * rewrite <- IHb. rewrite <- doble_nat. rewrite <- n_mas_n_2n.
Abort.



















