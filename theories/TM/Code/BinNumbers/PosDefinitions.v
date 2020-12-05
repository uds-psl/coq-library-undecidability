From Undecidability.TM Require Import ProgrammingTools.
From Undecidability.TM Require Import EncodeBinNumbers.
From Undecidability.TM Require Export ArithPrelim. (* [nia] etc. *)
From Coq Require Export BinPos.

(* Compute 42. (* default number notation is still for [nat] *) *)

Local Open Scope positive_scope.

(* Local Set Printing All. *)
(* Compute 42 % positive. *)
(* Compute 42 : positive. *)
(* Local Unset Printing All. *)


(* Big binary numbers are not a problem for Coq *)
(* Compute (42 ^ 42) % positive. *)

(* Number of bits required to represent this big number *)
(* Compute Pos.size_nat (42 ^ 42). *)


(* ** General definitions and lemmas on binary numbers *)

(* Append a lower-order bit *)
Definition append_bit (p : positive) (b : bool) := if b then p~1 else p~0.
Notation "p ~~ b" := (append_bit p b) (at level 7, left associativity, format "p '~~' b") : positive_scope.


Definition bitToSigPos (b : bool) : sigPos := if b then sigPos_xI else sigPos_xO.
Definition bitToSigPos' (b : bool) : sigPos^+ := inr (bitToSigPos b).

Lemma Encode_positive_app_xI (p : positive) :
  encode_pos (p ~ 0) = encode_pos p ++ [sigPos_xO].
Proof. cbn. congruence. Qed.

Lemma Encode_positive_app_xO (p : positive) :
  encode_pos (p ~ 1) = encode_pos p ++ [sigPos_xI].
Proof. cbn. congruence. Qed.

Lemma Encode_positive_app_xIO (p : positive) (b : bool) :
  encode_pos (p ~~ b) = encode_pos p ++ [if b then sigPos_xI else sigPos_xO].
Proof. destruct b. apply Encode_positive_app_xO. apply Encode_positive_app_xI. Qed.


(* Append (lower-order) bits to the binary number. The last bit in the list will be the LSB. *)
Fixpoint append_bits (x : positive) (bits : list bool) : positive :=
  match bits with
  | nil => x
  | b  :: bits' => append_bits (x~~b) bits'
  end.

(* Compute append_bits 42 [false; true]. (* 42 * 2 * 2 + 1 = 169 *) *)

Goal encode_pos (append_bits 1234567890 [false;true;true]) = encode_pos 1234567890 ++ map bitToSigPos [false;true;true]. Proof. reflexivity. Qed.

Lemma append_bits_bit (b : bool) (p : positive) (bits : list bool) :
  append_bits p (b :: bits) = append_bits (p~~b) bits.
Proof. reflexivity. Qed.

Lemma encode_append_bits (p : positive) (bits : list bool) :
  encode_pos (append_bits p bits) = encode_pos p ++ map bitToSigPos bits.
Proof.
  revert p. induction bits; intros; cbn in *; auto.
  - now simpl_list.
  - rewrite IHbits.
    rewrite Encode_positive_app_xIO.
    simpl_list; cbn.
    f_equal.
Qed.


(* [bits_to_pos] Computes the [positive] that is represented by the bitstring [true :: bits], where [true] is the HSB *)
Fixpoint bits_to_pos' (bits : list bool) : positive :=
  match bits with
  | nil => 1
  | b :: bits' => (bits_to_pos' bits') ~~ b
  end.
Definition bits_to_pos (bits : list bool) := bits_to_pos' (rev bits).

(* Compute bits_to_pos [false; true; false; true; false]. (* 42 *) *)
(* Compute bits_to_pos [false; true; false; true; true]. (* 43 -> last bit is LSB *) *)


Lemma bits_to_pos'_cons (bit : bool) (bits : list bool) :
  bits_to_pos' (bit :: bits) = (bits_to_pos' bits) ~~ bit.
Proof. reflexivity. Qed.

Lemma bits_to_pos_cons (bit : bool) (bits : list bool) :
  bits_to_pos (bits ++ [bit]) = (bits_to_pos bits) ~~ bit.
Proof. unfold bits_to_pos. simpl_list; cbn. apply bits_to_pos'_cons. Qed.


Lemma encode_bits_to_pos' (bits : list bool) :
  encode_pos (bits_to_pos' bits) = sigPos_xH :: map bitToSigPos (rev bits).
Proof.
  induction bits; cbn in *; f_equal; auto.
  rewrite Encode_positive_app_xIO.
  rewrite IHbits. cbn. f_equal. simpl_list. cbn. auto.
Qed.

Lemma encode_bits_to_pos (bits : list bool) :
  encode_pos (bits_to_pos bits) = sigPos_xH :: map bitToSigPos bits.
Proof. unfold bits_to_pos. rewrite encode_bits_to_pos'. now simpl_list. Qed.


Fixpoint pos_to_bits (p : positive) : list bool :=
  match p with
  | 1 => []
  | p ~ 1 => pos_to_bits p ++ [true]
  | p ~ 0 => pos_to_bits p ++ [false]
  end.

Lemma pos_to_bits_to_pos (p : positive) :
  bits_to_pos (pos_to_bits p) = p.
Proof.
  induction p; cbn; f_equal; eauto.
  - simpl_list; cbn. f_equal. eauto.
  - simpl_list; cbn. f_equal. auto.
Qed.

Lemma pos_to_bits_app_bit (b : bool) (p : positive) :
  pos_to_bits (p ~~ b) = pos_to_bits p ++ [b].
Proof. destruct b; reflexivity. Qed.

Lemma bits_to_pos_to_bits' (bits : list bool) :
  pos_to_bits (bits_to_pos' bits) = rev bits.
Proof.
  induction bits; intros; cbn in *.
  - auto.
  - simpl_list; cbn. rewrite pos_to_bits_app_bit. f_equal. auto.
Qed.

Lemma bits_to_pos_to_bits (bits : list bool) :
  pos_to_bits (bits_to_pos bits) = bits.
Proof. unfold bits_to_pos. rewrite bits_to_pos_to_bits'. now simpl_list. Qed.

Lemma pos_to_bits_append_bits : forall bits p, pos_to_bits (append_bits p bits) = pos_to_bits p ++ bits.
Proof.
  induction bits; intros; cbn in *.
  - now simpl_list.
  - destruct a; cbn; rewrite IHbits; cbn; simpl_list; cbn; auto.
Qed.

Lemma pos_to_bits_append_bits' : forall bits1 bits2, pos_to_bits (append_bits (bits_to_pos bits1) bits2) = bits1 ++ bits2.
Proof.
  intros.
  rewrite pos_to_bits_append_bits. now rewrite bits_to_pos_to_bits.
Qed.

Lemma Encode_positive_eq_pos_to_bits (p : positive) :
  encode_pos p = sigPos_xH :: map bitToSigPos (pos_to_bits p).
Proof.
  induction p; cbn; auto.
  - rewrite IHp; simpl_list; cbn; auto.
  - rewrite IHp; simpl_list; cbn; auto.
Qed.

Lemma pos_to_bits_inj : forall (p1 p2 : positive), pos_to_bits p1 = pos_to_bits p2 -> p1 = p2.
Proof.
  intros. apply Encode_positive_injective. cbn.
  rewrite !Encode_positive_eq_pos_to_bits. f_equal. f_equal. auto.
Qed.

(* We should have enough lemmas for [bits_to_pos] now. *)
Arguments bits_to_pos : simpl never.



Fixpoint pushHSB (p : positive) (b : bool) : positive :=
  match p with
  | p' ~ 1 => (pushHSB p' b) ~ 1
  | p' ~ 0 => (pushHSB p' b) ~ 0
  | 1 => 1 ~~ b
  end.

(* Compute pushHSB 42 true. (* 42 + 64 = 106 *) *)
(* Compute pushHSB 42 false. (* 42 + 64 - 32 = 74 *) *)

Lemma encode_pushHSB (p : positive) (b : bool) :
  encode_pos (pushHSB p b) = sigPos_xH :: bitToSigPos b :: tl (encode_pos p).
Proof.
  induction p; cbn.
  - rewrite IHp. simpl_list; cbn. now rewrite tl_app by apply Encode_positive_eq_nil.
  - rewrite IHp. simpl_list; cbn. now rewrite tl_app by apply Encode_positive_eq_nil.
  - rewrite Encode_positive_app_xIO. cbn. reflexivity.
Qed.


(* Alternative to [encode_pushHSB] *)
Lemma pos_to_bits_pushHSB (p : positive) (b : bool) :
  pos_to_bits (pushHSB p b) = b :: pos_to_bits p.
Proof.
  induction p; cbn.
  - rewrite IHp. simpl_list; cbn. auto.
  - rewrite IHp. simpl_list; cbn. auto.
  - destruct b; auto.
Qed.


(* Shifting bits left and right *)

Fixpoint shift_left (p : positive) (n : nat) :=
  match n with
  | O => p
  | S n' => shift_left (p~0) n'
  end.

Definition removeLSB (p : positive) : positive :=
  match p with
  | 1 => 1
  | p~0 => p
  | p~1 => p
  end.

Fixpoint shift_right (p : positive) (n : nat) :=
  match n with
  | O => p
  | S n' => shift_right (removeLSB p) n'
  end.

Lemma append_bit_removeLSB (p : positive) (b : bool) :
  removeLSB (p~~b) = p.
Proof. destruct b; reflexivity. Qed.

Lemma shift_left_append_zero (p : positive) (n : nat) :
  shift_left (p~0) n = (shift_left p n) ~ 0.
Proof. revert p. induction n; intros; cbn in *; auto. Qed.

Lemma shift_left_shift_right (p : positive) (n : nat) :
  shift_right (shift_left p n) n = p.
Proof.
  revert p. induction n; intros; cbn in *; auto.
  rewrite shift_left_append_zero. cbn. auto.
Qed.


(* Number of non-HSB bits *)
Fixpoint pos_size (p : positive) : nat :=
  match p with
  | 1 => 0
  | p~1 => S (pos_size p)
  | p~0 => S (pos_size p)
  end.

Lemma pos_size_append_bit (p : positive) (b : bool) :
  pos_size (p~~b) = S (pos_size p).
Proof. now destruct b. Qed.

Lemma pos_size_correct (p : positive) :
  S (pos_size p) = Pos.size_nat p.
Proof. induction p; cbn; auto. Qed.

Lemma pos_size_monotone (x y : positive) :
  x <= y ->
  (pos_size x <= pos_size y) % nat.
Proof.
  revert y. induction x; intros; cbn in *.
  - destruct y; cbn in *.
    + apply le_n_S. apply IHx. nia.
    + apply le_n_S. apply IHx. nia.
    + nia.
  - destruct y; cbn in *.
    + apply le_n_S. apply IHx. nia.
    + apply le_n_S. apply IHx. nia.
    + nia.
  - nia.
Qed.

(* Note that this doesn't hold for [<=] *)
Lemma pos_size_lt (p1 p2 : positive) :
  (pos_size p1 < pos_size p2) % nat ->
  p1 < p2.
Proof.
  revert p2. induction p1; intros; cbn in *; auto.
  - destruct p2; cbn in *.
    + specialize (IHp1 p2). spec_assert IHp1 by nia. nia.
    + specialize (IHp1 p2). spec_assert IHp1 by nia. nia.
    + nia.
  - destruct p2; cbn in *.
    + specialize (IHp1 p2). spec_assert IHp1 by nia. nia.
    + specialize (IHp1 p2). spec_assert IHp1 by nia. nia.
    + nia.
  - destruct p2; cbn in *; nia.
Qed.

