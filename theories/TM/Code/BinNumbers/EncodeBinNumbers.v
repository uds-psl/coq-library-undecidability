(** * Encoding for binary numbers *)

From Undecidability Require Import TM.Prelim Code.
From Undecidability Require Import ArithPrelim.
From PslBase Require Export Bijection.
Require Export BinNums. (* Warning: There also is a constructor called [N] for the type [move] *)


(* We use Coq's standard types [positive] and [N] *)

(* It is important to note that the least-significant bit is the last symbol in the encoding *)

Inductive sigPos : Type :=
| sigPos_xI : sigPos
| sigPos_xO : sigPos
| sigPos_xH : sigPos.

Global Instance sigPos_eq : eq_dec sigPos.
Proof. unfold dec. decide equality. Defined.

Global Instance sigPos_fin : finTypeC (EqType sigPos).
Proof. split with (enum := [sigPos_xI; sigPos_xO; sigPos_xH]). intros [ | | ]; cbn; reflexivity. Qed.

Fixpoint encode_pos (x : positive) : list sigPos :=
  match x with
  | xI x' => encode_pos x' ++ [sigPos_xI]
  | xO x' => encode_pos x' ++ [sigPos_xO]
  | xH => [sigPos_xH]
  end.

Global Instance Encode_positive : codable sigPos positive :=
  {|
    encode := encode_pos;
  |}.

Lemma Encode_positive_hasSize x : size _ x = Pos.size_nat x.
Proof. induction x; cbn; auto; simpl_list; setoid_rewrite IHx; cbn; auto; omega. Qed.

Corollary Encode_positive_eq_nil x :
  Encode_positive x <> nil.
Proof. intros H % length_zero_iff_nil. setoid_rewrite Encode_positive_hasSize in H. destruct x; cbn in *; omega. Qed.

Lemma app_singleton_inv (X : Type) (xs ys : list X) (x y : X) :
  xs ++ [x] = ys ++ [y] -> xs = ys /\ x = y.
Proof.
  revert ys. induction xs as [ | x' xs' IH]; intros; cbn in *.
  - destruct ys as [ | y']; cbn in *; inv H; auto.
    exfalso. now apply app_cons_not_nil in H2.
  - destruct ys as [ | y']; cbn in *; inv H; auto.
    + exfalso. symmetry in H2. now apply app_cons_not_nil in H2.
    + now apply IH in H2 as (->&->).
Qed.

Lemma app_singleton_inv_nil (X : Type) (xs : list X) (x y : X) :
  xs ++ [x] = [y] -> xs = nil /\ x = y.
Proof.
  destruct xs as [ | x' xs']; cbn in *; intros H; inv H; auto.
  exfalso. symmetry in H2. now apply app_cons_not_nil in H2.
Qed.


Lemma Encode_positive_injective : injective encode_pos.
Proof.
  cbn. hnf. intros n1. induction n1; intros n2 H; cbn in *.
  - destruct n2; cbn in *; try congruence.
    + apply app_singleton_inv in H as (H1&H1'); inv H1'; auto using f_equal.
    + apply app_singleton_inv in H as (H1&H1'); inv H1'; auto using f_equal.
    + exfalso. apply app_singleton_inv_nil in H as (H&H'); inv H'.
  - destruct n2; cbn in *; try congruence.
    + apply app_singleton_inv in H as (H1&H1'); inv H1'; auto using f_equal.
    + apply app_singleton_inv in H as (H1&H1'); inv H1'; auto using f_equal.
    + exfalso. apply app_singleton_inv_nil in H as (H&H'); inv H'.
  - destruct n2; cbn in *; try congruence.
    + symmetry in H. apply app_singleton_inv_nil in H as (H1&H1'); inv H1'; auto using f_equal.
    + symmetry in H. apply app_singleton_inv_nil in H as (H1&H1'); inv H1'; auto using f_equal.
Qed.

Lemma Encode_positive_startsWith_xH (x : positive) :
  exists str', encode_pos x = sigPos_xH :: str'.
Proof.
  induction x; cbn; eauto.
  - destruct IHx. eexists (_ ++ _); cbn. setoid_rewrite H; cbn; eauto.
  - destruct IHx. eexists (_ ++ _); cbn. setoid_rewrite H; cbn; eauto.
Qed.

Compute encode (42 % positive).

(* With this alphabet it is easier to derive the machines for [N] using the machines for [positive] *)
Notation sigN := (sigOption sigPos).

Definition N_to_optionPos : BinNums.N -> option positive :=
  fun n => match n with
        | N0 => None
        | Npos p => Some p
        end.

Instance Encode_N : codable sigN BinNums.N :=
  {|
    encode n := encode (N_to_optionPos n);
  |}.

Definition Encode_N_size (n : N) : nat :=
  match n with
  | N0 => 1
  | Npos p => S (Pos.size_nat p)
  end.

Lemma Encode_N_hasSize (n : N) :
  size _ n = Encode_N_size n.
Proof. destruct n; cbn; auto. simpl_list. f_equal. apply Encode_positive_hasSize. Qed.


Check _ : Retract sigPos sigN. (* The obvious retract *)

Compute encode (42 % N).
