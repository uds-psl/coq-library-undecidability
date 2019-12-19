(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Bool Eqdep_dec.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_list finite.

Set Implicit Arguments.

Fact eq_bool_pirr (b1 b2 : bool) (H1 H2 : b1 = b2) : H1 = H2.
Proof. apply UIP_dec, bool_dec. Qed.

Fact eq_nat_uniq (n : nat) (H : n = n ) : H = eq_refl.
Proof. apply UIP_dec, eq_nat_dec. Qed.

Fact eq_nat_pirr (x y : nat) (H1 H2 : x = y) : H1 = H2.
Proof. apply UIP_dec, eq_nat_dec. Qed.

Definition cast (P : nat -> Type) n k (v : P n) (H : n = k) : P k := eq_rect _ P v _ H.

Arguments cast {P n k} v H.

Lemma cast_refl P n (v : P n) : cast v eq_refl = v.
Proof. reflexivity. Qed.

Lemma cast_fun P Q (f : forall n, P n -> Q n) n k (v : P n) (H : n = k) : 
        f _ (cast v H) = cast (f _ v) H.
Proof. subst; auto. Qed.

Tactic Notation "solve" "ite" :=
  match goal with _ : ?x < ?y |- context[if le_lt_dec ?y ?x then _ else _]
        => let G := fresh in destruct (le_lt_dec y x) as [ G | _ ]; [ exfalso; lia | ]
  end.

Section graphs.

  Variable (X Y : Type) (R : X -> Y -> Prop).

  Definition graph_tot := forall x, ex (R x).
  Definition graph_fun := forall x y1 y2, R x y1 -> R x y2 -> y1 = y2.

  Definition is_graph_function := graph_fun /\ graph_tot.

  Hypothesis (H1 : finite_t Y)
             (H3 : forall x y, { R x y } + { ~ R x y }).

  Definition graph_tot_reif : is_graph_function -> { f | forall x y, R x y <-> y = f x }.
  Proof.
    intros (H2 & H4). 
    destruct finite_t_dec_choice with (3 := H4) as (f & Hf); auto.
    exists f; intros x y; split.
    + intros H; generalize H (Hf x); apply H2.
    + intros ->; auto.
  Qed.

End graphs.

Section graphs_equiv.

  Variable (X Y : Type) (R : X -> Y -> Prop) (equiv : Y -> Y -> Prop).
  
  Infix "≈" := equiv (at level 70, no associativity).

  Definition graph_equiv_tot := forall x, ex (R x).
  Definition graph_equiv_fun := forall x y1 y2, R x y1 -> R x y2 -> y1 ≈ y2.

  Definition is_graph_equiv_function := graph_equiv_fun /\ graph_equiv_tot.

  Hypothesis (H1 : finite_t Y)
             (H3 : forall x y, { R x y } + { ~ R x y })
             (H6 : forall x y1 y2, y1 ≈ y2 -> R x y2 -> R x y1).

  Definition graph_equiv_function_reif : is_graph_equiv_function -> { f | forall x y, R x y <-> y ≈ f x }.
  Proof.
    intros (H2 & H4). 
    destruct finite_t_dec_choice with (3 := H4) as (f & Hf); auto.
    exists f; intros x y; split.
    + intros H; generalize H (Hf x); apply H2.
    + intros H; generalize (Hf x); apply H6; auto.
  Qed.

End graphs_equiv.

