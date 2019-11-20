(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_list finite.

Set Implicit Arguments.

Inductive fol_bop := fol_conj | fol_disj | fol_imp.
Inductive fol_qop := fol_ex | fol_fa.

Definition fol_bin_sem b :=
  match b with
    | fol_conj => and
    | fol_disj => or
    | fol_imp  => fun A B => A -> B
  end.

Fact fol_bin_sem_ext b A A' B B' :
     (A <-> A') -> (B <-> B') -> (fol_bin_sem b A B <-> fol_bin_sem b A' B').
Proof.
  intros E1 E2; destruct b; simpl; tauto.
Qed. 

Fact fol_equiv_ext (P Q : Prop) : P = Q -> P <-> Q.
Proof. intros []; tauto. Qed.

Arguments fol_bin_sem b /.

Fact fol_bin_sem_dec b A B : 
       { A } + { ~ A } -> { B } + { ~ B } 
    -> { fol_bin_sem b A B } + { ~ fol_bin_sem b A B }.
Proof. revert b; intros [] HA HB; simpl; tauto. Qed.

Fact fol_equiv_dec A B : 
       { A } + { ~ A } -> { B } + { ~ B } 
    -> { A <-> B } + { ~ (A <-> B) }.
Proof. tauto. Qed.

Definition fol_quant_sem X q (P : X -> Prop) :=
  match q with
    | fol_ex => ex P
    | fol_fa => forall x, P x 
  end.

Arguments fol_quant_sem X q P /.

Fact fol_quant_sem_ext X q (P Q : X -> Prop) : 
        (forall x, P x <-> Q x) 
      -> fol_quant_sem q P <-> fol_quant_sem q Q.
Proof.
  revert q; intros [] H; simpl.
  + split; intros (k & ?); exists k; apply H; auto.
  + split; intros ? k; apply H; auto. 
Qed.

Notation forall_equiv := (@fol_quant_sem_ext _ fol_fa).
Notation exists_equiv := (@fol_quant_sem_ext _ fol_ex).

Fact forall_list_sem_dec X (P : X -> Prop) (l : list X) :  
       (forall x, { P x } + { ~ P x }) 
    -> { forall x, In x l -> P x } + { ~ forall x, In x l -> P x }.
Proof.
  intros H. 
  destruct list_dec with (P := fun x => ~ P x) (Q := P) (l := l)
      as [ (x & H1 & H2) | H1 ].
  + firstorder.
  + right; contradict H2; auto.
  + left; intros x; apply H1; auto.
Qed.

Fact exists_list_sem_dec X (P : X -> Prop) (l : list X) :  
       (forall x, { P x } + { ~ P x }) 
    -> { exists x, In x l /\ P x } + { ~ exists x, In x l /\ P x }.
Proof.
  intros H. 
  destruct list_dec with (P := P) (Q := fun x => ~ P x) (l := l)
      as [ (x & H1 & H2) | H1 ]; auto.
  + left; firstorder.
  + right; intros (y & Hy).
    apply (H1 y); tauto.
Qed.

Fact fol_quant_sem_dec X q (P : X -> Prop) : 
       finite_t X 
    -> (forall x, { P x } + { ~ P x }) 
    -> { fol_quant_sem q P } + { ~ fol_quant_sem q P }.
Proof.
  intros (lX & HlX). 
  revert q; intros [] H; simpl.
  + destruct exists_list_sem_dec with (l := lX) (1 := H); firstorder.
  + destruct forall_list_sem_dec with (l := lX) (1 := H); firstorder.
Qed.


