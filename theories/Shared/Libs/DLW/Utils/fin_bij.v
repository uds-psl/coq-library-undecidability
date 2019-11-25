(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import fin_base fin_choice.

From Undecidability.Shared.Libs.DLW.Vec
  Require Import pos vec.

Set Implicit Arguments.

Definition bij_t (X Y : Type) := { i : X -> Y & { j | (forall x, j (i x) = x) /\ forall y, i (j y) = y } }.

Definition surj_t (X Y : Type) := { s : X -> Y | forall y, exists x, y = s x }.

Fact surj_t_compose X Y Z : surj_t X Y -> surj_t Y Z -> surj_t X Z.
Proof. 
  intros (f & Hf) (g & Hg); exists (fun x => g (f x)).
  intros z.
  destruct (Hg z) as (y & Hy).
  destruct (Hf y) as (x & Hx).
  exists x; subst; auto.
Qed.

Fact finite_t_surj_t X Y : surj_t X Y -> finite_t X -> finite_t Y.
Proof.
  intros [ s E ] (l & Hl).
  exists (map s l).
  intros y; rewrite in_map_iff. 
  destruct (E y) as (x & ?); exists x; auto. 
Qed.

Fact finite_t_pos_equiv X : (finite_t X -> { n : _ & surj_t (pos n) X })
                          * ({ n : _ & surj_t (pos n) X } -> finite_t X).
Proof.
  split.
  + intros (l & Hl).
    exists (length l).
    destruct (list_vec_full l) as (v & Hv).
    rewrite <- Hv in Hl.
    generalize (length l) v Hl.
    clear l v Hl Hv.
    intros n v H.
    exists (vec_pos v).
    intros x; apply (vec_list_inv _ _ (H x)).
  + intros (n & Hn).
    generalize (finite_t_pos n).
    apply finite_t_surj_t; auto.
Qed.

Fact NoDup_vec_list X n v : NoDup (@vec_list X n v) -> forall p q, vec_pos v p = vec_pos v q -> p = q.
Proof.
  induction v as [ | n x v IHv ]; intros H p q.
  + invert pos p.
  + simpl in H; rewrite NoDup_cons_iff in H.
    destruct H as [ H1 H2 ].
    invert pos p; invert pos q; intros E; auto.
    1,2: destruct H1; subst; apply in_vec_list, in_vec_pos.
    f_equal; apply IHv; auto.
Qed.

Fact finite_t_discrete_bij_t_pos X : 
        finite_t X
     -> (forall x y : X, { x = y } + { x <> y })
     -> { n : nat & bij_t X (pos n) }.
Proof. 
  intros (l' & Hl') D.
  generalize (NoDup_nodup D l') (nodup_In D l').
  set (l := nodup D l'); intros H1 H2.
  assert (Hl : forall x, In x l) by (intro; apply H2, Hl').
  revert H1 Hl.
  generalize l; clear l l' Hl' H2.
  intros l Hl1 Hl2.
  exists (length l).
  destruct (list_vec_full l) as (v & Hv).
  rewrite <- Hv in Hl1, Hl2.
  assert (forall x, in_vec x v) by (intro; apply in_vec_list; auto).
  generalize (NoDup_vec_list _ Hl1).
  clear Hl1 Hv.
  revert v H Hl2.
  generalize (length l); clear l.
  intros n v H1 H2 H3.
  destruct constructive_choice with (R := fun x p => vec_pos v p = x) 
    as (f & Hf).
  + intro; apply in_vec_dec_inv; auto.
  + exists f, (vec_pos v); split; auto.
Qed.
