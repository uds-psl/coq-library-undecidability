(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith.

From Undecidability.Shared.Libs.DLW 
  Require Import utils_tac utils_nat utils_decidable pos vec.

From Undecidability.MuRec
  Require Import recalg ra_utils.

Set Implicit Arguments.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

Section ra_min_extra.

  Variable (n : nat) (f : recalg (S n)) (v : vec nat n).

  Hypothesis Hf : forall x, ex (⟦f⟧ (x##v)).

  Theorem ra_min_extra : ex (⟦ra_min f⟧ v) <-> exists x, ⟦f⟧ (x##v) 0.
  Proof using Hf.
    split.
    + intros (x & H1 & H2); exists x; auto.
    + intros (x & Hx).
      destruct bounded_min_d with (P := fun x => ⟦f⟧ (x##v) 0)
                                  (Q := fun x => exists k, ⟦f⟧ (x##v) (S k))
                                  (n := S x)
        as [ (m & H1 & H2 & H3) | H1 ]; auto.
      * intros y _; destruct (Hf y) as ([ | k ] & Hk); auto.
        right; exists k; auto.
      * exists m; split; auto.
      * destruct (H1 _ (le_refl _)) as (k & Hk).
        generalize (ra_rel_fun _ _ _ _ Hx Hk); discriminate.
  Qed.

End ra_min_extra.

Section ra_min_extra'.

  Variable (n : nat) (f : recalg (S n)) (v : vec nat n).

  Hypothesis Hf : forall x, ⟦f⟧ (x##v) 0 \/ ⟦f⟧ (x##v) 1.

  Theorem ra_min_ex : ex (⟦ra_min f⟧ v) <-> exists x, ⟦f⟧ (x##v) 0.
  Proof using Hf.
    apply ra_min_extra.
    intros x; destruct (Hf x); firstorder.
  Qed.

End ra_min_extra'.

Section ra_enum.

  Variables (k : nat) (f : recalg (S k)).

  Let a : recalg (S (S k)).
  Proof.
    ra root f.
    + ra arg pos0.
    + apply vec_set_pos; intros p.
      ra arg (pos_nxt (pos_nxt p)).
  Defined.

  Let Ha v x : ⟦a⟧ v x <-> ⟦f⟧ (vec_pos v pos0##vec_tail (vec_tail v)) x.
  Proof.
    unfold a.
    rewrite ra_rel_fix_comp; simpl.
    split.
    + intros (w & H1 & H2); revert H1 H2.
      vec split w with y; intros H1 H2.
      generalize (H2 pos0); simpl; intros H3; subst.
      eq goal H1; do 2 f_equal.
      apply vec_pos_ext; intros p.
      specialize (H2 (pos_nxt p)); simpl in H2.
      rewrite vec_pos_map, vec_pos_set in H2; simpl in H2.
      rewrite <- H2; repeat rewrite vec_pos_tail; auto.      
    + vec split v with p; vec split v with q; simpl; intros H. 
      exists (p##v); split; auto.
      intros y; analyse pos y; simpl; auto.
      rewrite vec_pos_map, vec_pos_set; simpl; auto.
  Qed.
  
  Let b : recalg (S (S k)).
  Proof.
    ra root ra_succ.
    ra arg pos1.
  Defined.

  Let Hb v x : ⟦b⟧ v x <-> x = S (vec_pos v pos1).
  Proof.
    unfold b; simpl; split.
    + intros (w & H1 & H2); revert H1 H2.
      vec split w with y; vec nil w; intros H1 H2.
      specialize (H2 pos0); simpl in H2; subst; auto.
    + intros H; exists (vec_pos v pos1##vec_nil); subst; split; simpl; auto.
      pos split; simpl; auto.
  Qed.

  Opaque a b.

  Let g : recalg (S (S k)).
  Proof.
    ra root ra_eq.
    + exact a.
    + exact b.
  Defined.

  Hypothesis Hf : forall v, exists x, ⟦f⟧ v x.

  Let Hg v : exists e, ⟦g⟧ v e /\ (e = 0 <-> ⟦f⟧ (vec_pos v pos0##vec_tail (vec_tail v)) (S (vec_pos v pos1))).
  Proof.
    unfold g.
    destruct (Hf (vec_pos v pos0##vec_tail (vec_tail v))) as (x & Hx).
    destruct (ra_eq_rel (x##S (vec_pos v pos1)##vec_nil)) as (e & H1 & H2).
    exists e; split.
    + exists (x##S (vec_pos v pos1)##vec_nil); split; auto.
      intros p; analyse pos p; simpl.
      * apply Ha; auto.
      * apply Hb; auto.
    + simpl in H2; rewrite H2; split.
      * intros; subst; auto.
      * revert Hx; apply ra_rel_fun.
  Qed.

  Opaque g.

  Definition ra_enum : recalg (S k).
  Proof using a. apply ra_min, g. Defined.

  (* A reduction of listability into recursive computability *)

  Fact ra_enum_spec x v : ex (⟦ra_enum⟧ (x##v)) <-> exists n, ⟦f⟧ (n##v) (S x).
  Proof using Hf.
    unfold ra_enum; simpl; unfold s_min.
    rewrite μ_min_of_total.
    + split.
      * intros (r & Hr).
        destruct (Hg (r##x##v)) as (e & H1 & H2).
        simpl in H2.
        exists r; apply H2.
        revert H1 Hr; apply ra_rel_fun.
      * intros (n & Hn); exists n.
        destruct (Hg (n##x##v)) as (e & H1 & H2).
        apply H2 in Hn; subst; auto.
    + intros ? ? ?; apply ra_rel_fun.
    + intros y; destruct (Hg (y##x##v)) as (e & ? & _).
      exists e; auto.
  Qed.
  
End ra_enum.
