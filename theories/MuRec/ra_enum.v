(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Eqdep_dec Omega.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_nat.

From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.

From Undecidability.MuRec Require Import recalg ra_utils.

Set Implicit Arguments.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

Section ra_enum.

  Variable f : recalg 1.

  Let a : recalg 2.
  Proof. apply ra_comp with (1 := f), (ra_proj pos0##vec_nil). Defined.

  Let Ha v x : ⟦a⟧ v x <-> ⟦f⟧ (vec_pos v pos0##vec_nil) x.
  Proof.
    unfold a.
    rewrite ra_rel_fix_comp; simpl.
    split.
    + intros (w & H1 & H2); revert H1 H2.
      vec split w with y; vec nil w; intros H1 H2.
      specialize (H2 pos0); simpl in H2; red in H2; subst; auto.
    + intros H; exists (vec_pos v pos0##vec_nil); split; auto.
      intros p; analyse pos p; simpl; red; auto.
  Qed.
  
  Let b : recalg 2.
  Proof.
    apply ra_comp with (1 := ra_succ), (ra_proj pos1##vec_nil).
  Defined.

  Let Hb v x : ⟦b⟧ v x <-> x = S (vec_pos v pos1).
  Proof.
    unfold b; simpl; split.
    + intros (w & H1 & H2); revert H1 H2.
      vec split w with y; vec nil w; intros H1 H2.
      specialize (H2 pos0); simpl in H2; red in H2; subst; auto.
    + intros H; exists (vec_pos v pos1##vec_nil); subst; split; auto.
      * red; auto.
      * intros p; analyse pos p; simpl; red; auto.
  Qed.

  Opaque a b.

  Let g : recalg 2.
  Proof.
    apply ra_comp with (1 := ra_eq), (a##b##vec_nil).
  Defined.

  Hypothesis Hf : forall v, exists x, ⟦f⟧ v x.

  Let Hg v : exists e, ⟦g⟧ v e /\ (e = 0 <-> ⟦f⟧ (vec_pos v pos0##vec_nil) (S (vec_pos v pos1))).
  Proof.
    unfold g.
    destruct (Hf (vec_pos v pos0##vec_nil)) as (x & Hx).
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

  Definition ra_enum : recalg 1.
  Proof. apply ra_min, g. Defined.

  (* A reduction of listability into recursive computability *)

  Fact ra_enum_spec x : ex (⟦ra_enum⟧ (x##vec_nil)) <-> exists n, ⟦f⟧ (n##vec_nil) (S x).
  Proof.
    unfold ra_enum; simpl; unfold s_min.
    rewrite μ_min_of_total.
    + split.
      * intros (r & Hr).
        destruct (Hg (r##x##vec_nil)) as (e & H1 & H2).
        simpl in H2.
        exists r; apply H2.
        revert H1 Hr; apply ra_rel_fun.
      * intros (n & Hn); exists n.
        destruct (Hg (n##x##vec_nil)) as (e & H1 & H2).
        apply H2 in Hn; subst; auto.
    + intros ? ? ?; apply ra_rel_fun.
    + intros y; destruct (Hg (y##x##vec_nil)) as (e & ? & _).
      exists e; auto.
  Qed.
  
End ra_enum.