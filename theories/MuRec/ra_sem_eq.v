(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Omega.

From Undecidability.Shared Require Import DLW.Utils.utils DLW.Utils.finite DLW.Vec.vec DLW.Vec.pos.
From Undecidability.MuRec Require Import recalg ra_bs recursor minimizer ra_ca.

Set Implicit Arguments.

Notation "[| f |]" := (@ra_rel _ f) (at level 0).

Section soundness_and_completeness.

  (* By induction on the ra_ca predicate *)

  Lemma ra_ca_inc_bs k (f : recalg k) v x : (exists n, [f;v] -[n>> x) -> [f;v] ~~> x.
  Proof.
    intros (n & H); revert H.
    induction 1 as [ n v | v | v
                   | k v p 
                   | k i f gj v n w q x H1 IH1 H2 IH2 
                   | k f g v n x H1 IH2 
                   | k f g v n p x q y H1 IH1 H2 IH2
                   | k f v p n w q H1 IH1 H2 IH2 ]; try (constructor; auto; fail).
    apply in_ra_bs_comp with w; auto.
    apply in_ra_bs_rec_S with x; auto.
    apply in_ra_bs_min with w; auto.
  Qed.

  (* By induction on the ra_bs predicate *)

  Lemma ra_bs_inc_rel k (f : recalg k) v x : [f;v] ~~> x -> [|f|] v x.
  Proof.
    induction 1 as [ n v | v | v
                   | k v p 
                   | k i f gj v w x H1 IH1 H2  
                   | k f g v n x H1  
                   | k f g v n x y H1 IH1 H2 
                   | k f v n w H1 IH1 H2 ]; try reflexivity.
    exists w; split; auto; intros; rewrite vec_pos_set; auto.
    red; unfold s_rec; simpl; auto.
    rewrite ra_rel_fix_rec in IH1 |- *; unfold s_rec in IH1 |- *.
    simpl in IH1 |- *; exists x; auto.
    rewrite ra_rel_fix_min; unfold s_min; split; auto.    
    intros y Hy.
    exists (vec_pos w (nat2pos Hy)).
    generalize (IH1 (nat2pos Hy)).
    rewrite pos2nat_nat2pos.
    eqgoal; do 2 f_equal.
  Qed.
  
  (* By induction on f *)
  
  Lemma ra_rel_inc_ca k (f : recalg k) v x : [|f|] v x -> exists n, [f;v] -[n>> x.
  Proof.
    revert v x; induction f as [ k | | | k p | k i f gj Hf Hgj 
                               | k f g Hf Hg 
                               | ]; intros v x.
    rewrite ra_rel_fix_cst; unfold s_cst; intros []; exists 1; constructor.
    rewrite ra_rel_fix_zero; unfold s_zero; intro; subst; exists 1; constructor.
    rewrite ra_rel_fix_succ; unfold s_succ; intro; subst; exists 1; constructor.
    rewrite ra_rel_fix_proj; unfold s_proj; intros []; exists 1; constructor.
    
    rewrite ra_rel_fix_comp; unfold s_comp; intros (w & H1 & H2).
    apply Hf in H1; destruct H1 as (n & H1).
    assert (forall p, exists n, [vec_pos gj p;v] -[n>> vec_pos w p) as H3.
      intros p; specialize (H2 p); rewrite vec_pos_map in H2; auto.
    apply vec_reif in H3.
    destruct H3 as (m & Hm).
    exists (1+n+vec_sum m).
    apply in_ra_ca_comp with (2 := H1); auto.
    
    rewrite ra_rel_fix_rec; unfold s_rec.
    rewrite (vec_head_tail v); simpl; generalize (vec_head v) (vec_tail v).
    clear v; intros i v.
    revert x; induction i as [ | i IHi ]; intros x; simpl.
    intros H; apply Hf in H; destruct H as (n & Hn); exists (S n); constructor; auto.
    intros (y & H1 & H2).
    apply IHi in H1; destruct H1 as (n & Hn).
    apply Hg in H2; destruct H2 as (m & Hm).
    exists (1+n+m); apply in_ra_ca_rec_S with (1 := Hn); auto.
    
    rewrite ra_rel_fix_min; unfold s_min; intros (H1 & H2).
    assert (forall (p : pos x), exists r, [|f|] (pos2nat p##v) (S r)) as H3.
      intros p; apply (H2 _ (pos2nat_prop p)).
    apply vec_reif in H3.
    destruct H3 as (w & Hw).
    assert (forall p, exists n, [f;pos2nat p##v] -[n>> S (vec_pos w p)) as H3.
      intros p; apply IHf, Hw.
    apply vec_reif in H3.
    destruct H3 as (m & Hm).
    apply IHf in H1.
    destruct H1 as (n & Hn).
    exists (1+n+vec_sum m).
    apply in_ra_ca_min with (1 := Hm); auto.
  Qed.
  
  (** Hence, there is a correspondance between the relational semantics
      and the bigstep semantics of recalg.
   **)

  Hint Resolve ra_ca_inc_bs ra_bs_inc_rel ra_rel_inc_ca : core.
  
  Theorem ra_bs_correct k (f : recalg k) v x : [|f|] v x <-> [f;v] ~~> x.
  Proof. split; auto. Qed.

  Theorem ra_ca_correct k (f : recalg k) v x : [|f|] v x <-> exists n, [f;v] -[n>> x.
  Proof. split; auto. Qed.

End soundness_and_completeness.

