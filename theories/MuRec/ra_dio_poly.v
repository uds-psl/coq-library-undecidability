(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith.

From Undecidability.Shared.Libs.DLW 
  Require Import utils_tac utils_nat pos vec.

From Undecidability.MuRec 
  Require Import recalg ra_utils recomp ra_recomp.

From Undecidability.H10.Dio 
  Require Import dio_single.

Set Implicit Arguments.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

Section dio_poly.

  Variable (n m : nat).

  Fixpoint ra_dio_poly (p : dio_polynomial (pos n) (pos m)) : recalg (n+m).
  Proof.
    destruct p as [ c | i | x | [] p q ].
    + apply ra_cst_n, c.
    + apply ra_proj, pos_left, i. 
    + apply ra_proj, pos_right, x.
    + apply ra_comp with (1 := ra_plus), (ra_dio_poly p##ra_dio_poly q##vec_nil).
    + apply ra_comp with (1 := ra_mult), (ra_dio_poly p##ra_dio_poly q##vec_nil).
  Defined.

  Fact ra_dio_poly_prim p : prim_rec (ra_dio_poly p).
  Proof.
    induction p as [ | | | [] ]; simpl; repeat (split; auto);
      intros j; analyse pos j; simpl; auto.
  Qed.

  Opaque ra_cst_n ra_plus ra_mult ra_inject ra_project ra_eq.

  Section ra_dio_poly_eval.

    Variable (v : vec nat (n+m)).

    Notation φ := (fun i => vec_pos v (pos_left _ i)).
    Notation ν := (fun i => vec_pos v (pos_right _ i)).

    Fact ra_dio_poly_val p : ⟦ra_dio_poly p⟧ v (dp_eval φ ν p).
    Proof.
      induction p as [ c | i | x | [] p Hp q Hq ]; simpl.
      + apply ra_cst_n_val.
      + cbv; auto.
      + cbv; auto.
      + exists (dp_eval φ ν p ## dp_eval φ ν q ## vec_nil); split.
        * apply ra_plus_val.
        * intros j; analyse pos j; simpl; auto.
      + exists (dp_eval φ ν p ## dp_eval φ ν q ## vec_nil); split.
        * apply ra_mult_val.
        * intros j; analyse pos j; simpl; auto.
    Qed.

    Variable (p q : dio_polynomial (pos n) (pos m)).

    Definition ra_dio_poly_eq : recalg (n+m).
    Proof.
      apply ra_comp with (1 := ra_eq).
      refine (_##_##vec_nil); apply ra_dio_poly.
      + exact p.
      + exact q.
    Defined.

    Hint Resolve ra_dio_poly_prim : core.
  
    Fact ra_dio_poly_eq_prim : prim_rec ra_dio_poly_eq.
    Proof.
      simpl; split; auto.
      intros j; analyse pos j; auto.
    Qed. 

    Fact ra_dio_poly_eq_val : { e | ⟦ra_dio_poly_eq⟧ v e /\ (e = 0 <-> dp_eval φ ν p = dp_eval φ ν q) }.
    Proof.
      destruct ra_eq_rel with (v := dp_eval φ ν p ## dp_eval φ ν q ## vec_nil) as (e & H1 & H2); simpl in H2.
      exists e; split; auto.
      simpl.
      exists (dp_eval φ ν p ## dp_eval φ ν q ## vec_nil); split; auto.
      intros i; analyse pos i; simpl; apply ra_dio_poly_val.
    Qed.

    Opaque ra_dio_poly_eq.

    Hint Resolve ra_dio_poly_eq_prim : core.

    Definition ra_dio_poly_test : recalg (S m).
    Proof.
      apply ra_comp with (1 := ra_dio_poly_eq).
      apply vec_set_pos; intros i.
      destruct (pos_both _ _ i) as [ j | j ].
      + apply ra_comp with (1 := ra_project j), (ra_proj pos0 ## vec_nil).
      + apply ra_proj, pos_nxt, j.
    Defined.

    Fact ra_dio_poly_test_prim : prim_rec ra_dio_poly_test.
    Proof.
      simpl; split; auto.
      intros i.
      rewrite vec_pos_set.
      destruct (pos_both n m i).
      + simpl; split; auto.
        intros j; analyse pos j; simpl; auto.
      + simpl; auto.
    Qed.

    Fact ra_dio_poly_test_total : total ⟦ra_dio_poly_test⟧.
    Proof. apply prim_rec_tot, ra_dio_poly_test_prim. Qed.

  End ra_dio_poly_eval.

  Notation φ := (fun x w i => vec_pos (vec_app (project n x) w) (pos_left _ i)).
  Notation ν := (fun x w i => vec_pos (vec_app (project n x) w) (pos_right _ i)).

  Variable (p q : dio_polynomial (pos n) (pos m)).

  Fact ra_dio_poly_test_val x w : { e | ⟦ra_dio_poly_test p q⟧ (x##w) e /\ (e = 0 <-> dp_eval (φ x w) (ν x w) p 
                                                                                    = dp_eval (φ x w) (ν x w) q) }.
  Proof.
    destruct (ra_dio_poly_eq_val (vec_app (project n x) w) p q) as (e & H1 & H2).
    exists e; split; auto.
    exists (vec_app (project n x) w); split; auto.
    intros i; repeat rewrite vec_pos_set.
    generalize (pos_lr_both n m i). 
    destruct (pos_both n m i) as [ j | j ]; intros Hj; subst i; simpl.
    * unfold vec_app; rewrite vec_pos_set, pos_both_left.
      exists (x##vec_nil); split.
      - apply ra_project_val.
      - intros k; analyse pos k; simpl; cbv; auto.
    * unfold vec_app; rewrite vec_pos_set, pos_both_right; reflexivity.
  Qed.

  Fact ra_dio_poly_test_rel v e : ⟦ra_dio_poly_test p q⟧ v e
                               -> e = 0 <-> dp_eval (φ (vec_head v) (vec_tail v)) 
                                                    (ν (vec_head v) (vec_tail v)) p 
                                          = dp_eval (φ (vec_head v) (vec_tail v)) 
                                                    (ν (vec_head v) (vec_tail v)) q.
  Proof.
    vec split v with x; intros H; simpl vec_head; simpl vec_tail.
    destruct (ra_dio_poly_test_val x v) as (e' & H1 & H2).
    rewrite <- H2; clear H2.
    generalize (ra_rel_fun _ _ _ _ H H1); intros []; tauto.
  Qed.

  Opaque ra_dio_poly_test.

  Definition ra_dio_poly_find : recalg m.
  Proof. apply ra_min, (ra_dio_poly_test p q). Defined.

  Lemma ra_dio_poly_find_rel w : (exists e, ⟦ra_dio_poly_find⟧ w e) <-> exists x, ⟦ra_dio_poly_test p q⟧ (x##w) 0.
  Proof.
    simpl; unfold s_min.
    apply μ_min_of_total.
    + intros ? ? ?; apply ra_rel_fun.
    + intros x; destruct (ra_dio_poly_test_val x w) as (e & ? & _).
      exists e; auto.
  Qed.

  (* ra_dio_poly_find terminates on w iff some solution of p(w,x1,...,xn) = q(w,x1,...,xn) exists 

      so termination of ra_dio_poly_find terminates on w simulates the existence of a solution
      to a given diophantine equation *)

  Theorem ra_dio_poly_find_spec w :  ex (⟦ra_dio_poly_find⟧ w) 
                                <-> exists v, dp_eval (vec_pos v) (vec_pos w) p 
                                            = dp_eval (vec_pos v) (vec_pos w) q.
  Proof.
    rewrite ra_dio_poly_find_rel; split.
    + intros (x & Hx).
      destruct (ra_dio_poly_test_val x w) as (e & H1 & H2).
      generalize (ra_rel_fun _ _ _ _ H1 Hx); rewrite H2.
      exists (project n x); auto.
      eq goal H; f_equal; apply dp_eval_ext; intro; try rewrite vec_pos_app_left; auto;
        rewrite vec_pos_app_right; auto.
    + intros (v & Hv).
      exists (inject v).
      destruct (ra_dio_poly_test_val (inject v) w) as (e & H1 & H2).
      rewrite project_inject in H2.
      assert (e=0); try (subst; auto; fail).
      apply H2.
      eq goal Hv; f_equal; apply dp_eval_ext; intro; try rewrite vec_pos_app_left; auto;
        rewrite vec_pos_app_right; auto.
  Qed.

End dio_poly.

Opaque ra_dio_poly_find.

Section dio_ra_enum.

  (* Given p = q in dio_eq (pos 1) (pos m), given a total
     µ-rec function of type recalg 1 that enumerates the solutions 

     given n compute x#w in vec nat (1+m). Compute 
     p[x][w] = q[x][w]. If equal, return (S x), otherwise return 0 *)

   Variable (m : nat) (p q : dio_polynomial (pos m) (pos 1)).

   Let f := ra_dio_poly_test p q.
 
   Let Hf x w : {e : nat |
       ⟦ f ⟧ (x ## w) e /\
       (e = 0 <->
        dp_eval
          (fun i => vec_pos (vec_app (project m x) w) (pos_left 1 i))
          (fun i => vec_pos (vec_app (project m x) w) (pos_right m i))
          p =
        dp_eval
          (fun i => vec_pos (vec_app (project m x) w) (pos_left 1 i))
          (fun i => vec_pos (vec_app (project m x) w) (pos_right m i)) q) }.
  Proof. apply ra_dio_poly_test_val. Qed.

  Opaque f.

  Let g : recalg 1.
  Proof.
    apply ra_comp with (1 := ra_ite).
    refine (_##_##_##vec_nil).
    + apply ra_comp with (1 := f), ra_vec_project.
    + apply ra_comp with (1 := ra_succ).
      refine (_##vec_nil).
      apply (@ra_project 2 pos1).
    + apply ra_cst_n, 0.
  Defined.

  Opaque ra_decomp_l ra_decomp_r ra_project.

  Let Hg0 : prim_rec g.
  Proof.
    simpl; split; auto.
    intros j; analyse pos j; auto.
    + simpl; split; auto.
      * apply ra_dio_poly_test_prim.
      * intros j; analyse pos j; simpl; auto; split; auto.
    + simpl; split; auto.
      intros j; analyse pos j; auto.
  Qed.

  Let Hg1 x : ex (⟦g⟧ (x##vec_nil)).
  Proof. apply prim_rec_tot; auto. Qed.

  (* Not a very nice proof ... *)

  Let Hg x : (exists n, ⟦g⟧ (n##vec_nil) (S x)) <-> exists w, dp_eval (vec_pos w) (fun _ => x) p
                                                            = dp_eval (vec_pos w) (fun _ => x) q.
  Proof.
    split.
    + intros (n & w & H1 & H2).
      apply ra_ite_rel in H1.
      generalize (H2 pos0) (H2 pos1) (H2 pos2).
      clear H2; revert H1.
      repeat rewrite vec_pos_set.
      vec split w with a; vec split w with b; vec split w with c; vec nil w; clear w.
      simpl; intros H1 H2 H3 H4.
      destruct H3 as (w & H3 & H5).
      generalize (H5 pos0); revert H3; clear H5.
      vec split w with d; vec nil w; clear w; simpl; intros H3 H5.
      apply ra_project_rel in H5; simpl in H5.
      destruct H4 as (w & H4 & _); red in H4; clear w.
      destruct H2 as (w & H2 & H6).
      generalize (H6 pos0) (H6 pos1); clear H6.
      revert H2; vec split w with u; vec split w with v; vec nil w; clear w; simpl.
      intros H2 H6 H7.
      apply ra_project_rel in H6.
      apply ra_project_rel in H7.
      simpl in H5, H6, H7.
      subst c b d u v.
      apply ra_dio_poly_test_rel in H2; simpl in H2.
      exists (project m (decomp_l n)).
      apply proj1 in H2.
      destruct a; try discriminate.
      simpl in H1; injection H1; clear H1; intros H1.
      specialize (H2 eq_refl); subst x.
      eq goal H2; f_equal; apply dp_eval_ext;
        try (intros; rewrite vec_pos_app_left; auto);
        intros j _; analyse pos j; rewrite vec_pos_app_right; simpl; auto.
    + intros (w & Hw).
      destruct (Hf (inject w) (x##vec_nil)) as (e & H1 & H2).
      assert (e = 0) as He.
      { apply H2.
        eq goal Hw; f_equal; apply dp_eval_ext;
          try (intros j _; rewrite vec_pos_app_left; rewrite project_inject; auto);
          intros j _; analyse pos j; rewrite vec_pos_app_right; simpl; auto. }
      clear H2; subst e.
      exists (inject (inject w##x##vec_nil)).
      unfold g.
      exists (0##S x##0##vec_nil); split.
      * apply ra_ite_rel; simpl; auto.
      * intros j; rewrite vec_pos_set; analyse pos j; simpl.
        - exists (inject w ## x ## vec_nil); split; auto.
          intros j; analyse pos j; simpl.
          { apply ra_project_rel; simpl.
            rewrite decomp_l_recomp; auto. }
          { apply ra_project_rel; simpl.
            rewrite decomp_r_recomp, decomp_l_recomp; auto. }
        - exists (x##vec_nil); split; try (red; auto; fail).
          intros j; analyse pos j; simpl.
          apply ra_project_rel; simpl.
          rewrite decomp_r_recomp, decomp_l_recomp; auto.
        - exists vec_nil; split; try (red; auto; fail).
          intros j; analyse pos j.
  Qed.

  Theorem dio_poly_eq_2_ra_prim : 
          { g : recalg 1 | prim_rec g 
               /\ forall x, (exists n, ⟦g⟧ (n##vec_nil) (S x)) 
                         <-> exists w, dp_eval (vec_pos w) (fun _ => x) p
                                     = dp_eval (vec_pos w) (fun _ => x) q }.
  Proof. exists g; split; auto. Qed. 

End dio_ra_enum.

 

 
