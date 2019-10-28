(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Eqdep_dec Omega.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_nat utils_list.

From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.

From Undecidability.MuRec Require Import recalg ra_utils ra_enum.

From Undecidability.Problems Require Import H10C.

Set Implicit Arguments.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

Section ra_lsum.

  (** Given a prim rec algo recalg 1 and n
      returns f 0 v + f 1 v + ... + f (n-1) v *) 

  Variable (n : nat) (f : recalg (S n)) (Hf : prim_rec f).

  Let Hf' : forall v, exists x, ⟦f⟧ v x.
  Proof. apply prim_rec_tot; auto. Qed.

  Let h : recalg (S (S n)).
  Proof.
    apply ra_comp with (1 := ra_plus).
    refine (_##_##vec_nil).
    + apply ra_comp with (1 := f).
      apply vec_set_pos.
      intros p; invert pos p.
      * apply (ra_proj pos0).
      * apply (ra_proj (pos_nxt (pos_nxt p))).
    + apply (ra_proj pos1).
  Defined.

  Opaque ra_plus.

  Let h_prim_rec : prim_rec h.
  Proof.
    simpl; split; auto.
    repeat (intros p; analyse pos p; simpl; split; auto).
    intros p; analyse pos p; simpl; auto.
    rewrite vec_pos_set; simpl; auto.
  Qed.

  Let Hh i x v r : ⟦h⟧ (i##x##v) r <-> exists y, ⟦f⟧ (i##v) y /\ r = y+x. 
  Proof.
    unfold h; rewrite ra_rel_fix_comp; simpl; split.
    + intros (w & H1 & H2).
      rewrite ra_plus_rel in H1; revert H1 H2.
      vec split w with u1; vec split w with u2; vec nil w; clear w.
      intros H1 H2; simpl in H1.
      generalize (H2 pos0) (H2 pos1); simpl.
      clear H2; intros H2 H3.
      cbv in H3; subst u2.
      destruct H2 as (w & H2 & H3); revert H2 H3.
      vec split w with u2; intros H2 H3.
      generalize (H3 pos0) (fun p => H3 (pos_nxt p)); simpl; clear H3.
      intros H3 H4; cbv in H3; subst u2.
      exists u1; split; auto.
      eq goal H2; do 2 f_equal.
      apply vec_pos_ext.
      intros p; specialize (H4 p).
      repeat rewrite vec_pos_set in H4.
      simpl in H4; red in H4; simpl in H4; auto.
    + intros (y & H1 & H2).
      exists (y##x##vec_nil); split.
      { subst; apply ra_plus_val. }
      intros p; analyse pos p; simpl.
      2: { cbv; auto. }
      exists (i##v); split; auto.
      intros p; invert pos p. 
      * cbv; auto.
      * do 2 rewrite vec_pos_set; simpl; red; simpl; auto.
  Qed.

  Opaque h ra_cst_n.

  Definition ra_lsum : recalg (S n).
  Proof.
    apply ra_rec.
    + apply (ra_cst_n _ 0).
    + apply h.
  Defined.

  Fact ra_lsum_prim_rec : prim_rec ra_lsum.
  Proof. 
    simpl; split; auto.
  Qed.

  Fact ra_lsum_spec i v lr : 
          Forall2 ⟦f⟧ (map (fun x => x##v) (list_an 0 i)) lr
       -> ⟦ra_lsum⟧ (i##v) (lsum lr).
  Proof.
    revert lr.
    induction i as [ | i IHi ]; intros lr H.
    + simpl in H.
      apply Forall2_nil_inv_l in H; subst lr; simpl.
      red; simpl; apply ra_cst_n_val.
    + replace (S i) with (i+1) in H by omega.
      rewrite list_an_plus, map_app in H. 
      apply Forall2_app_inv_l in H.
      destruct H as (l1 & l2 & H1 & H2 & ->).
      rewrite lsum_app.
      rewrite plus_comm in H2; simpl in H2.
      apply Forall2_cons_inv_l in H2.
      destruct H2 as (yn & l3 & H2 & -> & H3).
      apply Forall2_nil_inv_l in H3; subst l3.
      simpl; red; simpl.
      exists (lsum l1); split.
      * apply IHi; auto.
      * apply Hh; exists yn; split; auto; omega.
  Qed.

  Fact ra_lsum_0 i v :
        (forall p, p < i -> ⟦f⟧ (p##v) 0) -> ⟦ra_lsum⟧ (i##v) 0.
  Proof.
    intros H.
    assert (lsum (map (fun _ => 0) (list_an 0 i)) = 0) as E.
    { clear v H; generalize 0 at 2; induction i; intros j; simpl; auto. }
    rewrite <- E.
    apply ra_lsum_spec.
    rewrite Forall2_map_left, Forall2_map_right, Forall2_Forall, Forall_forall.
    intros p; rewrite list_an_spec; intros Hp; apply H; omega.
  Qed.

  Fact ra_lsum_S i v :
        (exists p k, p < i /\ ⟦f⟧ (p##v) (S k)) 
     -> exists k, ⟦ra_lsum⟧ (i##v) (S k).
  Proof.
    intros H.
    assert (forall p : pos i, ex (⟦ f ⟧ (pos2nat p##v))) as H1.
    { intro; apply Hf'. }
    apply vec_reif in H1.
    destruct H1 as (w & Hw).
    assert (⟦ra_lsum⟧ (i##v) (lsum (vec_list w))) as H1.
    { apply ra_lsum_spec.
      rewrite <- pos_list2nat, map_map, map_pos_list_vec.
      apply Forall2_vec_list.
      intro; rewrite vec_pos_set; auto. }
    assert (0 < lsum (vec_list w)) as H2.
    { destruct H as (p & k & Hp & H2).
      apply lt_le_trans with (S k); try omega.
      apply le_lsum, vec_list_In_iff.
      exists (nat2pos Hp).
      specialize (Hw (nat2pos Hp)).
      rewrite pos2nat_nat2pos in Hw.
      revert H2 Hw; apply ra_rel_fun. }
    clear H Hw.
    revert H1 H2.
    generalize (lsum (vec_list w)).
    intros [ | k ]; intros; try omega; exists k; auto.
  Qed.

End ra_lsum.

Hint Resolve ra_lsum_prim_rec.

Opaque ra_lsum.

Check ra_lsum_prim_rec.
Check ra_lsum_spec.

Definition h10c_nat (c : h10c) :=
  match c with
    | h10c_one x      => recomp 0 x
    | h10c_plus x y z => recomp 1 (recomp z (recomp x y))
    | h10c_mult x y z => recomp 2 (recomp z (recomp x y))
  end.

Definition nat_h10c (n : nat) :=
  match decomp_l n with 
    | 0 => h10c_one (decomp_r n)
    | 1 => h10c_plus (decomp_l (decomp_r (decomp_r n)))
                     (decomp_r (decomp_r (decomp_r n)))
                     (decomp_l (decomp_r n))
    | _ => h10c_mult (decomp_l (decomp_r (decomp_r n)))
                     (decomp_r (decomp_r (decomp_r n)))
                     (decomp_l (decomp_r n))
  end.

Lemma nat_h10c_nat c : nat_h10c (h10c_nat c) = c.
Proof.
  destruct c; simpl; unfold nat_h10c; 
    repeat (rewrite decomp_l_recomp || rewrite decomp_r_recomp); auto.
Qed.

Definition nat_test_eq a b := ite_rel (a-b) (b-a) 1.

Fact nat_test_eq_spec0 a : nat_test_eq a a = 0.
Proof. 
  unfold nat_test_eq.
  replace (a-a) with 0; simpl; omega.
Qed.

Fact nat_test_eq_spec1 a b : a <> b -> nat_test_eq a b > 0.
Proof.
  intros H.
  destruct (lt_eq_lt_dec a b) as [ [] | ]; try tauto; unfold nat_test_eq.
  + replace (a-b) with 0; simpl; omega.
  + replace (a-b) with (S (a-S b)); simpl; omega.
Qed.

Fact nat_test_eq_spec a b : nat_test_eq a b = 0 <-> a = b.
Proof.
  split.
  + intros H.
    destruct (eq_nat_dec a b) as [ | D ]; auto.
    apply nat_test_eq_spec1 in D; omega.
  + intros ->; apply nat_test_eq_spec0.
Qed.

Opaque ra_eq ra_beta ra_decomp_l ra_decomp_r ra_ite ra_cst_n ra_plus ra_mult.

Section ra_choice3.

(*  Variable (n : nat) (f g h : recalg n) 
           (Hf : prim_rec f) (Hg : prim_rec g) (Hh : prim_rec h). *)

  Definition ra_choice3 : recalg 4.
  Proof.
    apply ra_comp with (1 := ra_ite).
    refine (_##_##_##vec_nil).
    + apply ra_comp with (1 := ra_eq).
      refine (_##_##vec_nil).
      * apply (ra_proj pos0).
      * apply (ra_cst_n _ 0).
    + apply (ra_proj pos1).
    + apply ra_comp with (1 := ra_ite).
      refine (_##_##_##vec_nil).
      * apply ra_comp with (1 := ra_eq).
        refine (_##_##vec_nil).
        - apply (ra_proj pos0).
        - apply (ra_cst_n _ 1).
      * apply (ra_proj pos2).
      * apply (ra_proj pos3).
  Defined.

  Fact ra_choice3_prim_rec : prim_rec ra_choice3.
  Proof.
    simpl; split; auto.
    repeat (intros p; analyse pos p; simpl; split; auto).
  Qed.

  Fact ra_choice3_val b x y z : ⟦ra_choice3⟧ (b##x##y##z##vec_nil) 
                                  (match b with 0 => x | 1 => y | _ => z end).
  Proof.
    simpl.
    exists (nat_test_eq b 0##x##match b with 1 => y | _ => z end##vec_nil).
    simpl; split.
    { apply ra_ite_rel; simpl.
      destruct b as [ | [] ]; simpl; auto. }
    intros p; analyse pos p; simpl.
    + exists (b##0##vec_nil); split.
      * apply ra_eq_val.
      * intros p; analyse pos p; simpl.
        { cbv; auto. }
        apply ra_cst_n_val.
    + cbv; auto.
    + exists (nat_test_eq b 1##y##z##vec_nil).
      simpl; split.
      { apply ra_ite_rel; simpl.
        destruct b as [ | [] ]; simpl; auto. }
      intros p; analyse pos p; simpl.
      * exists (b##1##vec_nil); split.
        - apply ra_eq_val.
        - intros p; analyse pos p; simpl.
          { cbv; auto. }
          apply ra_cst_n_val.
      * cbv; auto.
      * cbv; auto.
  Qed.

  Fact ra_choice3_spec b x y z d :
        (b = 0  -> d = x)
     -> (b = 1  -> d = y)
     -> (2 <= b -> d = z)
     -> ⟦ra_choice3⟧ (b##x##y##z##vec_nil) d.
  Proof.
    intros H1 H2 H3.
    destruct b as [ | [] ].
    + rewrite H1; auto; apply ra_choice3_val.
    + rewrite H2; auto; apply ra_choice3_val.
    + rewrite H3; try omega.
      apply ra_choice3_val.
  Qed.

End ra_choice3.

Opaque ra_choice3.

Hint Resolve ra_choice3_prim_rec.

Definition h10c_test c v :=
  match decomp_l c with 
    | 0 => let x := decomp_r c in nat_test_eq (beta v x) 1
    | 1 => let x := decomp_l (decomp_r (decomp_r c)) in
           let y := decomp_r (decomp_r (decomp_r c)) in
           let z := decomp_l (decomp_r c)
           in  nat_test_eq (beta v x + beta v y) (beta v z) 
    | _ => let x := decomp_l (decomp_r (decomp_r c)) in
           let y := decomp_r (decomp_r (decomp_r c)) in
           let z := decomp_l (decomp_r c)
           in  nat_test_eq (beta v x * beta v y) (beta v z) 
  end.

Fact h10c_test_stable c v : h10c_test (h10c_nat (nat_h10c c)) v = h10c_test c v.
Proof.
  unfold h10c_test, h10c_nat, nat_h10c.
  destruct (decomp_l c) as [ | [] ];
  repeat (rewrite decomp_l_recomp || rewrite decomp_r_recomp); auto.
Qed.

Fact h10c_test_spec c v : h10c_test (h10c_nat c) v = 0 <-> h10c_sem c (beta v).
Proof.
  destruct c as [ x | x y z | x y z ]; unfold h10c_test, h10c_nat;
    repeat (rewrite decomp_l_recomp || rewrite decomp_r_recomp); unfold h10c_sem;
    apply nat_test_eq_spec.
Qed.

Section ra_h10c.

  Let x0 : recalg 2.
  Proof.
    apply ra_comp with (1 := ra_beta).
    refine (ra_proj pos1##_##vec_nil).
    apply ra_comp with (1 := ra_decomp_r); refine (_##vec_nil).
    apply (ra_proj pos0).
  Defined.

  Let x : recalg 2.
  Proof.
    apply ra_comp with (1 := ra_beta).
    refine (ra_proj pos1##_##vec_nil).
    apply ra_comp with (1 := ra_decomp_l); refine (_##vec_nil).
    apply ra_comp with (1 := ra_decomp_r); refine (_##vec_nil).
    apply ra_comp with (1 := ra_decomp_r); refine (_##vec_nil).
    apply (ra_proj pos0).
  Defined.

  Let y : recalg 2.
  Proof.
    apply ra_comp with (1 := ra_beta).
    refine (ra_proj pos1##_##vec_nil).
    apply ra_comp with (1 := ra_decomp_r); refine (_##vec_nil).
    apply ra_comp with (1 := ra_decomp_r); refine (_##vec_nil).
    apply ra_comp with (1 := ra_decomp_r); refine (_##vec_nil).
    apply (ra_proj pos0).
  Defined.

  Let z : recalg 2.
  Proof.
    apply ra_comp with (1 := ra_beta).
    refine (ra_proj pos1##_##vec_nil).
    apply ra_comp with (1 := ra_decomp_l); refine (_##vec_nil).
    apply ra_comp with (1 := ra_decomp_r); refine (_##vec_nil).
    apply (ra_proj pos0).
  Defined.

  Let Hx0 c v : ⟦x0⟧ (c##v##vec_nil) (beta v (decomp_r c)).
  Proof.
    exists (v##decomp_r c##vec_nil); split.
    { apply ra_beta_val. }
    intros p; analyse pos p; simpl.
    { cbv; auto. }
    exists (c##vec_nil); split.
    { apply ra_decomp_r_val. }
    intros p; analyse pos p; simpl.
    cbv; auto.
  Qed.

  Let Hx c v : ⟦x⟧ (c##v##vec_nil) (beta v (decomp_l (decomp_r (decomp_r c)))).
  Proof.
    exists (v##decomp_l (decomp_r (decomp_r c))##vec_nil); split.
    { apply ra_beta_val. }
    intros p; analyse pos p; simpl.
    { cbv; auto. }
    exists (decomp_r (decomp_r c)##vec_nil); split.
    { apply ra_decomp_l_val. }
    intros p; analyse pos p; simpl.
    exists (decomp_r c##vec_nil); split.
    { apply ra_decomp_r_val. }
    intros p; analyse pos p; simpl.
    exists (c##vec_nil); split.
    { apply ra_decomp_r_val. }
    intros p; analyse pos p; simpl.
    cbv; auto.
  Qed.

  Let Hy c v : ⟦y⟧ (c##v##vec_nil) (beta v (decomp_r (decomp_r (decomp_r c)))).
  Proof.
    exists (v##decomp_r (decomp_r (decomp_r c))##vec_nil); split.
    { apply ra_beta_val. }
    intros p; analyse pos p; simpl.
    { cbv; auto. }
    exists (decomp_r (decomp_r c)##vec_nil); split.
    { apply ra_decomp_r_val. }
    intros p; analyse pos p; simpl.
    exists (decomp_r c##vec_nil); split.
    { apply ra_decomp_r_val. }
    intros p; analyse pos p; simpl.
    exists (c##vec_nil); split.
    { apply ra_decomp_r_val. }
    intros p; analyse pos p; simpl.
    cbv; auto.
  Qed.

  Let Hz c v : ⟦z⟧ (c##v##vec_nil) (beta v (decomp_l (decomp_r c))).
  Proof.
    exists (v##decomp_l (decomp_r c)##vec_nil); split.
    { apply ra_beta_val. }
    intros p; analyse pos p; simpl.
    { cbv; auto. }
    exists (decomp_r c##vec_nil); split.
    { apply ra_decomp_l_val. }
    intros p; analyse pos p; simpl.
    exists (c##vec_nil); split.
    { apply ra_decomp_r_val. }
    intros p; analyse pos p; simpl.
    cbv; auto.
  Qed.
  
  Definition ra_h10c : recalg 2.
  Proof.
    apply ra_comp with (1 := ra_choice3).
    refine (_##_##_##_##vec_nil).
    + apply ra_comp with (1 := ra_decomp_l).
      refine (_##vec_nil).
      apply (ra_proj pos0).
    + apply ra_comp with (1 := ra_eq).
      exact (x0##ra_cst_n _ 1##vec_nil).
    + apply ra_comp with (1 := ra_eq).
      refine (_##z##vec_nil).
      apply ra_comp with (1 := ra_plus).
      refine (x##y##vec_nil).
    + apply ra_comp with (1 := ra_eq).
      refine (_##z##vec_nil).
      apply ra_comp with (1 := ra_mult).
      refine (x##y##vec_nil).
  Defined.

  Fact ra_h10c_prim_rec : prim_rec ra_h10c.
  Proof.
    simpl; split; auto.
    repeat (repeat (intros p; analyse pos p; simpl; split; auto); repeat split; auto).
  Qed.

  Opaque x0 x y z.

  Fact ra_h10c_val c v : ⟦ra_h10c⟧ (c##v##vec_nil) (h10c_test c v).
  Proof.
    simpl.
    set (i0 := decomp_r c).
    set (i := decomp_l (decomp_r (decomp_r c))).
    set (j := decomp_r (decomp_r (decomp_r c))).
    set (k := decomp_l (decomp_r c)).
    exists (decomp_l c##nat_test_eq (beta v i0) 1
                      ##nat_test_eq (beta v i + beta v j) (beta v k) 
                      ##nat_test_eq (beta v i * beta v j) (beta v k)
                      ##vec_nil).
    split.
    + apply ra_choice3_spec; intros H; unfold h10c_test.
      * rewrite H; auto.
      * rewrite H; auto.
      * destruct (decomp_l c) as [ | [] ]; auto; omega.
    + intros p; analyse pos p; simpl.
      * exists (c##vec_nil); split.
        { apply ra_decomp_l_val. }
        intros p; analyse pos p; simpl.
        cbv; auto.
      * exists (beta v i0##1##vec_nil); split.
        { apply ra_eq_val. }
        intros p; analyse pos p; simpl.
        apply Hx0.
        apply ra_cst_n_val.
      * exists (beta v i+beta v j##beta v k##vec_nil); split.
        { apply ra_eq_val. }
        intros p; analyse pos p; simpl.
        2: apply Hz.
        exists (beta v i##beta v j##vec_nil); split.
        { apply ra_plus_val. }
        intros p; analyse pos p; simpl.
        apply Hx.
        apply Hy.
      * exists (beta v i*beta v j##beta v k##vec_nil); split.
        { apply ra_eq_val. }
        intros p; analyse pos p; simpl.
        2: apply Hz.
        exists (beta v i##beta v j##vec_nil); split.
        { apply ra_mult_val. }
        intros p; analyse pos p; simpl.
        apply Hx.
        apply Hy.
  Qed.

End ra_h10c.

Opaque ra_h10c.

Hint Resolve ra_h10c_prim_rec.
      
Check ra_h10c_val.
Check ra_h10c_prim_rec.

Ltac fill_vec := 
  match goal with 
    | |- vec _ O     => apply vec_nil
    | |- vec _ (S _) => refine (_##_); [ | fill_vec ]
  end.

Tactic Notation "ra" "root" uconstr(f) := 
  apply ra_comp with (1 := f); fill_vec.

Tactic Notation "ra" "cst" constr(f) :=
  apply (ra_cst_n _ f).

Tactic Notation "ra" "arg" uconstr(f) :=
  apply (ra_proj f).

Opaque ra_minus.

Section ra_not.

  Definition ra_not : recalg 1.
  Proof.
    ra root ra_minus.
    ra cst 1.
    ra arg pos0.
  Defined.

  Fact ra_not_prim_rec : prim_rec ra_not.
  Proof.
    split; auto.
    repeat (intros p; analyse pos p; simpl; split; auto).
  Qed.

  Fact ra_not_val n : ⟦ra_not⟧ (n##vec_nil) (1-n).
  Proof.
    exists (1##n##vec_nil); split.
    + apply ra_minus_val.
    + intros p; analyse pos p; simpl.
      * apply ra_cst_n_val.
      * cbv; auto.
  Qed. 

End ra_not.

Opaque ra_not.

Hint Resolve ra_not_prim_rec.

Check nat_h10c.

Definition nat_h10lc k :=
   let n  := decomp_l k in
   let lc := decomp_r k
   in  map (fun p => nat_h10c (beta lc (pos2nat p))) (pos_list n).

(** nat_h10lc is surjective 

    needed to map an H10C instance to a instance of the universal solver 

*) 

Fact nat_h10lc_surj lc : { k | lc = nat_h10lc k }.
Proof.
  destruct (list_vec lc) as (v & <-).
  generalize (length lc) v; clear lc v.
  intros n v.
  set (w := vec_map h10c_nat v).
  destruct beta_inv with (v := w) as (lc & Hlc).
  exists (recomp n lc).
  unfold nat_h10lc.
  rewrite decomp_l_recomp.
  rewrite map_pos_list_vec; f_equal.
  apply vec_pos_ext; intros p.
  rewrite vec_pos_set, decomp_r_recomp, Hlc.
  unfold w; rewrite vec_pos_map, nat_h10c_nat.
  auto.
Qed.

Opaque ra_lsum ra_h10c.

Section iter_h10c.

  Let f : recalg 3.
  Proof.
    ra root ra_h10c.
    + ra root ra_beta.
      * ra arg pos1.
      * ra arg pos0.
    + ra arg pos2.
  Defined.

  Opaque ra_beta ra_h10c.

  Let Hf_pr : prim_rec f.
  Proof.
    split; auto.
    repeat (intros p; analyse pos p; simpl; auto; split; auto).
  Qed.

  Let Hf_val i lc v : ⟦f⟧ (i##lc##v##vec_nil) (h10c_test (beta lc i) v).
  Proof.
    exists (beta lc i##v##vec_nil); split.
    { apply ra_h10c_val. }
    intros p; analyse pos p; simpl; auto.
    + exists (lc##i##vec_nil); split.
      { apply ra_beta_val. }
      intros p; analyse pos p; simpl; auto; cbv; auto.
    + cbv; auto.
  Qed.

  Opaque f ra_decomp_l ra_decomp_r.
  
  Definition ra_iter_h10c : recalg 3.
  Proof.
    ra root ra_not.
    ra root ra_not.
    apply (ra_lsum f).
  Defined.

  Fact ra_iter_h10c_prim_rec : prim_rec ra_iter_h10c.
  Proof.
    split; auto.
    repeat (intros p; analyse pos p; simpl; auto; split; auto).
  Qed.

  Section ra_iter_spec.

    Variable (n lc v : nat).

    Fact ra_iter_h10c_val_0 :
          (forall p, p < n -> h10c_sem (nat_h10c (beta lc p)) (beta v)) 
       -> ⟦ra_iter_h10c⟧ (n##lc##v##vec_nil) 0.
    Proof.
      intros H2; simpl.
      exists (1##vec_nil); split.
      { apply ra_not_val. }
      intros p; analyse pos p; simpl.
      exists (0##vec_nil); split.
      { apply ra_not_val. }
      intros p; analyse pos p; simpl.
      apply ra_lsum_0.
      intros p Hp.
      specialize (H2 _ Hp).
      apply h10c_test_spec in H2.
      rewrite h10c_test_stable in H2.
      rewrite <- H2.
      apply Hf_val.
    Qed.

    Fact ra_iter_h10c_val_1 :
          (exists p, p < n /\ ~ h10c_sem (nat_h10c (beta lc p)) (beta v)) 
       -> ⟦ra_iter_h10c⟧ (n##lc##v##vec_nil) 1.
    Proof.
      intros H2; simpl.
      exists (0##vec_nil); split.
      { apply ra_not_val. }
      intros p; analyse pos p; simpl.
      destruct ra_lsum_S with (1 := Hf_pr) (i := n) (v := lc##v##vec_nil)
        as (k & Hk).
      { destruct H2 as (p & H2 & H3).
        rewrite <- h10c_test_spec, h10c_test_stable in H3.
        case_eq (h10c_test (beta lc p) v).
        { intros; omega. }
        intros k Hk.
        exists p, k; rewrite <- Hk; split; auto. }
      exists (S k##vec_nil); split.
      { apply ra_not_val. }
      intros p; analyse pos p; simpl; auto.
    Qed.

  End ra_iter_spec.

End iter_h10c.

Opaque ra_iter_h10c.

Hint Resolve ra_iter_h10c_prim_rec.

Section ra_univ.

  Let f : recalg 2.
  Proof.
    ra root ra_iter_h10c.
    + ra root ra_decomp_l.
      ra arg pos1.
    + ra root ra_decomp_r.
      ra arg pos1.
    + ra arg pos0.
  Defined.

  Let Hf_pr : prim_rec f.
  Proof.
    split; auto.
    repeat (intros p; analyse pos p; simpl; auto; split; auto).
  Qed.

  Variables (lc : list h10c) (k : nat)
            (Hlc : lc = nat_h10lc k).

  Let Hf_val_0 v : 
        (forall c, In c lc -> h10c_sem c (beta v))
     -> ⟦f⟧ (v##k##vec_nil) 0.
  Proof.
    intros H2.
    exists (decomp_l k##decomp_r k##v##vec_nil); split.
    + apply ra_iter_h10c_val_0.
      intros p Hp.
      apply H2; subst.
      unfold nat_h10lc.
      apply in_map_iff.
      exists (nat2pos Hp); split.
      * rewrite pos2nat_nat2pos; auto.
      * apply pos_list_prop.
    + intros p; analyse pos p; simpl.
      * exists (k##vec_nil); split.
        { apply ra_decomp_l_val. }
        intros p; analyse pos p; simpl; cbv; auto.
      * exists (k##vec_nil); split.
        { apply ra_decomp_r_val. }
        intros p; analyse pos p; simpl; cbv; auto.
      * cbv; auto.
  Qed.
 
  Let Hf_val_1 v : 
        (exists c, In c lc /\ ~ h10c_sem c (beta v))
     -> ⟦f⟧ (v##k##vec_nil) 1.
  Proof.
    intros H2.
    exists (decomp_l k##decomp_r k##v##vec_nil); split.
    + apply ra_iter_h10c_val_1.
      destruct H2 as (c & H1 & H2).
      rewrite Hlc in H1.
      apply in_map_iff in H1.
      destruct H1 as (p & H1 & _).
      exists (pos2nat p); split.
      * apply pos2nat_prop.
      * rewrite H1; auto.
    + intros p; analyse pos p; simpl.
      * exists (k##vec_nil); split.
        { apply ra_decomp_l_val. }
        intros p; analyse pos p; simpl; cbv; auto.
      * exists (k##vec_nil); split.
        { apply ra_decomp_r_val. }
        intros p; analyse pos p; simpl; cbv; auto.
      * cbv; auto.
  Qed.

  Let Hf_tot v : ⟦f⟧ (v##k##vec_nil) 0 \/ ⟦f⟧ (v##k##vec_nil) 1.
  Proof.
    destruct (h10lc_sem_dec lc (beta v))
      as [ (c & H) | H ].
    + right; apply Hf_val_1; exists c; auto.
    + left; apply Hf_val_0; auto.
  Qed.

  Definition ra_univ : recalg 1.
  Proof. apply ra_min, f. Defined.

  Opaque f.

  Theorem ra_univ_prop : ex (⟦ra_univ⟧ (k##vec_nil)) <-> H10C_SAT lc.
  Proof.
    split.
    + intros (v & Hv).
      simpl in Hv; red in Hv.
      destruct Hv as (H1 & H2).
      destruct (h10lc_sem_dec lc (beta v))
        as [ (c & H) | H ].
      * assert (⟦ f ⟧ (v ## k ## vec_nil) 1) as C.
        { apply Hf_val_1; exists c; auto. }
        generalize (ra_rel_fun _ _ _ _ H1 C); discriminate.
      * exists (beta v); auto.
    + intros (phi & Hphi).
      destruct (beta_fun_inv (h10lc_bound lc) phi)
        as (v & Hv).
      generalize (h10lc_bound_prop _ _ Hv); clear Hv; intros Hv.
      apply ra_min_ex; auto.
      exists v; simpl.
      apply Hf_val_0.
      intros c Hc; apply Hv; auto.
  Qed.

End ra_univ.
