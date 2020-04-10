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
  Require Import utils_tac utils_nat utils_list.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.MuRec 
  Require Import recalg ra_utils ra_enum recomp ra_recomp beta ra_godel_beta.

From Undecidability.H10C 
  Require Import h10c_defs h10c_utils.

Set Implicit Arguments.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

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

Opaque ra_eq ra_beta ra_decomp_l ra_decomp_r ra_ite ra_cst_n ra_plus ra_mult.
Opaque ra_decomp_l ra_decomp_r ra_recomp.
Opaque ra_lsum ra_not ra_choice3 ra_beta.

Section ra_h10c.

  Let x0 : recalg 2.
  Proof.
    ra root ra_beta.
    + ra arg pos1.
    + ra root ra_decomp_r.
      ra arg pos0.
  Defined.

  Let x : recalg 2.
  Proof.
   ra root ra_beta.
    + ra arg pos1.
    + ra root ra_decomp_l.
      ra root ra_decomp_r.
      ra root ra_decomp_r.
      ra arg pos0.
  Defined.

  Let y : recalg 2.
  Proof.
    ra root ra_beta.
    + ra arg pos1.
    + ra root ra_decomp_r.
      ra root ra_decomp_r.
      ra root ra_decomp_r.
      ra arg pos0.
  Defined.

  Let z : recalg 2.
  Proof.
    ra root ra_beta.
    + ra arg pos1.
    + ra root ra_decomp_l.
      ra root ra_decomp_r.
      ra arg pos0.
  Defined.

  Let Hx0 c v : ⟦x0⟧ (c##v##vec_nil) (beta v (decomp_r c)).
  Proof.
    exists (v##decomp_r c##vec_nil); split; simpl; auto.
    pos split; simpl; auto.
    exists (c##vec_nil); split; simpl; auto.
    pos split; simpl; auto.
  Qed.

  Let Hx c v : ⟦x⟧ (c##v##vec_nil) (beta v (decomp_l (decomp_r (decomp_r c)))).
  Proof.
    exists (v##decomp_l (decomp_r (decomp_r c))##vec_nil); split; simpl; auto.
    pos split; simpl; auto.
    exists (decomp_r (decomp_r c)##vec_nil); split; simpl; auto.
    pos split; simpl; auto.
    exists (decomp_r c##vec_nil); split; simpl; auto.
    pos split; simpl; auto.
    exists (c##vec_nil); split; simpl; auto.
    pos split; simpl; auto.
  Qed.

  Let Hy c v : ⟦y⟧ (c##v##vec_nil) (beta v (decomp_r (decomp_r (decomp_r c)))).
  Proof.
    exists (v##decomp_r (decomp_r (decomp_r c))##vec_nil); split; simpl; auto.
    pos split; simpl; auto.
    exists (decomp_r (decomp_r c)##vec_nil); split; simpl; auto.
    pos split; simpl; auto.
    exists (decomp_r c##vec_nil); split; simpl; auto.
    pos split; simpl; auto.
    exists (c##vec_nil); split; simpl; auto.
    pos split; simpl; auto.
  Qed.

  Let Hz c v : ⟦z⟧ (c##v##vec_nil) (beta v (decomp_l (decomp_r c))).
  Proof.
    exists (v##decomp_l (decomp_r c)##vec_nil); split; simpl; auto.
    pos split; simpl; auto.
    exists (decomp_r c##vec_nil); split; simpl; auto.
    pos split; simpl; auto.
    exists (c##vec_nil); split; simpl; auto.
    pos split; simpl; auto.
  Qed.
  
  Definition ra_h10c : recalg 2.
  Proof.
    ra root ra_choice3.
    + ra root ra_decomp_l.
      ra arg pos0.
    + ra root ra_eq.
      * exact x0.
      * ra cst 1.
    + ra root ra_eq.
      * ra root ra_plus.
        - exact x.
        - exact y.
      * exact z.
    + ra root ra_eq.
      * ra root ra_mult.
        - exact x.
        - exact y.
      * exact z.
  Defined.

  Fact ra_h10c_prim_rec : prim_rec ra_h10c.
  Proof. ra prim rec. Qed.

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
      * destruct (decomp_l c) as [ | [] ]; auto; lia.
    + pos split; simpl.
      * exists (c##vec_nil); split; simpl; auto.
        pos split; simpl; auto.
      * exists (beta v i0##1##vec_nil); split; simpl; auto.
        - apply ra_eq_val.
        - pos split; simpl; auto.
          apply Hx0.
      * exists (beta v i+beta v j##beta v k##vec_nil); split; simpl; auto.
        - apply ra_eq_val.
        - pos split; simpl; auto.
          2: apply Hz.
          exists (beta v i##beta v j##vec_nil); split; simpl; auto.
          pos split; simpl; auto.
          ++ apply Hx.
          ++ apply Hy.
      * exists (beta v i*beta v j##beta v k##vec_nil); split; simpl; auto.
        - apply ra_eq_val.
        - pos split; simpl; auto.
          2: apply Hz.
          exists (beta v i##beta v j##vec_nil); split; simpl; auto.
          pos split; simpl; auto.
          ++ apply Hx.
          ++ apply Hy.
  Qed.

End ra_h10c.

Hint Resolve ra_h10c_prim_rec ra_h10c_val : core.
Opaque ra_h10c.

Section iter_h10c.

  Let f : recalg 3.
  Proof.
    ra root ra_h10c.
    + ra root ra_beta.
      * ra arg pos1.
      * ra arg pos0.
    + ra arg pos2.
  Defined. 

  Let Hf_pr : prim_rec f.
  Proof. ra prim rec. Qed.

  Let Hf_val i lc v : ⟦f⟧ (i##lc##v##vec_nil) (h10c_test (beta lc i) v).
  Proof.
    exists (beta lc i##v##vec_nil); split; auto.
    pos split; simpl; auto.
    exists (lc##i##vec_nil); split; auto.
    pos split; simpl; auto.
  Qed.
 
  Definition ra_iter_h10c : recalg 3.
  Proof.
    ra root ra_not.
    ra root ra_not.
    apply (ra_lsum f).
  Defined.

  Fact ra_iter_h10c_prim_rec : prim_rec ra_iter_h10c.
  Proof. ra prim rec. Qed.

  Section ra_iter_spec.

    Variable (n lc v : nat).

    Fact ra_iter_h10c_val_0 :
          (forall p, p < n -> h10c_sem (nat_h10c (beta lc p)) (beta v)) 
       -> ⟦ra_iter_h10c⟧ (n##lc##v##vec_nil) 0.
    Proof.
      intros H2; simpl.
      exists (1##vec_nil); split.
      { apply ra_not_val. }
      pos split; simpl; auto.
      exists (0##vec_nil); split.
      { apply ra_not_val. }
      pos split; simpl; auto.
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
      pos split; simpl; auto.
      destruct ra_lsum_S with (1 := Hf_pr) (i := n) (v := lc##v##vec_nil)
        as (k & Hk).
      { destruct H2 as (p & H2 & H3).
        rewrite <- h10c_test_spec, h10c_test_stable in H3.
        case_eq (h10c_test (beta lc p) v).
        { intros; lia. }
        intros k Hk.
        exists p, k; rewrite <- Hk; split; auto. }
      exists (S k##vec_nil); split.
      { apply ra_not_val. }
      pos split; simpl; auto.
    Qed.

  End ra_iter_spec.

End iter_h10c.

Hint Resolve ra_iter_h10c_prim_rec : core.
Opaque ra_iter_h10c.

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
  Proof. ra prim rec. Qed.

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
    + pos split; simpl; auto.
      * exists (k##vec_nil); split; auto.
        pos split; simpl; auto.
      * exists (k##vec_nil); split; auto.
        pos split; simpl; auto.
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
      unfold nat_h10lc in H1.
      apply in_map_iff in H1.
      destruct H1 as (p & H1 & _).
      exists (pos2nat p); split.
      * apply pos2nat_prop.
      * rewrite H1; auto.
    + pos split; simpl; auto.
      * exists (k##vec_nil); split; auto.
        pos split; simpl; auto.
      * exists (k##vec_nil); split; auto.
        pos split; simpl; auto.
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

  Theorem ra_univ_spec : ex (⟦ra_univ⟧ (k##vec_nil)) 
                     <-> exists φ, forall c, In c lc -> h10c_sem c φ.
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
