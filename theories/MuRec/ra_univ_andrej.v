(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Omega.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_nat utils_list crt.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.MuRec 
  Require Import recalg ra_utils ra_enum recomp ra_recomp beta ra_godel_beta.

From Undecidability.DiophantineConstraints 
  Require Import H10C Util.h10c_utils.

Set Implicit Arguments.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

Definition h10uc_eq a' b' (c : nat*nat*nat) :=
  match c with (x,y,z) => 
    let vx := godel_beta a' b' x in
    let vy := godel_beta a' b' y in
    let vz := godel_beta a' b' z 
    in 1+vx+vy*vy = vz 
  end.

Definition h10uc_test a' b' x y z := 
  let vx := godel_beta a' b' x in
  let vy := godel_beta a' b' y in
  let vz := godel_beta a' b' z 
  in if eq_nat_dec (1+vx+vy*vy) vz then 0 else 1.

Definition idx_h10uc a b p : h10uc :=
  (godel_beta a b (3*p), godel_beta a b (1+3*p), godel_beta a b (2+3*p)).

Definition nat_h10luc k :=
   let n := decomp_r k           in
   let a := decomp_l (decomp_l k) in
   let b := decomp_r (decomp_l k) 
   in  map (fun p => idx_h10uc a b (pos2nat p)) (pos_list n).

(** nat_h10luc is surjective 

    needed to map an H10UC instance to a instance of the universal solver 

*) 

Fact nat_h10luc_surj lc : { k | lc = nat_h10luc k }.
Proof.
  destruct (list_vec_full lc) as (v & <-).
  set (n := length lc).
  set (f p := match le_lt_dec n p with
    | left _   => (0,0,0)
    | right Hp => vec_pos v (nat2pos Hp)
  end).
  destruct godel_beta_fun_inv_triples with (n := n) (f := f)
    as (a & b & Hab).
  exists (recomp (recomp a b) n).
  unfold nat_h10luc. 
  repeat (rewrite decomp_l_recomp).
  repeat rewrite decomp_r_recomp.
  rewrite map_pos_list_vec; f_equal.
  apply vec_pos_ext; intros p; rewrite vec_pos_set.
  unfold idx_h10uc; rewrite <- Hab; auto.
  2: apply pos2nat_prop.
  unfold f, n.
  destruct (le_lt_dec (length lc) (pos2nat p)) as [ H | H ].
  + generalize (pos2nat_prop p); try omega.
  + rewrite nat2pos_pos2nat; auto.
Qed. 

Section ra_h10uc.

  Let s : recalg 1.
  Proof.
    ra root ra_mult; ra arg pos0.
  Defined. 

  Let s_val x : ⟦s⟧ (x##vec_nil) (x*x).
  Proof.
    unfold s.
    exists (x##x##vec_nil); split; auto.
    pos split; simpl; auto.
  Qed.

  Definition ra_h10uc : recalg 5.
  Proof.
    ra root ra_not.
    ra root ra_not.
    ra root ra_eq.
    + ra root ra_succ.
      ra root ra_plus.
      * ra root ra_godel_beta.
        - ra arg pos3.
        - ra arg pos4.
        - ra arg pos0.
      * ra root s.
        ra root ra_godel_beta.
        - ra arg pos3.
        - ra arg pos4.
        - ra arg pos1.
    + ra root ra_godel_beta.
      * ra arg pos3.
      * ra arg pos4.
      * ra arg pos2.
  Defined.

  Opaque ra_not ra_eq ra_plus ra_mult ra_cst_n ra_godel_beta.

  Fact ra_h10uc_prim_rec : prim_rec ra_h10uc.
  Proof. ra prim rec. Qed.

  Opaque s.

  Variable x y z a' b' : nat.

  Let vx := godel_beta a' b' x.
  Let vy := godel_beta a' b' y.
  Let vz := godel_beta a' b' z.

  Fact ra_h10uc_val  : ⟦ra_h10uc⟧ (x##y##z##a'##b'##vec_nil) (h10uc_test a' b' x y z).
  Proof.
    exists (1-ite_rel (1+vx+vy*vy-vz) (vz-(1+vx+vy*vy)) 1##vec_nil); split.
    { generalize (ra_not_val (1-ite_rel (1+vx+vy*vy-vz) (vz-(1+vx+vy*vy)) 1)).
      intros H; eq goal H; f_equal.
      unfold ite_rel, h10uc_test.
      fold vx; fold vy; fold vz.
      case_eq (1 + vx + vy * vy - vz); destruct (eq_nat_dec (1+vx+vy*vy) vz); intros; omega. }
    pos split; simpl.
    exists (ite_rel (1+vx+vy*vy-vz) (vz-(1+vx+vy*vy)) 1##vec_nil); split.
    { apply ra_not_val. }
    pos split; simpl.
    exists (1+vx+vy*vy##vz##vec_nil); split; auto.
    { apply ra_eq_val. }
    pos split; simpl; auto.
    + exists (vx+vy*vy##vec_nil); split; auto.
      { simpl; auto. }
      pos split; simpl; auto.
      exists (vx##vy*vy##vec_nil); split; auto.
      pos split; simpl; auto.
      * exists (a'##b'##x##vec_nil); split; auto.
        { apply ra_godel_beta_val. }
        pos split; simpl; auto.
      * exists (vy##vec_nil); split; auto.
        pos split.
        exists (a'##b'##y##vec_nil); split; auto.
        { apply ra_godel_beta_val. }
        pos split; simpl; auto.
    + exists (a'##b'##z##vec_nil); split; auto.
      { apply ra_godel_beta_val. }
      pos split; simpl; auto.
  Qed.

End ra_h10uc.

Hint Resolve ra_h10uc_prim_rec ra_h10uc_val : core.
Opaque ra_h10uc.

Section ra_iter_h10uc.

  Let t3 : recalg 1.
  Proof.
    ra root ra_mult.
    - ra cst 3.
    - ra arg pos0.
  Defined.

  Let t3_val n : ⟦t3⟧ (n##vec_nil) (3*n).
  Proof.
    exists (3##n##vec_nil); split; auto.
    pos split; simpl; auto.
    apply ra_cst_n_val.
  Qed. 

  Let f : recalg 5.
  Proof.
    ra root ra_h10uc.
    + ra root ra_godel_beta.
      * ra arg pos1.
      * ra arg pos2.
      * ra root t3.
        ra arg pos0.
    + ra root ra_godel_beta.
      * ra arg pos1.
      * ra arg pos2.
      * ra root ra_succ.
        ra root t3.
        ra arg pos0.
    + ra root ra_godel_beta.
      * ra arg pos1.
      * ra arg pos2.
      * ra root ra_succ.
        ra root ra_succ.
        ra root t3.
        ra arg pos0.
    + ra arg pos3.
    + ra arg pos4.
  Defined.

  Opaque ra_godel_beta ra_mult ra_cst_n.

  Let f_pr : prim_rec f.
  Proof. ra prim rec. Qed.

  Opaque t3 mult.

  Let f_val n a b a' b' : ⟦f⟧ (n##a##b##a'##b'##vec_nil) 
                            (h10uc_test a' b' (godel_beta a b (3*n))
                                              (godel_beta a b (1+3*n))
                                              (godel_beta a b (2+3*n))).
  Proof.
    exists (godel_beta a b (3*n)##godel_beta a b (1+3*n)##godel_beta a b (2+3*n)##a'##b'##vec_nil); split; auto.
    pos split; simpl; auto.
    + exists (a##b##3*n##vec_nil); split; auto.
      pos split; simpl; auto.
      exists (n##vec_nil); split; auto.
      pos split; simpl; auto.
    + exists (a##b##1+3*n##vec_nil); split; auto.
      pos split; simpl; auto.
      exists (3*n##vec_nil); split; auto.
      { simpl; auto. }
      pos split; simpl.
      exists (n##vec_nil); split; auto.
      pos split; simpl; auto.
    + exists (a##b##2+3*n##vec_nil); split; auto.
      pos split; simpl; auto.
      exists (1+3*n##vec_nil); split; auto.
      { simpl; auto. }
      pos split; simpl; auto.
      exists (3*n##vec_nil); split; auto.
      { simpl; auto. }
      pos split; simpl.
      exists (n##vec_nil); split; auto.
      pos split; simpl; auto.
  Qed.

  Opaque f.
 
  Definition ra_iter_h10uc : recalg 5.
  Proof.
    ra root ra_not.
    ra root ra_not.
    apply (ra_lsum f).
  Defined.

  Fact ra_iter_h10uc_prim_rec : prim_rec ra_iter_h10uc.
  Proof. ra prim rec. Qed.

  Section ra_iter_spec.

    Variable (n a b a' b' : nat).

    Fact ra_iter_h10uc_val_0 :
          (forall p, p < n -> h10uc_eq a' b' (idx_h10uc a b p))
       -> ⟦ra_iter_h10uc⟧ (n##a##b##a'##b'##vec_nil) 0.
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
      unfold h10uc_eq, idx_h10uc in H2.
      generalize (f_val p a b a' b').
      unfold h10uc_test.
      match type of H2 with
        | ?a = ?b => destruct (eq_nat_dec a b)
      end; auto; lia.
    Qed.

    Fact ra_iter_h10uc_val_1 :
          (exists p, p < n /\ ~ h10uc_eq a' b' (idx_h10uc a b p)) 
       -> ⟦ra_iter_h10uc⟧ (n##a##b##a'##b'##vec_nil) 1.
    Proof.
      intros H2; simpl.
      exists (0##vec_nil); split.
      { apply ra_not_val. }
      pos split; simpl; auto.
      destruct ra_lsum_S with (1 := f_pr) (i := n) (v := a##b##a'##b'##vec_nil)
        as (k & Hk).
      { destruct H2 as (p & H2 & H3).
        exists p, 0; split; auto.
        unfold h10uc_eq, idx_h10uc in H3.
        generalize (f_val p a b a' b').
        unfold h10uc_test.
        match type of H3 with
          | ?a <> ?b => destruct (eq_nat_dec a b)
        end; auto; lia. }
      exists (S k##vec_nil); split.
      { apply ra_not_val. }
      pos split; simpl; auto.
    Qed.

  End ra_iter_spec.

End ra_iter_h10uc.

Hint Resolve ra_iter_h10uc_prim_rec : core.
Opaque ra_iter_h10uc.

Section ra_univ_ad.

  Let f : recalg 2.
  Proof.
    ra root ra_iter_h10uc.
    + ra root ra_decomp_r.
      ra arg pos1.
    + ra root ra_decomp_l.
      ra root ra_decomp_l.
      ra arg pos1.
    + ra root ra_decomp_r.
      ra root ra_decomp_l.
      ra arg pos1.
    + ra root ra_decomp_l.
      ra arg pos0.
    + ra root ra_decomp_r.
      ra arg pos0.
  Defined.

  Opaque ra_decomp_l ra_decomp_r.

  Let Hf_pr : prim_rec f.
  Proof. ra prim rec. Qed.

  Variables (lc : list h10uc) (k : nat)
            (Hlc : lc = nat_h10luc k).

  Let Hf_val_0 v : 
        (forall c, In c lc -> h10uc_sem (godel_beta (decomp_l v) (decomp_r v)) c)
     -> ⟦f⟧ (v##k##vec_nil) 0.
  Proof.
    intros H2.
    exists (decomp_r k##decomp_l (decomp_l k)##decomp_r (decomp_l k)##
            decomp_l v##decomp_r v##vec_nil); split.
    + apply ra_iter_h10uc_val_0.
      intros p Hp.
      apply H2; subst.
      unfold idx_h10uc.
      apply in_map_iff.
      exists (nat2pos Hp); split.
      * rewrite pos2nat_nat2pos; auto.
      * apply pos_list_prop.
    + pos split; simpl; auto.
      * exists (k##vec_nil); split; auto.
        pos split; simpl; auto.
      * exists (decomp_l k##vec_nil); split; auto.
        pos split; simpl; auto.
        exists (k##vec_nil); split; auto.
        pos split; simpl; auto.
      * exists (decomp_l k##vec_nil); split; auto.
        pos split; simpl; auto.
        exists (k##vec_nil); split; auto.
        pos split; simpl; auto.
      * exists (v##vec_nil); split; auto.
        pos split; simpl; auto.
      * exists (v##vec_nil); split; auto.
        pos split; simpl; auto.
  Qed.
 
  Let Hf_val_1 v : 
        (exists c, In c lc /\ ~ h10uc_sem (godel_beta (decomp_l v) (decomp_r v)) c)
     -> ⟦f⟧ (v##k##vec_nil) 1.
  Proof.
    intros H2.
    exists (decomp_r k##decomp_l (decomp_l k)##decomp_r (decomp_l k)##
            decomp_l v##decomp_r v##vec_nil); split.
    + apply ra_iter_h10uc_val_1.
      destruct H2 as (c & H1 & H2).
      rewrite Hlc in H1.
      unfold nat_h10luc in H1.
      apply in_map_iff in H1.
      destruct H1 as (p & H1 & _).
      exists (pos2nat p); split.
      * apply pos2nat_prop.
      * rewrite H1; auto.
    + pos split; simpl; auto.
      * exists (k##vec_nil); split; auto.
        pos split; simpl; auto.
      * exists (decomp_l k##vec_nil); split; auto.
        pos split; simpl; auto.
        exists (k##vec_nil); split; auto.
        pos split; simpl; auto.
      * exists (decomp_l k##vec_nil); split; auto.
        pos split; simpl; auto.
        exists (k##vec_nil); split; auto.
        pos split; simpl; auto.
      * exists (v##vec_nil); split; auto.
        pos split; simpl; auto.
      * exists (v##vec_nil); split; auto.
        pos split; simpl; auto.
  Qed.

  Let Hf_tot v : ⟦f⟧ (v##k##vec_nil) 0 \/ ⟦f⟧ (v##k##vec_nil) 1.
  Proof.
    destruct (h10luc_sem_dec lc (godel_beta (decomp_l v) (decomp_r v)))
      as [ (c & H) | H ].
    + right; apply Hf_val_1; exists c; auto.
    + left; apply Hf_val_0; auto.
  Qed.

  Definition ra_univ_ad : recalg 1.
  Proof. apply ra_min, f. Defined.

  Opaque f.

  Theorem ra_univ_ad_spec : ex (⟦ra_univ_ad⟧ (k##vec_nil)) 
                     <-> exists φ, forall c, In c lc -> h10uc_sem φ c.
  Proof.
    split.
    + intros (v & Hv).
      simpl in Hv; red in Hv.
      destruct Hv as (H1 & H2).
      destruct (h10luc_sem_dec lc (beta v))
        as [ (c & H) | H ].
      * assert (⟦ f ⟧ (v ## k ## vec_nil) 1) as C.
        { apply Hf_val_1; exists c; auto. }
        generalize (ra_rel_fun _ _ _ _ H1 C); discriminate.
      * exists (beta v); auto.
    + intros (phi & Hphi).
      destruct (godel_beta_fun_inv (h10luc_bound lc) phi)
        as (a & b & Hab).
      generalize (h10luc_bound_prop _ _ Hab); clear Hab; intros Hab.
      apply ra_min_ex; auto.
      exists (recomp a b); simpl.
      apply Hf_val_0.
      intros c Hc; rewrite decomp_l_recomp, decomp_r_recomp; apply Hab; auto.
  Qed.

End ra_univ_ad.
