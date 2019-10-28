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
  Require Import utils_tac utils_nat gcd crt sums.

From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.

From Undecidability.MuRec Require Import recalg.

Set Implicit Arguments.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

Local Notation power := (mscal mult 1).

Section iter.

  Variable (X : Type) (f : X -> X). 

  Fixpoint iter n x :=
    match n with 
      | 0   => x
      | S n => f (iter n x)
    end.

  Fact iter_plus n m x : iter (n+m) x = iter n (iter m x).
  Proof. induction n; simpl; f_equal; auto. Qed.

  Fact iter_S n x : iter (S n) x = iter n (f x).
  Proof. replace (S n) with (n+1) by omega; apply iter_plus. Qed.

End iter.

Section div_mult.

  Variable (p q : nat) (Hp : p <> 0) (Hq : q <> 0).

  Fact div_rem_mult n : div n (p*q) = div (div n p) q /\ rem n (p*q) = rem n p + p*rem (div n p) q.
  Proof.
    assert (p*q <> 0) as Hpq.
    { intros E; apply mult_is_O in E; omega. }
    apply div_rem_uniq with (p := p*q); auto.
    + generalize (div_rem_spec1 n p)
                 (div_rem_spec1 (div n p) q)
                 (div_rem_spec1 n (p*q)); intros H1 H2 H3.
      rewrite <- H3; rewrite H1 at 1; rewrite H2 at 1; ring.
    + apply div_rem_spec2; auto.
    + generalize (div_rem_spec2 n Hp)
                 (div_rem_spec2 (div n p) Hq); intros H1 H2.
      replace q with (1+(q-1)) at 2 by omega.
      rewrite Nat.mul_add_distr_l.
      apply plus_lt_le_compat; try omega.
      apply mult_le_compat; omega.
  Qed.

  Corollary div_mult n : div n (p*q) = div (div n p) q.
  Proof. apply div_rem_mult. Qed.

  Corollary rem_mult n : rem n (p*q) = rem n p + p*rem (div n p) q.
  Proof. apply div_rem_mult. Qed.

End div_mult.

Section nat_nat2_bij.

  (* An easy to implement bijection nat <-> nat * nat *)

  Let decomp_recomp_full n : n <> 0 -> { a & { b | n = power a 2 * (2*b+1) } }.
  Proof.
    induction on n as IHn with measure n; intros Hn.
    generalize (euclid_2_div n); intros (H1 & H2).
    case_eq (rem n 2).
    + intros H.
      destruct (IHn (div n 2)) as (a & b & H3); try omega.
      exists (S a), b.
      rewrite H1, H, H3, power_S; ring.
    + intros [ | [ | k ] ] Hk; try omega.
      exists 0, (div n 2); rewrite power_0.
      rewrite H1 at 1; rewrite Hk; ring.
  Qed.

  Definition decomp_l n := projT1 (@decomp_recomp_full (S n) (Nat.neq_succ_0 _)).
  Definition decomp_r n := proj1_sig (projT2 (@decomp_recomp_full (S n) (Nat.neq_succ_0 _))).
 
  Fact decomp_lr_spec n : S n = power (decomp_l n) 2 * (2 * (decomp_r n) + 1).
  Proof. apply (proj2_sig (projT2 (@decomp_recomp_full (S n) (Nat.neq_succ_0 _)))). Qed.

  Definition recomp a b := power a 2 * (2*b+1) - 1.
  
  Fact recomp_decomp n : n = recomp (decomp_l n) (decomp_r n).
  Proof. unfold recomp; rewrite <- decomp_lr_spec; omega. Qed.

  Let power_mult_lt_inj a1 b1 a2 b2 : a1 < a2 -> power a1 2 * (2*b1+1) <> power a2 2 * b2.
  Proof.
    intros H1 H.
    replace a2 with (a1+(S (a2-a1-1))) in H by omega.
    rewrite power_plus in H.
    rewrite <- mult_assoc, Nat.mul_cancel_l in H.
    2: generalize (power2_gt_0 a1); omega.
    revert H; rewrite power_S, <- mult_assoc.
    generalize (power (a2-a1-1) 2*b1); intros; omega.
  Qed.

  Let comp_gt a b : power a 2 *(2*b+1) <> 0.
  Proof. 
    intros E; apply mult_is_O in E.
    generalize (power2_gt_0 a); intros; omega.
  Qed. 

  Fact decomp_uniq a1 b1 a2 b2 : power a1 2 * (2*b1+1) = power a2 2 * (2*b2+1) -> a1 = a2 /\ b1 = b2.
  Proof.
    intros H.
    destruct (lt_eq_lt_dec a1 a2) as [ [ H1 | H1 ] | H1 ].
    + exfalso; revert H; apply power_mult_lt_inj; auto.
    + split; auto; subst a2.
      rewrite Nat.mul_cancel_l in H; try omega.
      generalize (power2_gt_0 a1); omega.
    + exfalso; symmetry in H.
      revert H; apply power_mult_lt_inj; auto.
  Qed.

  Let decomp_lr_recomp a b : decomp_l (recomp a b) = a /\ decomp_r (recomp a b) = b.
  Proof.
    apply decomp_uniq; symmetry.
    replace (power a 2 * (2*b+1)) with (S (recomp a b)).
    + apply decomp_lr_spec.
    + unfold recomp; generalize (power a 2 * (2*b+1)) (comp_gt a b); intros; omega.
  Qed.

  Fact decomp_l_recomp a b : decomp_l (recomp a b) = a.
  Proof. apply decomp_lr_recomp. Qed.

  Fact decomp_r_recomp a b : decomp_r (recomp a b) = b.
  Proof. apply decomp_lr_recomp. Qed.

End nat_nat2_bij.

Section prim_min.

  Variable (X : Type) (f : nat -> nat).

  Let min_f n : f n = 0 -> { k | k <= n /\ f k = 0 /\ forall i, i < k -> f i <> 0 }.
  Proof. 
    intros Hn.
    destruct first_which with (P := fun i => f i = 0) as (k & H1 & H2). 
    + intros; apply eq_nat_dec.
    + exists n; auto.
    + exists k; split; auto.
      destruct (le_lt_dec k n); auto.
      destruct (H2 n); auto. 
  Qed.
 
  Let g i := match f i with 0 => i | _ => S i end.

  Let prim_min_rec n a := iter g n a.

  Let prim_min_rec_spec_0 n a : (forall i, i < n -> f (i+a) <> 0) -> forall i, i <= n -> prim_min_rec i a = i+a.
  Proof.
    unfold prim_min_rec.
    revert a; induction n as [ | n IHn ]; intros a Hn.
    + intros i Hi; replace i with 0 by omega; auto.
    + intros [ | i ] Hi; auto.
      * rewrite iter_S.
        unfold g at 2.
        generalize (Hn 0); simpl; intros E.
        destruct (f a); try omega.
        rewrite IHn; try omega.
        intros j Hj.
        replace (j+S a) with (S j+a) by omega.
        apply Hn; omega.
  Qed.

  Let prim_min_rec_spec_1 n a : f a = 0 -> prim_min_rec n a = a.
  Proof.
    intros Ha; unfold prim_min_rec.
    induction n as [ | n IHn ]; auto.
    rewrite iter_S.
    unfold g at 2; rewrite Ha; auto.
  Qed.

  Definition prim_min n := prim_min_rec n 0.

  Fact prim_min_spec n : f n = 0 -> f (prim_min n) = 0 /\ forall i, i < prim_min n -> f i <> 0.
  Proof.
    intros Hn.
    destruct (min_f Hn) as (k & H1 & H2 & H3).
    assert (prim_min n = k) as H4.
    { unfold prim_min. 
      unfold prim_min_rec.
      replace n with (n-k+k) by omega.
      rewrite iter_plus.
      fold (prim_min_rec k 0).
      rewrite prim_min_rec_spec_0 with (n := k) (a := 0); auto.
      rewrite plus_comm; apply prim_min_rec_spec_1; auto.
      intros; apply H3; omega. }
    rewrite H4; auto.
  Qed.

End prim_min.

Section utils.
 
  Definition ra_cst_n n x : recalg n := ra_comp (ra_cst x) vec_nil.

  Fact ra_cst_n_prim n x : prim_rec (ra_cst_n n x).
  Proof. apply prim_rec_bool_spec; reflexivity. Qed. 

  Fact ra_cst_n_val n x v : ⟦ra_cst_n n x⟧ v x.
  Proof.
    exists vec_nil; split.
    + cbv; auto.
    + intro i; analyse pos i.
  Qed.

  Fact ra_cst_n_rel n x v e : ⟦ra_cst_n n x⟧ v e <-> e = x.
  Proof.
    split.
    + intros H; apply ra_rel_fun with (1 := H), ra_cst_n_val.
    + intro; subst; apply ra_cst_n_val.
  Qed.

  Opaque ra_cst_n.

  Hint Resolve ra_cst_n_prim.

  Section ra_iter_n.

    Variable (n : nat) (f : vec nat n -> nat) (af : recalg n) 
                       (Hf : forall v, ⟦af⟧ v (f v))
                       (Haf : prim_rec af)
                       (g : vec nat n -> nat -> nat) (ag : recalg (S n)) 
                       (Hg : forall i v, ⟦ag⟧ (i##v) (g v i))
                       (Hag : prim_rec ag).

    Definition ra_iter_n : recalg (S n).
    Proof.
      apply ra_rec.
      + apply af.
      + apply ra_comp with (S n).
        * apply ag.
        * apply vec_set_pos; intros p.
          apply (ra_proj (pos_nxt p)).
    Defined.

    Fact ra_iter_n_prim : prim_rec ra_iter_n.
    Proof. 
      simpl; repeat (split; auto).
      intros p; analyse pos p.
      + simpl; auto.
      + rewrite vec_pos_set; simpl; auto.
    Qed.

    Fact ra_iter_n_val i v : ⟦ra_iter_n⟧ (i##v) (iter (g v) i (f v)).
    Proof.
      simpl; unfold s_rec.
      induction i as [ | i IHi ]; simpl.
      + apply Hf; auto.
      + exists (iter (g v) i (f v)); split; auto.
        exists (iter (g v) i (f v)## v); split.
        * apply Hg; auto.
        * intros p; analyse_pos p; simpl.
          - red; simpl; auto.
          - repeat rewrite vec_pos_set.
            simpl; red; simpl; auto.
    Qed.

    Fact ra_iter_n_rel v e : ⟦ra_iter_n⟧ v e <-> e = iter (g (vec_tail v)) (vec_pos v pos0) (f (vec_tail v)).
    Proof.
      vec split v with i.
      split.
      + intros H; apply ra_rel_fun with (1 := H), ra_iter_n_val.
      + intros; subst; apply ra_iter_n_val.
    Qed.
      
  End ra_iter_n.

  Hint Resolve ra_iter_n_prim.

  Opaque ra_iter_n.

  Fact eq_equiv X (e a b : X) : a = b -> (e = a <-> e = b).
  Proof. intros []; tauto. Qed.

  Section ra_iter.

    Variable (n : nat) (f : nat -> nat) (af : recalg 1) 
             (Hf : forall v e, ⟦af⟧ v e <-> e = f (vec_head v))
             (Haf : prim_rec af).

    Definition ra_iter : recalg 2.
    Proof.
      apply ra_iter_n.
      + apply (ra_proj pos0).
      + apply ra_comp with 1.
        * apply af.
        * apply (ra_proj pos0 ## vec_nil).
    Defined.

    Fact ra_iter_prim : prim_rec ra_iter.
    Proof. 
      apply ra_iter_n_prim; simpl; auto; split; auto.
      intros p; analyse pos p; simpl; auto.
    Qed.

    Fact ra_iter_rel v e : ⟦ra_iter⟧ v e <-> e = iter f (vec_pos v pos0) (vec_pos v pos1).
    Proof.
      unfold ra_iter; rewrite ra_iter_n_rel with (f := @vec_head _ _) (g := fun _ => f).
      + apply eq_equiv; f_equal.
        vec split v with a; vec split v with b; auto.
      + intros w; simpl; unfold s_proj.
        vec split w with a; simpl; split; auto.
      + intros i w; simpl; unfold s_comp.
          exists (i##vec_nil).
          rewrite Hf; split; auto.
          intro p; analyse pos p; cbv; auto.
    Qed.

  End ra_iter.

  Hint Resolve ra_iter_prim.

  Opaque ra_iter.

  Definition ra_pred := ra_rec (ra_cst 0) (ra_proj pos0).

  Fact ra_pred_prim : prim_rec ra_pred.
  Proof. apply prim_rec_bool_spec; auto. Qed.

  Fact ra_pred_val n : ⟦ra_pred⟧ (n##vec_nil) (n-1).
  Proof.
    simpl; unfold s_rec.
    induction n as [ | n IHn ]; simpl.
    + cbv; trivial.
    + simpl in IHn; exists (n-1); split; auto.
      replace (n-0) with n by omega; cbv; auto.
  Qed.

  Hint Resolve ra_pred_prim.

  Opaque ra_pred.

  Fact ra_pred_rel v e : ⟦ra_pred⟧ v e <-> e = vec_head v - 1.
  Proof.
    vec split v with n; vec nil v; simpl.
    split.
    + intros H.
      apply ra_rel_fun with (1 := H) (2 := ra_pred_val _).
    + intros; subst; apply ra_pred_val.
  Qed.

  Definition ra_plus : recalg 2.
  Proof. apply ra_iter, ra_succ. Defined.

  Fact ra_plus_prim : prim_rec ra_plus.
  Proof. apply prim_rec_bool_spec; auto. Qed.

  Fact ra_plus_rel v e : ⟦ra_plus⟧ v e <-> e = vec_head v + vec_head (vec_tail v).
  Proof.
    unfold ra_plus; simpl.
    rewrite ra_iter_rel with (f := S).
    + vec split v with n; vec split v with m; vec nil v; simpl.
      apply eq_equiv; induction n; simpl; f_equal; auto.
    + intros; simpl; unfold s_succ; simpl; tauto.
  Qed.

  Fact ra_plus_val n m : ⟦ra_plus⟧ (n##m##vec_nil) (n+m).
  Proof. apply ra_plus_rel; simpl; auto. Qed.

  Hint Resolve ra_plus_prim.

  Opaque ra_plus.

  Section ra_minus.

    Let ra_minus_inv : recalg 2.
    Proof. apply ra_iter, ra_pred. Defined.
 
    Let ra_minus_inv_rel v e : ⟦ra_minus_inv⟧ v e <-> e = vec_pos v pos1 - vec_pos v pos0.
    Proof.
      unfold ra_minus_inv; simpl.
      rewrite ra_iter_rel with (f := pred).
      + vec split v with n; vec split v with m; vec nil v; simpl.
        apply eq_equiv; induction n; simpl; omega.
      + intros; simpl; rewrite ra_pred_rel.
        apply eq_equiv; omega.
    Qed.

    Definition ra_minus : recalg 2.
    Proof.
      apply ra_comp with 2.
      + apply ra_minus_inv.
      + refine (_##_##vec_nil).
        * apply (ra_proj pos1).
        * apply (ra_proj pos0).
    Defined.

    Fact ra_minus_prim : prim_rec ra_minus.
    Proof. apply prim_rec_bool_spec; auto. Qed.

    Fact ra_minus_val n m : ⟦ra_minus⟧ (n##m##vec_nil) (n-m).
    Proof.
      exists (m##n##vec_nil); split; auto.
      + rewrite ra_minus_inv_rel; simpl; auto.
      + intro i; analyse pos i; cbv; auto.
    Qed.

    Fact ra_minus_rel v e : ⟦ra_minus⟧ v e <-> e = vec_pos v pos0 - vec_pos v pos1.
    Proof.
      vec split v with n; vec split v with m; vec nil v.
      split.
      + intros H; apply ra_rel_fun with (1 := H), ra_minus_val.
      + intros; subst; apply ra_minus_val.
    Qed.

  End ra_minus.

  Hint Resolve ra_minus_prim.

  Opaque ra_minus.

  Definition ra_mult : recalg 2.
  Proof.
    apply ra_rec.
    apply (ra_zero).
    apply ra_comp with 2.
    apply ra_plus.
    apply vec_cons.
    apply (ra_proj pos1).
    apply vec_cons.
    apply (ra_proj pos2).
    apply vec_nil.
  Defined.

  Fact ra_mult_prim : prim_rec ra_mult.
  Proof. apply prim_rec_bool_spec; auto. Qed.

  Fact ra_mult_val n m : ⟦ra_mult⟧ (n##m##vec_nil) (n*m).
  Proof.
    simpl; unfold s_rec; simpl.
    induction n as [ | n IHn ]; simpl in *.
    + cbv; trivial.
    + exists (n*m); split; auto.
      exists ((n*m)##m##vec_nil); split.
      * apply ra_plus_rel; simpl; ring.
      * intros p; analyse pos p; cbv; trivial.
  Qed.

  Hint Resolve ra_mult_prim.

  Opaque ra_mult.

  Fact ra_mult_rel v e : ⟦ra_mult⟧ v e <-> e = vec_head v * vec_head (vec_tail v).
  Proof.
    vec split v with n; vec split v with m; vec nil v.
    split.
    + intros H; apply ra_rel_fun with (1 := H), ra_mult_val.
    + intros; subst; apply ra_mult_val.
  Qed.

  Definition ra_exp : recalg 2.
  Proof.
    apply ra_iter_n.
    + apply ra_cst_n, 1.
    + apply ra_comp with (1 := ra_mult).
      refine (_##_##vec_nil).
      * apply (ra_proj pos1).
      * apply (ra_proj pos0).
  Defined.

  Fact ra_exp_prim : prim_rec ra_exp.
  Proof. apply prim_rec_bool_spec; auto. Qed.

  Fact ra_exp_val n m : ⟦ra_exp⟧ (n##m##vec_nil) (power n m).
  Proof.
    unfold ra_exp.
    rewrite ra_iter_n_rel with (f := fun _ => 1) (g := fun v i => vec_head v*i).
    + simpl; induction n.
      * rewrite power_0; auto.
      * rewrite power_S; simpl; f_equal; auto.
    + apply ra_cst_n_val.
    + intros i v; vec split v with j; vec nil v; simpl.
      exists (j##i##vec_nil); split.
      * apply ra_mult_val.
      * intros p; analyse pos p; simpl; cbv; auto.
  Qed.

  Fact ra_exp_rel v e : ⟦ra_exp⟧ v e <-> e = power (vec_pos v pos0) (vec_pos v pos1).
  Proof.
    vec split v with n; vec split v with m; vec nil v.
    split.
    + intros H; apply ra_rel_fun with (1 := H), ra_exp_val.
    + intros; subst; apply ra_exp_val.
  Qed.

  Hint Resolve ra_exp_prim.

  Opaque ra_exp.

  Section ite.

    Definition ra_ite : recalg 3.
    Proof.
      apply ra_rec.
      apply (ra_proj pos0).
      apply (ra_proj pos3).
    Defined.

    Fact ra_ite_prim : prim_rec ra_ite.
    Proof. apply prim_rec_bool_spec; auto. Qed.

    Definition ite_rel (b p q : nat) := match b with 0 => p | _ => q end.

    Fact ra_ite_val b p q : ⟦ra_ite⟧ (b##p##q##vec_nil) (ite_rel b p q).
    Proof.
      simpl; unfold s_rec.
      induction b as [ | b IHb ]; simpl.
      + cbv; trivial.
      + exists (ite_rel b p q); split; auto.
        cbv; trivial.
    Qed.

    Fact ra_ite_rel v e : ⟦ra_ite⟧ v e <-> e = ite_rel (vec_pos v pos0) (vec_pos v pos1) (vec_pos v pos2).
    Proof.
      vec split v with b; vec split v with p; vec split v with q; vec nil v.
      split.
      + intros H; apply ra_rel_fun with (1 := H), ra_ite_val.
      + intro; subst; apply ra_ite_val.
    Qed.

    Fact ra_ite_0 p q : ⟦ra_ite⟧ (0##p##q##vec_nil) p.
    Proof. apply ra_ite_val. Qed.

    Fact ra_ite_S b p q : ⟦ra_ite⟧ (S b##p##q##vec_nil) q.
    Proof. apply ra_ite_val. Qed.

  End ite.

  Hint Resolve ra_ite_prim.

  Opaque ra_ite.

  Section ra_eq.

    Definition ra_eq : recalg 2.
    Proof.
      apply ra_comp with (1 := ra_ite).
      refine (_##_##_##vec_nil).
      + apply ra_minus.
      + apply ra_comp with (1 := ra_minus).
        refine (_##_##vec_nil).
        * apply ra_proj, pos1.
        * apply ra_proj, pos0.
      + apply ra_cst_n, 1.
    Defined.

    Fact ra_eq_prim : prim_rec ra_eq.
    Proof. apply prim_rec_bool_spec; auto. Qed.

    Fact ra_eq_val a b : ⟦ra_eq⟧ (a##b##vec_nil) (ite_rel (a-b) (b-a) 1).
    Proof.
      exists (a-b##b-a##1##vec_nil); split.
      + apply ra_ite_val.
      + intros p; analyse pos p; simpl.
        * apply ra_minus_val.
        * exists (b##a##vec_nil); split.
          - apply ra_minus_val.
          - intros p; analyse pos p; simpl; cbv; auto.
        * apply ra_cst_n_val.
    Qed.

    Fact ra_eq_rel v : { e | ⟦ra_eq⟧ v e /\ (e = 0 <-> vec_pos v pos0 = vec_pos v pos1) }.
    Proof.
      vec split v with a; vec split v with b; vec nil v.
      exists (ite_rel (a-b) (b-a) 1); split.
      + apply ra_eq_val.
      + simpl; unfold ite_rel.
        case_eq (a-b); intros; omega.
    Qed.
 
  End ra_eq.

  Hint Resolve ra_eq_prim.

  Opaque ra_eq.

  Section ra_prim_min.

    Variable (n : nat) (f : vec nat n -> nat -> nat) (af : recalg (S n)) 
                       (Hf : forall i v, ⟦af⟧ (i##v) (f v i))
                       (Haf : prim_rec af).

    Let ag : recalg (S n).
    Proof.
      apply ra_comp with 3.
      * apply ra_ite.
      * refine (_##_##_##vec_nil).
        - apply af.
        - apply (ra_proj pos0).
        - apply ra_comp with 1.
          ++ apply ra_succ.
          ++ apply (ra_proj pos0##vec_nil).
    Defined.

    Let ag_prim : prim_rec ag.
    Proof.
      simpl; split; auto.
      intros p; analyse pos p; auto;
      apply prim_rec_bool_spec; auto.
    Qed.

    Let ag_val i v : ⟦ag⟧ (i##v) (ite_rel (f v i) i (S i)).
    Proof.
      simpl; unfold s_comp.
      exists (f v i##i##S i##vec_nil); split.
      apply ra_ite_val.
      intros p; analyse pos p.
      + apply Hf; auto.
      + cbv; auto.
      + simpl; exists (i##vec_nil); split; auto.
        * cbv; auto. 
        * intros q; analyse pos q; cbv; auto.
    Qed.

    Definition ra_prim_min : recalg (S n).
    Proof.
      apply ra_iter_n.
      + apply ra_cst_n, 0.
      + apply ag.
    Defined.

    Opaque ag.

    Fact ra_prim_min_prim : prim_rec ra_prim_min.
    Proof. apply ra_iter_n_prim; auto. Qed.

    Fact ra_prim_min_val i v : ⟦ra_prim_min⟧ (i##v) (prim_min (f v) i).
    Proof.
      unfold ra_prim_min.
      rewrite ra_iter_n_rel with (f := fun _ => 0) (g := fun w i => match f w i with 0 => i | _ => S i end).
      + unfold prim_min; simpl; auto.
      + intros; rewrite ra_cst_n_rel; tauto.
      + intros; apply ag_val.
    Qed.

    Fact ra_prim_min_rel v e : ⟦ra_prim_min⟧ v e <-> e = prim_min (f (vec_tail v)) (vec_head v).
    Proof.
      vec split v with a.
      split.
      + intros H; apply ra_rel_fun with (1 := H), ra_prim_min_val.
      + intros; subst; apply ra_prim_min_val.
    Qed.

  End ra_prim_min.

  Hint Resolve ra_prim_min_prim.

  Opaque ra_prim_min.

  Section ra_prim_max.

    Variable (n : nat) (f : vec nat n -> nat -> nat) (af : recalg (S n)) 
             (Hf : forall a v, ⟦af⟧ (a##v) (f v a))
             (Haf : prim_rec af).
  
    Let ag : recalg (S (S n)).
    Proof.
      apply ra_comp with (1 := ra_minus).
      refine (_##_##vec_nil).
      * apply ra_comp with (1 := ra_succ). 
        apply (ra_proj pos1##vec_nil).
      * apply ra_comp with (1 := af).
        apply vec_cons.
        + apply ra_comp with (1 := ra_succ).
          apply (ra_proj pos0##vec_nil).
        + apply vec_set_pos.
          intros p; apply (ra_proj (pos_nxt (pos_nxt p))).
    Defined.

    Let ag_prim : prim_rec ag.
    Proof.
      simpl; split; auto.
      intros p; analyse pos p; simpl; split; auto.
      + intros p; analyse pos p; simpl; auto.
      + intros p; analyse pos p; simpl; auto.
        * split; auto.
          intros p; analyse pos p; simpl; auto.
        * rewrite vec_pos_set; simpl; auto.
    Qed.

    Let ag_val a b v : ⟦ag⟧ (a##b##v) ((S b) - f v (S a)).
    Proof.
      exists (S b##f v (S a)##vec_nil); split.
      + apply ra_minus_val.
      + intros p.
        repeat rewrite vec_pos_set.
        analyse pos p.
        { simpl; exists (b##vec_nil); split.
          * cbv; auto.
          * intros q; analyse pos q; cbv; auto. }
        { simpl; exists (S a##v); split.
          * apply Hf; auto.
          * intros q; analyse pos q.
            { simpl; exists (a##vec_nil); split.
              - cbv; auto.
              - intros p; analyse pos p; cbv; auto. }
            { simpl; repeat rewrite vec_pos_set.
              simpl; red; simpl; auto. } }
    Qed.

    Opaque ag.

    Definition ra_prim_max : recalg (S (S n)).
    Proof. apply ra_prim_min, ag. Defined.

    Fact ra_prim_max_prim : prim_rec ra_prim_max.
    Proof. apply ra_prim_min_prim; auto. Qed.

    Hypothesis (Hf2 : forall v n, f v n <= f v (S n)).

    Variable (a b : nat) (v : vec nat n).

    Hypothesis (Hb : f v 0 <= b < f v (S a)).

    Fact ra_prim_max_spec : { e | ⟦ra_prim_max⟧ (a##b##v) e /\ f v e <= b /\ b < f v (S e) }.
    Proof.
      exists (prim_min (fun i => S b - f v (S i)) a); split.
      + unfold ra_prim_max.
        rewrite ra_prim_min_rel with (f := fun w i => S (vec_head w) - f (vec_tail w) (S i)); auto.
        intros i w; vec split w with j; simpl vec_tail; simpl vec_head; auto.
      + destruct prim_min_spec with (f := fun i => S b - f v (S i)) (n := a)
          as (H2 & H3); try omega.
        split; try omega.
        revert H3.
        destruct (prim_min (fun j => S b - f v (S j)) a) as [ | k ]; intros H3; try omega.
        specialize (H3 k); omega.
    Qed.

  End ra_prim_max.

  Hint Resolve ra_prim_max_prim.

  Opaque ra_prim_max.

  Section ra_div.

    Let f (v : vec nat 1) k := (vec_head v)*k.

    Let af : recalg 2.
    Proof.
      apply ra_comp with (1 := ra_mult).
      apply (ra_proj pos1##ra_proj pos0##vec_nil).
    Defined.

    Let af_prim : prim_rec af.
    Proof. apply prim_rec_bool_spec; auto. Qed.

    Let af_val k v : ⟦af⟧ (k##v) (f v k).
    Proof.
      vec split v with b. 
      exists (b##k##vec_nil); split.
      + apply ra_mult_val.
      + intro p; analyse pos p; cbv; auto.
    Qed.

    Definition ra_div : recalg 2.
    Proof.
      apply ra_comp with 3.
      * apply ra_prim_max, af.
      * apply (ra_proj pos0##ra_proj pos0##ra_proj pos1##vec_nil).
    Defined.

    Fact ra_div_prim : prim_rec ra_div.
    Proof. 
      simpl; split; auto.
      intros p; analyse pos p; simpl; auto.
    Qed. 

    Let ra_div_spec n m : m <> 0 -> { k | ⟦ra_div⟧ (n##m##vec_nil) k /\ m*k <= n < m*(S k) }.
    Proof.
      unfold ra_div; intros Hm.
      destruct ra_prim_max_spec with (f := f) (af := af) (a := n) (b := n) (v := m##vec_nil)
        as (k & H1 & H2); auto.
      { unfold f; simpl; rewrite Nat.mul_0_r; split; try omega.
        apply le_trans with (1*S n); try omega.
        apply mult_le_compat; omega. }
      exists k; split; auto.
      exists (n##n##m##vec_nil); split; auto.
      intro p; analyse pos p; cbv; auto.
    Qed.

    Fact ra_div_val n m : m <> 0 -> ⟦ra_div⟧ (n##m##vec_nil) (div n m).
    Proof.
      intros Hm.
      generalize (div_rem_spec1 n m) (div_rem_spec2 n Hm); intros H1 H2.
      destruct (ra_div_spec n Hm) as (k & H3 & H4).
      assert (k = div n m); try omega; subst; auto.
      clear H3.
      rewrite Nat.mul_succ_r in H4.
      apply (@div_rem_uniq _ k (n-m*k) (div n m) (rem n m) Hm); try omega. 
      rewrite mult_comm; omega. 
    Qed.

    Fact ra_div_rel v e : vec_pos v pos1 <> 0 -> ⟦ra_div⟧ v e <-> e = div (vec_pos v pos0) (vec_pos v pos1).
    Proof.
      vec split v with a; vec split v with b; vec nil v; intros H.
      split.
      + intros H1; apply ra_rel_fun with (1 := H1), ra_div_val; auto.
      + intros; subst; apply ra_div_val; auto.
    Qed.

  End ra_div.

  Hint Resolve ra_div_prim.

  Opaque ra_div.

  Section ra_rem.

    Definition ra_rem : recalg 2.
    Proof.
      apply ra_comp with (1 := ra_minus).
      refine (_##_##vec_nil).
      + apply (ra_proj pos0).
      + apply ra_comp with (1 := ra_mult).
        refine (_##_##vec_nil).
        * apply (ra_proj pos1).
        * apply ra_div.
    Defined.

    Fact ra_rem_prim : prim_rec ra_rem.
    Proof.
      simpl; split; auto.
      intros p; analyse pos p; simpl; split; auto.
      intros p; analyse pos p; simpl; split; auto.
      * apply ra_prim_max_prim, prim_rec_bool_spec; auto.
      * intros p; analyse pos p; simpl; auto.
    Qed.

    Let ra_rem_val_0 n m : m <> 0 -> ⟦ra_rem⟧ (n##m##vec_nil) (n-m*div n m).
    Proof.
      intros Hm.
      simpl; exists (n##m*div n m##vec_nil); split.
      + apply ra_minus_val.
      + intro p; analyse pos p.
        { cbv; auto. }
        { simpl; exists (m##div n m##vec_nil); split.
          * apply ra_mult_val.
          * intros p; analyse pos p.
            { cbv; auto. }  
            { apply ra_div_val; auto. } }
    Qed.

    Fact ra_rem_val n m : m <> 0 -> ⟦ra_rem⟧ (n##m##vec_nil) (rem n m).
    Proof.
      intros Hm.
      generalize (div_rem_spec1 n m) (ra_rem_val_0 n Hm); intros.
      replace (rem n m) with (n-m*div n m); auto.
      rewrite mult_comm; omega.
    Qed.

    Fact ra_rem_rel v e : vec_pos v pos1 <> 0 -> ⟦ra_rem⟧ v e <-> e = rem (vec_pos v pos0) (vec_pos v pos1).
    Proof.
      vec split v with a; vec split v with b; vec nil v; intros H0.
      split.
      + intros H; apply ra_rel_fun with (1 := H), ra_rem_val; auto.
      + intros; subst; apply ra_rem_val; auto.
    Qed.

  End ra_rem.

  Hint Resolve ra_rem_prim.
 
  Opaque ra_rem.

  Definition ra_div2 : recalg 1.
  Proof.
    apply ra_comp with (1 := ra_div); refine (_##_##vec_nil).
    + apply (ra_proj pos0).
    + apply ra_cst_n, 2.
  Defined.

  Fact ra_div2_prim : prim_rec ra_div2.
  Proof. 
     simpl; split; auto. 
     intros p; analyse pos p; simpl; auto. 
  Qed.

  Fact ra_div2_val n : ⟦ra_div2⟧ (n##vec_nil) (div n 2).
  Proof.
    exists (n##2##vec_nil); split.
    + apply ra_div_val; discriminate.
    + intros p; analyse pos p; simpl.
    unfold ra_div2; simpl; cbv; auto.
    apply ra_cst_n_val.
  Qed.

  Definition ra_mod2 : recalg 1.
  Proof.
    apply ra_comp with (1 := ra_rem); refine (_##_##vec_nil).
    + apply (ra_proj pos0).
    + apply ra_cst_n, 2.
  Defined.

  Fact ra_mod2_prim : prim_rec ra_mod2.
  Proof. 
     simpl; split; auto. 
     intros p; analyse pos p; simpl; auto. 
  Qed.

  Fact ra_mod2_val n : ⟦ra_mod2⟧ (n##vec_nil) (rem n 2).
  Proof.
    exists (n##2##vec_nil); split.
    + apply ra_rem_val; discriminate.
    + intros p; analyse pos p; simpl.
      * cbv; auto.
      * apply ra_cst_n_val.
  Qed.

  Definition ra_pow2 : recalg 1.
  Proof.
    apply ra_comp with (1 := ra_exp).
    refine (_##_##vec_nil).
    + apply ra_proj, pos0.
    + apply ra_cst_n, 2.
  Defined.

  Fact ra_pow2_prim : prim_rec ra_pow2.
  Proof. 
     simpl; split; auto. 
     intros p; analyse pos p; simpl; auto. 
  Qed.

  Fact ra_pow2_val n : ⟦ra_pow2⟧ (n##vec_nil) (power n 2).
  Proof.
     exists (n##2##vec_nil); split.
    + apply ra_exp_val; discriminate.
    + intros p; analyse pos p; simpl.
      * cbv; auto.
      * apply ra_cst_n_val.
  Qed.
  
  Hint Resolve ra_div2_prim ra_mod2_prim ra_pow2_prim.

  Opaque ra_div2 ra_mod2 ra_pow2.

  Section ra_notdiv_pow2.

    (* f n m = 0 if 2^n does not divides m and <> 0 is 2^n divides m *)

    Definition notdiv_pow2 n m := ite_rel (rem m (power n 2)) 1 0.

    Fact notdiv_pow2_spec_1 n m : notdiv_pow2 n m <> 0 <-> divides (power n 2) m.
    Proof.
      unfold notdiv_pow2.
      generalize (power n 2); clear n; intros n.
      unfold ite_rel; case_eq (rem m n).
      * intros H; split; try discriminate; intros _.
        exists (div m n).
        generalize (div_rem_spec1 m n); omega.
      * intros k Hk; split; try omega; intros H _.
        apply divides_rem_eq in H; omega.
    Qed.

    Fact notdiv_pow2_spec_2 n m : notdiv_pow2 n m = 0 <-> ~ divides (power n 2) m.
    Proof.
      rewrite <- notdiv_pow2_spec_1; omega.
    Qed.

    Definition ra_notdiv_pow2 : recalg 2.
    Proof.
      apply ra_comp with (1 := ra_ite).
      refine (_##_##_##vec_nil).
      + apply ra_comp with (1 := ra_rem).
        refine (_##_##vec_nil).
        * apply ra_proj, pos1.
        * apply ra_comp with (1 := ra_pow2).
          apply (ra_proj pos0##vec_nil).
      + apply ra_cst_n, 1.
      + apply ra_cst_n, 0.
    Defined.

    Fact ra_notdiv_pow2_prim : prim_rec ra_notdiv_pow2.
    Proof.
      simpl; split; auto.
      repeat (intros p; analyse pos p; simpl; split; auto).
    Qed.
   
    Fact ra_notdiv_pow2_val n m : ⟦ra_notdiv_pow2⟧ (n##m##vec_nil) (notdiv_pow2 n m).
    Proof.
      simpl.
      exists (rem m (power n 2)##1##0##vec_nil); split.
      + apply ra_ite_val.
      + intros p; analyse pos p.
        * exists (m##power n 2##vec_nil); split.
          - apply ra_rem_val; generalize (@power_ge_1 n 2); intros; omega.
          - intros p; analyse pos p.
            ++ cbv; auto.
            ++ exists (n##vec_nil); split.
               ** apply ra_pow2_val.
               ** intros p; analyse pos p; cbv; auto.
        * apply ra_cst_n_val.
        * apply ra_cst_n_val.
    Qed.

  End ra_notdiv_pow2.

  Hint Resolve ra_notdiv_pow2_prim.

  Opaque ra_notdiv_pow2.

  Section ra_decomp.

    (* given n, find a such that S n = 2^a*(2*b+1) 
       to get a bijection nat -> nat * nat *)

    (* first, given n, find the first a such that 2^(S a) does not divide S n *)

    Definition ra_decomp_l : recalg 1.
    Proof.
      apply ra_comp with 2.
      + apply ra_prim_min.
        apply ra_comp with (1 := ra_notdiv_pow2).
        refine (_##_##vec_nil).
        * apply ra_comp with (1 := ra_succ), (ra_proj pos0##vec_nil).
        * apply ra_proj, pos1.
      + refine (_##_##vec_nil);
        apply ra_comp with (1 := ra_succ), (ra_proj pos0##vec_nil).
    Defined.

    Fact ra_decomp_l_prim : prim_rec ra_decomp_l.
    Proof.
      simpl; split; auto.
      + apply ra_prim_min_prim; simpl; split; auto.
        repeat (intros p; analyse pos p; simpl; split; auto).
      + repeat (intros p; analyse pos p; simpl; split; auto).
    Qed.

    Fact ra_decomp_l_val_0 n : ⟦ra_decomp_l⟧ (n##vec_nil) (prim_min (fun i => notdiv_pow2 (S i) (S n)) (S n)).
    Proof.
      simpl.
      exists (S n##S n##vec_nil); split.
      + apply ra_prim_min_val with (f := fun v i => notdiv_pow2 (S i) (vec_head v)).
        intros i v; vec split v with j; vec nil v.
        exists (S i##j##vec_nil); split.
        * apply ra_notdiv_pow2_val.
        * intros p; analyse pos p.
          - simpl; exists (i##vec_nil); split; try (cbv; auto; fail).
            intros p; analyse pos p; cbv; auto.
          - cbv; auto.
      + intros p; analyse pos p.
        * exists (n##vec_nil); split.
          - cbv; auto.
          - intros p; analyse pos p; cbv; auto.
        * exists (n##vec_nil); split.
          - cbv; auto.
          - intros p; analyse pos p; cbv; auto.
    Qed.
 
    Fact ra_decomp_l_rel n : { a | ⟦ra_decomp_l⟧ (n##vec_nil) a /\ divides (power a 2) (S n) /\ ~ divides (power (S a) 2) (S n) }.
    Proof.
      exists (prim_min (fun i => notdiv_pow2 (S i) (S n)) (S n)); split.
      1: apply ra_decomp_l_val_0.
      generalize (prim_min_spec (fun i => notdiv_pow2 (S i) (S n)) (S n)); intros H.
      destruct H as (H1 & H2).
      { apply notdiv_pow2_spec_2; intros C.
        apply divides_le in C; try discriminate.
        generalize (@power_ge_n (S (S n)) 2); intros; omega. }
      apply notdiv_pow2_spec_2 in H1; split; auto.
      revert H2; generalize (prim_min (fun i : nat => notdiv_pow2 (S i) (S n)) (S n)); intros [ | k ] Hk.
      + rewrite power_0; apply divides_1.
      + apply notdiv_pow2_spec_1, Hk; omega.
    Qed.

    Hint Resolve ra_decomp_l_prim.

    Opaque ra_decomp_l.

    Definition ra_decomp_r : recalg 1.
    Proof.
      apply ra_comp with (1 := ra_div).
      refine (_##_##vec_nil).
      + apply ra_comp with (1 := ra_succ), (ra_proj pos0##vec_nil).
      + apply ra_comp with (1 := ra_pow2); refine (_##vec_nil).
        apply ra_comp with (1 := ra_succ); refine (_##vec_nil).
        apply ra_comp with (1 := ra_decomp_l), (ra_proj pos0##vec_nil).
    Defined.

    Fact ra_decomp_r_prim : prim_rec ra_decomp_r.
    Proof. 
      simpl; split; auto.
      repeat (intros p; analyse pos p; simpl; split; auto).
    Qed.
     
    Fact ra_decomp_r_rel n : { b | ⟦ra_decomp_r⟧ (n##vec_nil) b /\ exists a, ⟦ra_decomp_l⟧ (n##vec_nil) a /\ S n = power a 2 * (2*b+1) }.
    Proof.
      destruct (ra_decomp_l_rel n) as (a & H1 & H2 & H3).
      exists (div (S n) (power (S a) 2)); split.
      + exists (S n##power (S a) 2##vec_nil); split.
        { apply ra_div_val; generalize (@power_ge_1 (S a) 2); intros; omega. }
        intros p; analyse pos p; repeat rewrite vec_pos_set; simpl.
        * exists (n##vec_nil); split; try (cbv; auto; fail).
          intros p; analyse pos p; cbv; auto.
        * exists (S a##vec_nil); split.
          { apply ra_pow2_val. }
          intros p; analyse pos p; simpl.
          exists (a##vec_nil); split.
          { cbv; auto. }
          intros p; analyse pos p; simpl.
          exists (n##vec_nil); split; auto.
          intros p; analyse pos p; cbv; auto.
      + exists a; split; auto.
        generalize (div_rem_spec1 (S n) (power a 2)).
        apply divides_rem_eq in H2; rewrite H2, Nat.add_0_r.
        rewrite power_S in *.
        clear H1.
        revert H2 H3.
        generalize (S n) (power a 2) (power2_gt_0 a); clear n a; intros n p H1 H2 H3 H4.
        rewrite H4 at 1; rewrite mult_comm; f_equal.
        rewrite divides_rem_eq in H3.
        rewrite (mult_comm _ p), div_mult; try omega.
        rewrite mult_comm, rem_mult in H3; try omega.
        rewrite (@div_rem_spec1 (div n p) 2) at 1.
        rewrite H2 in H3; simpl in H3.
        generalize (@div_rem_spec2 (div n p) 2); intros H5.
        rewrite mult_comm in H3.
        destruct (rem (div n p) 2) as [ | [ | ] ]; omega.
    Qed.

    Fact ra_decomp_lr_val n : ⟦ra_decomp_l⟧ (n##vec_nil) (decomp_l n) /\ ⟦ra_decomp_r⟧ (n##vec_nil) (decomp_r n).
    Proof.
      destruct (ra_decomp_r_rel n) as (b & H1 & a & H2 & H3).
      rewrite (decomp_lr_spec n) in H3.
      apply decomp_uniq in H3; destruct H3; subst a b; auto.
    Qed.

    Fact ra_decomp_l_val n : ⟦ra_decomp_l⟧ (n##vec_nil) (decomp_l n).
    Proof. apply ra_decomp_lr_val. Qed.

    Fact ra_decomp_r_val n : ⟦ra_decomp_r⟧ (n##vec_nil) (decomp_r n).
    Proof. apply ra_decomp_lr_val. Qed.

  End ra_decomp.

  Hint Resolve ra_decomp_l_prim ra_decomp_r_prim.

  Definition ra_recomp : recalg 2.
  Proof.
    apply ra_comp with (1 := ra_pred); refine (_##vec_nil).
    apply ra_comp with (1 := ra_mult); refine (_##_##vec_nil).
    + apply ra_comp with (1 := ra_pow2), (ra_proj pos0##vec_nil).
    + apply ra_comp with (1 := ra_succ); refine (_##vec_nil).
      apply ra_comp with (1 := ra_mult); refine (_##_##vec_nil).
      * apply ra_cst_n, 2.
      * apply ra_proj, pos1.
  Defined.

  Fact ra_recomp_prim : prim_rec ra_recomp.
  Proof.
    simpl; split; auto.
    repeat (intros p; analyse pos p; simpl; split; auto).
  Qed.
  
  Fact ra_recomp_val a b : ⟦ra_recomp⟧ (a##b##vec_nil) (recomp a b).
  Proof.
    unfold recomp.
    rewrite plus_comm.
    exists (power a 2 * (S (2*b)) ## vec_nil); split.
    { apply ra_pred_val. }
    intros p; analyse pos p; simpl.
    exists (power a 2##S (2*b)##vec_nil); split.
    { apply ra_mult_val. }
    intros p; analyse pos p; simpl.
    * exists (a##vec_nil); split. 
      { apply ra_pow2_val. }
      intros p; analyse pos p; cbv; auto.
    * exists (2*b##vec_nil); split.
      { reflexivity. }
      intros p; analyse pos p; simpl.
      exists (2##b##vec_nil); split.
      { apply ra_mult_val. }
      intros p; analyse pos p; simpl.
      - apply ra_cst_n_val.
      - cbv; auto.
  Qed.

  Hint Resolve ra_recomp_prim.

  Opaque ra_decomp_l ra_decomp_r ra_recomp.

  Section ra_godel_beta.

    Definition ra_godel_beta : recalg 3.
    Proof.
      apply ra_comp with (1 := ra_rem).
      refine (_##_##vec_nil).
      + apply (ra_proj pos0).
      + apply ra_comp with (1 := ra_succ).
        refine (_##vec_nil).
        * apply ra_comp with (1 := ra_mult).
          refine (_##_##vec_nil).
          - apply ra_comp with (1 := ra_succ).
            refine (_##vec_nil).
            apply (ra_proj pos2).
          - apply (ra_proj pos1).
    Defined.

    Fact ra_godel_beta_prim : prim_rec ra_godel_beta.
    Proof.
      simpl; split; auto.
      repeat (intros p; analyse pos p; simpl; split; auto).
    Qed.
 
    Fact ra_godel_beta_val a b n : ⟦ra_godel_beta⟧ (a##b##n##vec_nil) (godel_beta a b n).
    Proof.
      simpl.
      exists (a##S ((S n)*b)##vec_nil); split.
      + apply ra_rem_val; discriminate.
      + intro p; analyse pos p; simpl.
        { cbv; auto. }
        exists (((S n)*b)##vec_nil); split.
        { red; simpl; auto. }
        intro p; analyse pos p; simpl.
        exists (S n##b##vec_nil); split.
        { apply ra_mult_val. }
        intro p; analyse pos p; simpl.
        * exists (n##vec_nil); split.
          { cbv; auto. }
          intro p; analyse pos p; simpl.
          cbv; auto.
        * cbv; auto.
    Qed.

    Fact ra_godel_beta_rel v e : ⟦ra_godel_beta⟧ v e <-> e = godel_beta (vec_pos v pos0) (vec_pos v pos1) (vec_pos v pos2).
    Proof.
      vec split v with a; vec split v with b; vec split v with n; vec nil v.
      split.
      + intros H; apply ra_rel_fun with (1 := H), ra_godel_beta_val; auto.
      + intros; subst; apply ra_godel_beta_val; auto.
    Qed.

  End ra_godel_beta.

  Hint Resolve ra_godel_beta_prim.
 
  Opaque ra_godel_beta.

  Definition beta a n := godel_beta (decomp_l a) (decomp_r a) n.

  (** beta can enumerate ANY vector of ANY length by wisely choosing
      the parameter a *)

  Lemma beta_inv n (v : vec _ n) : { a | forall p, beta a (pos2nat p) = vec_pos v p }.
  Proof.
    destruct (godel_beta_inv v) as (a & b & H).
    exists (recomp a b); intro p; unfold beta.
    rewrite decomp_l_recomp, decomp_r_recomp; auto.
  Qed.

  Lemma beta_fun_inv n f : { a | forall p, p < n -> f p = beta a p }.
  Proof.
    destruct beta_inv with (v := vec_set_pos (fun p : pos n => f (pos2nat p)))
      as (a & Ha).
    exists a; intros p Hp.
    specialize (Ha (nat2pos Hp)).
    rewrite vec_pos_set, pos2nat_nat2pos in Ha.
    auto.
  Qed.

  Section ra_beta.

    Definition ra_beta : recalg 2.
    Proof.
      apply ra_comp with (1 := ra_godel_beta).
      refine (_##_##_##vec_nil).
      + apply ra_comp with (1 := ra_decomp_l).
        refine (_##vec_nil).
        apply (ra_proj pos0).
      + apply ra_comp with (1 := ra_decomp_r).
        refine (_##vec_nil).
        apply (ra_proj pos0).
      + apply (ra_proj pos1).
    Defined.

    Fact ra_beta_prim : prim_rec ra_beta.
    Proof.
      simpl; split; auto.
      repeat (intros p; analyse pos p; simpl; split; auto).
    Qed.

    Fact ra_beta_val a n : ⟦ra_beta⟧ (a##n##vec_nil) (beta a n).
    Proof.
      simpl.
      exists (decomp_l a##decomp_r a##n##vec_nil); split.
      { apply ra_godel_beta_val. }
      intro p; analyse pos p; simpl.
      + exists (a##vec_nil); split.
        { apply ra_decomp_l_val. }
        intro p; analyse pos p; cbv; auto.
      + exists (a##vec_nil); split.
        { apply ra_decomp_r_val. }
        intro p; analyse pos p; cbv; auto.
      + cbv; auto.
    Qed.

    Fact ra_beta_rel v e : ⟦ra_beta⟧ v e <-> e = beta (vec_pos v pos0) (vec_pos v pos1).
    Proof.
      vec split v with a; vec split v with n; vec nil v.
      split.
      + intros H; apply ra_rel_fun with (1 := H), ra_beta_val; auto.
      + intros; subst; apply ra_beta_val; auto.
    Qed.

  End ra_beta.

  Hint Resolve ra_beta_prim.
 
  Opaque ra_beta.

  Fixpoint inject n (v : vec nat n) : nat :=
    match v with
      | vec_nil => 0
      | x##v    => recomp x (inject v)
    end.

  Fixpoint project n : nat -> vec nat n :=
    match n with
      | 0   => fun _ => vec_nil
      | S n => fun x => decomp_l x ## project _ (decomp_r x)
    end.

  Fact project_inject n v : project _ (@inject n v) = v.
  Proof.
    induction v as [ | n x v IHv ]; simpl; auto.
    rewrite decomp_l_recomp, decomp_r_recomp; f_equal; trivial.
  Qed. 

  Fixpoint ra_inject n : recalg n.
  Proof.
    destruct n as [ | n ].
    + apply ra_cst, 0.
    + apply ra_comp with (1 := ra_recomp).
      refine (_##_##vec_nil).
      * apply ra_proj, pos0.
      * apply ra_comp with (1 := ra_inject n).
        apply vec_set_pos.
        intros p; apply ra_proj, pos_nxt, p.
  Defined.

  Fact ra_inject_prim n : prim_rec (ra_inject n).
  Proof.
    induction n as [ | n IHn ]; simpl; split; auto.
    intros p; analyse pos p; simpl; split; auto.
    intros p; rewrite vec_pos_set; simpl; auto.
  Qed.

  Fact ra_inject_val n v : ⟦ra_inject n⟧ v (inject v).
  Proof.
    induction n as [ | n IHn ]; simpl.
    + vec nil v; cbv; auto.
    + vec split v with x.
      exists (x##inject v##vec_nil); split.
      * apply ra_recomp_val.
      * intros p; analyse pos p; simpl.
        - cbv; auto.
        - exists v; split; auto.
          intros p; repeat rewrite vec_pos_set.
          simpl; red; auto.
  Qed.

  Fixpoint ra_project n (p : pos n) : recalg 1 :=
    match p with
      | pos_fst   => ra_decomp_l
      | pos_nxt p => ra_comp (ra_project p) (ra_decomp_r##vec_nil)
    end.

  Fact ra_project_prim n p : prim_rec (@ra_project n p).
  Proof.
    induction p as [ | n p IHp ]; simpl; auto; split; auto.
    intros j; analyse pos j; simpl; auto.
  Qed. 

  Fact ra_project_val n p x : ⟦@ra_project n p⟧ (x##vec_nil) (vec_pos (@project n x) p).
  Proof.
    revert x; induction p as [ | n p IHp ]; intros x; simpl.
    + apply ra_decomp_l_val.
    + exists (decomp_r x##vec_nil); split.
      * apply IHp.
      * intros q; analyse pos q; simpl.
        apply ra_decomp_r_val.
  Qed.

  Fact ra_project_rel n p v x : ⟦@ra_project n p⟧ v x <-> x = vec_pos (@project n (vec_head v)) p.
  Proof.
    vec split v with a; vec nil v.
    split.
    + intros H; apply ra_rel_fun with (1 := H), ra_project_val.
    + intros; subst; apply ra_project_val.
  Qed.

  Definition ra_vec_project n : vec (recalg 1) n.
  Proof. apply vec_set_pos, ra_project. Defined. 

End utils.

(* Now we have inject/project implemented as primitive recursive algorithms *)

Opaque ra_cst_n ra_pred ra_plus ra_minus ra_mult ra_ite
       ra_div ra_rem ra_div2 ra_mod2 ra_pow2 ra_notdiv_pow2
       ra_decomp_l ra_decomp_l ra_decomp_r ra_recomp
       ra_godel_beta ra_beta
       ra_inject ra_project.

Hint Resolve ra_cst_n_prim ra_iter_n_prim ra_iter_prim
             ra_pred_prim ra_plus_prim ra_minus_prim
             ra_mult_prim ra_exp_prim ra_ite_prim
             ra_eq_prim ra_prim_min_prim ra_prim_max_prim
             ra_div_prim ra_rem_prim ra_div2_prim ra_mod2_prim 
             ra_pow2_prim ra_notdiv_pow2_prim
             ra_decomp_l_prim ra_decomp_r_prim ra_recomp_prim
             ra_godel_beta_prim ra_beta_prim
             ra_project_prim ra_inject_prim.
