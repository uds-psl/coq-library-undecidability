(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith List Lia.

From Undecidability.Shared.Libs.DLW 
  Require Import utils_tac utils_nat utils_list gcd crt sums finite pos vec.

From Undecidability.MuRec 
  Require Import recalg recomp prim_min.

Set Implicit Arguments.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

Local Notation power := (mscal mult 1).

Ltac fill_vec := 
  match goal with 
    | |- vec _ O     => apply vec_nil
    | |- vec _ (S _) => refine (_##_); [ | try fill_vec ]
  end.

Tactic Notation "ra" "root" uconstr(f) := 
  apply ra_comp with (1 := f); fill_vec.

Tactic Notation "ra" "arg" uconstr(f) :=
  apply (ra_proj f).

Fact ra_cst_val k v : ⟦ra_cst k⟧ v k.
Proof. reflexivity. Qed. 

Fact ra_proj_val n (v : vec nat n) p : ⟦ra_proj p⟧ v (vec_pos v p).
Proof. reflexivity. Qed.

Hint Resolve ra_cst_val ra_proj_val : core.

Tactic Notation "pos" "split" := let p := fresh in intro p; analyse pos p.

Ltac prim_rec_tac :=
  repeat (simpl; match goal with 
    | |- True   => exact I
    | |- _ /\ _ => split
    | |- forall _ : pos _, _ => pos split
  end; auto; try rewrite vec_pos_set; auto).

Tactic Notation "ra" "prim" "rec" := prim_rec_tac.

Section ra_cst_n.

  Definition ra_cst_n n x : recalg n := ra_comp (ra_cst x) vec_nil.

  Fact ra_cst_n_prim n x : prim_rec (ra_cst_n n x).
  Proof. apply prim_rec_bool_spec; reflexivity. Qed. 

  Fact ra_cst_n_val n x v : ⟦ra_cst_n n x⟧ v x.
  Proof.
    exists vec_nil; split; auto.
    pos split.
  Qed.

  Fact ra_cst_n_rel n x v e : ⟦ra_cst_n n x⟧ v e <-> e = x.
  Proof.
    split.
    + intros H; apply ra_rel_fun with (1 := H), ra_cst_n_val.
    + intro; subst; apply ra_cst_n_val.
  Qed.

End ra_cst_n.

Opaque ra_cst_n.
Hint Resolve ra_cst_n_prim ra_cst_n_val : core.

Tactic Notation "ra" "cst" constr(f) := apply (ra_cst_n _ f).

Tactic Notation "vec" "pos" "simpl" := simpl; repeat rewrite vec_pos_set; simpl; auto.

Local Fact eq_equiv X (e a b : X) : a = b -> (e = a <-> e = b).
Proof. intros []; tauto. Qed.

(* We start with primitive recursive iterators *)

Section ra_iter_n.

  Variable (n : nat) (f : vec nat n -> nat) (af : recalg n) 
                     (Hf : forall v, ⟦af⟧ v (f v))
                     (Haf : prim_rec af)
                     (g : vec nat n -> nat -> nat) (ag : recalg (S n)) 
                     (Hg : forall i v, ⟦ag⟧ (i##v) (g v i))
                     (Hag : prim_rec ag).

  Definition ra_iter_n : recalg (S n).
  Proof.
    apply (ra_rec af).
    apply ra_comp with (1 := ag).
    apply vec_set_pos; intros p.
    apply (ra_proj (pos_nxt p)).
  Defined.

  Fact ra_iter_n_prim_rec : prim_rec ra_iter_n.
  Proof. ra prim rec. Qed.

  Fact ra_iter_n_val i v : ⟦ra_iter_n⟧ (i##v) (iter (g v) i (f v)).
  Proof.
    simpl; unfold s_rec.
    induction i as [ | i IHi ]; simpl; auto.
    exists (iter (g v) i (f v)); split; auto.
    exists (iter (g v) i (f v)## v); split; auto.
    intros p; analyse_pos p; simpl; auto.
    vec pos simpl.
  Qed.

  Fact ra_iter_n_rel v e : ⟦ra_iter_n⟧ v e <-> e = iter (g (vec_tail v)) (vec_pos v pos0) (f (vec_tail v)).
  Proof.
    vec split v with i; split.
    + intros H; apply ra_rel_fun with (1 := H), ra_iter_n_val.
    + intros; subst; apply ra_iter_n_val.
  Qed.
      
End ra_iter_n.

Opaque ra_iter_n.
Hint Resolve ra_iter_n_prim_rec ra_iter_n_val : core.

Section ra_iter.

  Variable (n : nat) (f : nat -> nat) (af : recalg 1) 
           (Hf : forall v e, ⟦af⟧ v e <-> e = f (vec_head v))
           (Haf : prim_rec af).

  Definition ra_iter : recalg 2.
  Proof.
    apply ra_iter_n.
    + ra arg pos0.
    + ra root af.
      ra arg pos0.
  Defined. 

  Fact ra_iter_prim_rec : prim_rec ra_iter.
  Proof.
    apply ra_iter_n_prim_rec; ra prim rec.
  Qed.

  Fact ra_iter_val k x : ⟦ra_iter⟧ (k##x##vec_nil) (iter f k x).
  Proof.
    unfold ra_iter.
    rewrite ra_iter_n_rel with (f := @vec_head _ _) (g := fun _ => f); simpl; auto.
    + intros v; vec split v with y; vec nil v; auto.
    + intros i v; vec split v with y; vec nil v; simpl; auto.
      exists (i##vec_nil); split; auto.
      * rewrite Hf; auto.
      * pos split; simpl; auto.
  Qed.

  Fact ra_iter_rel v e : ⟦ra_iter⟧ v e <-> e = iter f (vec_pos v pos0) (vec_pos v pos1).
  Proof.
    vec split v with k; vec split v with x; vec nil v.
    split.
    + intros H; apply ra_rel_fun with (1 := H), ra_iter_val.
    + intros ->; apply ra_iter_val.
  Qed.

End ra_iter.

Opaque ra_iter.
Hint Resolve ra_iter_prim_rec ra_iter_val : core.

(* Then basic arithmetic -1, +, -, *, exp *)

Section ra_pred_plus.

  Definition ra_pred := ra_rec (ra_cst 0) (ra_proj pos0).

  Fact ra_pred_prim_rec : prim_rec ra_pred.
  Proof. apply prim_rec_bool_spec; auto. Qed.

  Fact ra_pred_val n : ⟦ra_pred⟧ (n##vec_nil) (n-1).
  Proof.
    simpl; unfold s_rec.
    induction n as [ | n IHn ]; simpl.
    + cbv; trivial.
    + simpl in IHn; exists (n-1); split; auto.
      replace (n-0) with n by lia; cbv; auto.
  Qed.

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

  Fact ra_plus_prim_rec : prim_rec ra_plus.
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

End ra_pred_plus.

Hint Resolve ra_plus_prim_rec ra_pred_prim_rec
             ra_plus_val ra_pred_val : core.
Opaque ra_plus ra_pred.

Section ra_minus_mult.

  Let ra_minus_inv : recalg 2.
  Proof. apply ra_iter, ra_pred. Defined.
 
  Let ra_minus_inv_rel v e : ⟦ra_minus_inv⟧ v e <-> e = vec_pos v pos1 - vec_pos v pos0.
  Proof.
    unfold ra_minus_inv; simpl.
    rewrite ra_iter_rel with (f := pred).
    + vec split v with n; vec split v with m; vec nil v; simpl.
      apply eq_equiv; induction n; simpl; lia.
    + intros; simpl; rewrite ra_pred_rel.
      apply eq_equiv; lia.
  Qed.

  Definition ra_minus : recalg 2.
  Proof.
    ra root ra_minus_inv.
    + ra arg pos1.
    + ra arg pos0.
  Defined.

  Fact ra_minus_prim_rec : prim_rec ra_minus.
  Proof. apply prim_rec_bool_spec; auto. Qed.

  Fact ra_minus_val n m : ⟦ra_minus⟧ (n##m##vec_nil) (n-m).
  Proof.
    exists (m##n##vec_nil); split; auto.
    + rewrite ra_minus_inv_rel; simpl; auto.
    + pos split; simpl; auto.
  Qed.

  Fact ra_minus_rel v e : ⟦ra_minus⟧ v e <-> e = vec_pos v pos0 - vec_pos v pos1.
  Proof.
    vec split v with n; vec split v with m; vec nil v.
    split.
    + intros H; apply ra_rel_fun with (1 := H), ra_minus_val.
    + intros; subst; apply ra_minus_val.
  Qed.

  Definition ra_mult : recalg 2.
  Proof.
    apply ra_rec.
    + apply ra_zero.
    + ra root ra_plus.
      ra arg pos1.
      ra arg pos2.
  Defined.

  Fact ra_mult_prim_rec : prim_rec ra_mult.
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

  Fact ra_mult_rel v e : ⟦ra_mult⟧ v e <-> e = vec_head v * vec_head (vec_tail v).
  Proof.
    vec split v with n; vec split v with m; vec nil v.
    split.
    + intros H; apply ra_rel_fun with (1 := H), ra_mult_val.
    + intros; subst; apply ra_mult_val.
  Qed.

End ra_minus_mult.

Hint Resolve ra_minus_prim_rec ra_mult_prim_rec
             ra_minus_val ra_mult_val : core.
Opaque ra_minus ra_mult.

Section ra_exp.

  Definition ra_exp : recalg 2.
  Proof.
    apply ra_iter_n.
    + ra cst 1.
    + ra root ra_mult.
      * ra arg pos1.
      * ra arg pos0.
  Defined.

  Fact ra_exp_prim_rec : prim_rec ra_exp.
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
      exists (j##i##vec_nil); split; auto.
      pos split; simpl; auto.
  Qed.

  Fact ra_exp_rel v e : ⟦ra_exp⟧ v e <-> e = power (vec_pos v pos0) (vec_pos v pos1).
  Proof.
    vec split v with n; vec split v with m; vec nil v.
    split.
    + intros H; apply ra_rel_fun with (1 := H), ra_exp_val.
    + intros; subst; apply ra_exp_val.
  Qed.

End ra_exp.

Hint Resolve ra_exp_prim_rec ra_exp_val : core.
Opaque ra_exp.

(* The Boolean/branch operators *)

(* if b=0 then p else q *)

Definition ite_rel (b p q : nat) := match b with 0 => p | _ => q end.

Section ra_ite.

  Definition ra_ite : recalg 3.
  Proof.
    apply ra_rec.
    + ra arg pos0.
    + ra arg pos3.
  Defined.

  Fact ra_ite_prim_rec : prim_rec ra_ite.
  Proof. apply prim_rec_bool_spec; auto. Qed.

  Fact ra_ite_val b p q : ⟦ra_ite⟧ (b##p##q##vec_nil) (ite_rel b p q).
  Proof.
    simpl; unfold s_rec.
    induction b as [ | b IHb ]; simpl; auto.
    exists (ite_rel b p q); split; auto.
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

End ra_ite.

Hint Resolve ra_ite_prim_rec ra_ite_val : core.
Opaque ra_ite.

Section ra_not.

  Definition ra_not : recalg 1.
  Proof.
    ra root ra_minus.
    ra cst 1.
    ra arg pos0.
  Defined.

  Fact ra_not_prim_rec : prim_rec ra_not.
  Proof. ra prim rec. Qed.

  Fact ra_not_val n : ⟦ra_not⟧ (n##vec_nil) (1-n).
  Proof.
    exists (1##n##vec_nil); split; auto.
    pos split; simpl; auto.
  Qed. 

End ra_not.

Hint Resolve ra_not_prim_rec ra_not_val : core.
Opaque ra_not.

Section ra_eq.

  Definition ra_eq : recalg 2.
  Proof.
    ra root ra_ite.
    + exact ra_minus.
    + ra root ra_minus.
      * ra arg pos1.
      * ra arg pos0.
    + ra cst 1.
  Defined.

  Fact ra_eq_prim_rec : prim_rec ra_eq.
  Proof. apply prim_rec_bool_spec; auto. Qed.

  Fact ra_eq_val a b : ⟦ra_eq⟧ (a##b##vec_nil) (ite_rel (a-b) (b-a) 1).
  Proof.
    exists (a-b##b-a##1##vec_nil); split; auto.
    pos split; vec pos simpl.
    exists (b##a##vec_nil); split; auto.
    pos split; vec pos simpl.
  Qed.

  Fact ra_eq_rel v : { e | ⟦ra_eq⟧ v e /\ (e = 0 <-> vec_pos v pos0 = vec_pos v pos1) }.
  Proof.
    vec split v with a; vec split v with b; vec nil v.
    exists (ite_rel (a-b) (b-a) 1); split.
    + apply ra_eq_val.
    + simpl; unfold ite_rel.
      case_eq (a-b); intros; lia.
  Qed.
 
End ra_eq.

Hint Resolve ra_eq_prim_rec ra_eq_val : core.
Opaque ra_eq.

(* A primitive recursive bounded minimization *)

Section ra_prim_min.

  Variable (n : nat) (f : vec nat n -> nat -> nat) (af : recalg (S n)) 
                     (Hf : forall i v, ⟦af⟧ (i##v) (f v i))
                     (Haf : prim_rec af).

  Let ag : recalg (S n).
  Proof.
    ra root ra_ite.
    + exact af.
    + ra arg pos0.
    + ra root ra_succ.
      ra arg pos0.
  Defined.

  Let ag_pr : prim_rec ag.
  Proof. ra prim rec. Qed.

  Let ag_val i v : ⟦ag⟧ (i##v) (ite_rel (f v i) i (S i)).
  Proof.
    simpl; unfold s_comp.
    exists (f v i##i##S i##vec_nil); split; auto.
    pos split; vec pos simpl.
    exists (i##vec_nil); split; auto.
    pos split; simpl; auto.
  Qed.

  Definition ra_prim_min : recalg (S n).
  Proof.
    apply ra_iter_n.
    + ra cst 0.
    + exact ag.
  Defined.

  Opaque ag.

  Fact ra_prim_min_prim_rec : prim_rec ra_prim_min.
  Proof. apply ra_iter_n_prim_rec; auto. Qed.

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

Hint Resolve ra_prim_min_prim_rec ra_prim_min_val : core.
Opaque ra_prim_min.

(* A primrec function than find i st f i <= b < f (S i) when f is a strictly
    increasing 

    This provides an easy way to invert a primitive recursive function which is 
    strictly increasing *) 

Section ra_prim_max.

  Variable (n : nat) (f : vec nat n -> nat -> nat) (af : recalg (S n)) 
           (Hf : forall a v, ⟦af⟧ (a##v) (f v a))
           (Haf : prim_rec af).
  
  Let ag : recalg (S (S n)).
  Proof.
    ra root ra_minus.
    + ra root ra_succ.
      ra arg pos1.
    + ra root af.
      * ra root ra_succ.
        ra arg pos0.
      * apply vec_set_pos.
        intros p; apply (ra_proj (pos_nxt (pos_nxt p))).
  Defined.

  Let ag_prim : prim_rec ag.
  Proof. ra prim rec. Qed.
 
  Let ag_val a b v : ⟦ag⟧ (a##b##v) ((S b) - f v (S a)).
  Proof.
    exists (S b##f v (S a)##vec_nil); split; auto.
    pos split; vec pos simpl.
    + exists (b##vec_nil); split; simpl; auto.
      pos split; simpl; auto.
    + exists (S a##v); split; simpl; auto.
      pos split; vec pos simpl.
      exists (a##vec_nil); split; simpl; auto.
      pos split; simpl; auto.
  Qed.

  Opaque ag.

  Definition ra_prim_max : recalg (S (S n)).
  Proof. apply ra_prim_min, ag. Defined.

  Fact ra_prim_max_prim_rec : prim_rec ra_prim_max.
  Proof. apply ra_prim_min_prim_rec; auto. Qed.

  Variables (a b : nat) (v : vec nat n) 
            (Hf2 : forall n, f v n <= f v (S n))
            (Hb : f v 0 <= b < f v (S a)).

  Fact ra_prim_max_spec : { e | ⟦ra_prim_max⟧ (a##b##v) e /\ f v e <= b /\ b < f v (S e) }.
  Proof.
    exists (prim_min (fun i => S b - f v (S i)) a); split.
    + unfold ra_prim_max.
      rewrite ra_prim_min_rel with (f := fun w i => S (vec_head w) - f (vec_tail w) (S i)); auto.
      intros i w; vec split w with j; simpl vec_tail; simpl vec_head; auto.
    + destruct prim_min_spec with (f := fun i => S b - f v (S i)) (n := a)
        as (H2 & H3); try lia.
      split; try lia.
      revert H3.
      destruct (prim_min (fun j => S b - f v (S j)) a) as [ | k ]; intros H3; try lia.
      specialize (H3 k); lia.
  Qed.

End ra_prim_max.

Hint Resolve ra_prim_max_prim_rec : core.
Opaque ra_prim_max.

(* Hence we can implement division as the inverse of multiplication *)

Section ra_div.

  Let f (v : vec nat 1) k := (vec_head v)*k.

  Let af : recalg 2.
  Proof.
    ra root ra_mult.
    + ra arg pos1.
    + ra arg pos0.
  Defined.

  Let af_prim : prim_rec af.
  Proof. apply prim_rec_bool_spec; auto. Qed.

  Let af_val k v : ⟦af⟧ (k##v) (f v k).
  Proof.
    vec split v with b. 
    exists (b##k##vec_nil); split; auto.
    + apply ra_mult_val.
    + pos split; simpl; auto.
  Qed.

  Definition ra_div : recalg 2.
  Proof.
    ra root (ra_prim_max af).
    + ra arg pos0.
    + ra arg pos0.
    + ra arg pos1.
  Defined.

  Fact ra_div_prim_rec : prim_rec ra_div.
  Proof. ra prim rec. Qed. 

  Let ra_div_spec n m : m <> 0 -> { k | ⟦ra_div⟧ (n##m##vec_nil) k /\ m*k <= n < m*(S k) }.
  Proof.
    unfold ra_div; intros Hm.
    destruct ra_prim_max_spec with (f := f) (af := af) (a := n) (b := n) (v := m##vec_nil)
      as (k & H1 & H2); auto.
    { unfold f; simpl; rewrite Nat.mul_0_r; split; try lia.
      apply le_trans with (1*S n); try lia.
      apply mult_le_compat; lia. }
    exists k; split; auto.
    exists (n##n##m##vec_nil); split; auto.
    pos split; simpl; auto.
  Qed.

  Fact ra_div_val n m : m <> 0 -> ⟦ra_div⟧ (n##m##vec_nil) (div n m).
  Proof.
    intros Hm.
    generalize (div_rem_spec1 n m) (div_rem_spec2 n Hm); intros H1 H2.
    destruct (ra_div_spec n Hm) as (k & H3 & H4).
    assert (k = div n m); try lia; subst; auto.
    clear H3.
    rewrite Nat.mul_succ_r in H4.
    apply (@div_rem_uniq _ k (n-m*k) (div n m) (rem n m) Hm); try lia.
  Qed.

  Fact ra_div_rel v e : vec_pos v pos1 <> 0 -> ⟦ra_div⟧ v e <-> e = div (vec_pos v pos0) (vec_pos v pos1).
  Proof.
    vec split v with a; vec split v with b; vec nil v; intros H.
    split.
    + intros H1; apply ra_rel_fun with (1 := H1), ra_div_val; auto.
    + intros; subst; apply ra_div_val; auto.
  Qed.

End ra_div.

Hint Resolve ra_div_prim_rec ra_div_val : core.
Opaque ra_div.

(* And then the remainder using division and multiplication *)

Section ra_rem.

  Definition ra_rem : recalg 2.
  Proof.
    ra root ra_minus.
    + ra arg pos0.
    + ra root ra_mult.
      * ra arg pos1.
      * exact ra_div.
  Defined.

  Fact ra_rem_prim_rec : prim_rec ra_rem.
  Proof. ra prim rec. Qed.

  Let ra_rem_val_0 n m : m <> 0 -> ⟦ra_rem⟧ (n##m##vec_nil) (n-m*div n m).
  Proof.
    intros Hm.
    simpl; exists (n##m*div n m##vec_nil); split; auto.
    pos split; simpl; auto.
    exists (m##div n m##vec_nil); split; auto.
    pos split; simpl; auto.
  Qed.

  Fact ra_rem_val n m : m <> 0 -> ⟦ra_rem⟧ (n##m##vec_nil) (rem n m).
  Proof.
    intros Hm.
    generalize (div_rem_spec1 n m) (ra_rem_val_0 n Hm); intros.
    replace (rem n m) with (n-m*div n m); auto.
    rewrite mult_comm; lia.
  Qed.

  Fact ra_rem_rel v e : vec_pos v pos1 <> 0 -> ⟦ra_rem⟧ v e <-> e = rem (vec_pos v pos0) (vec_pos v pos1).
  Proof.
    vec split v with a; vec split v with b; vec nil v; intros H0.
    split.
    + intros H; apply ra_rel_fun with (1 := H), ra_rem_val; auto.
    + intros; subst; apply ra_rem_val; auto.
  Qed.

End ra_rem.

Hint Resolve ra_rem_prim_rec ra_rem_val : core.
Opaque ra_rem.

(* Now we specialize to binary ops *)

Section ra_binary_ops.

  Definition ra_div2 : recalg 1.
  Proof.
    ra root ra_div.
    + ra arg pos0.
    + ra cst 2.
  Defined.

  Fact ra_div2_prim_rec : prim_rec ra_div2.
  Proof. ra prim rec. Qed. 

  Fact ra_div2_val n : ⟦ra_div2⟧ (n##vec_nil) (div n 2).
  Proof.
    exists (n##2##vec_nil); split.
    + apply ra_div_val; discriminate.
    + pos split; simpl; auto.
  Qed.

  Definition ra_mod2 : recalg 1.
  Proof.
    ra root ra_rem.
    + ra arg pos0.
    + ra cst 2.
  Defined.

  Fact ra_mod2_prim_rec : prim_rec ra_mod2.
  Proof. ra prim rec. Qed. 

  Fact ra_mod2_val n : ⟦ra_mod2⟧ (n##vec_nil) (rem n 2).
  Proof.
    exists (n##2##vec_nil); split.
    + apply ra_rem_val; discriminate.
    + pos split; simpl; auto.
  Qed.

  Definition ra_pow2 : recalg 1.
  Proof.
    ra root ra_exp.
    + ra arg pos0.
    + ra cst 2.
  Defined.

  Fact ra_pow2_prim_rec : prim_rec ra_pow2.
  Proof. ra prim rec. Qed. 
 
  Fact ra_pow2_val n : ⟦ra_pow2⟧ (n##vec_nil) (power n 2).
  Proof.
    exists (n##2##vec_nil); split.
    + apply ra_exp_val; discriminate.
    + pos split; simpl; auto.
  Qed.

End ra_binary_ops.

Hint Resolve ra_div2_prim_rec ra_mod2_prim_rec ra_pow2_prim_rec
             ra_div2_val ra_mod2_val ra_pow2_val : core.
Opaque ra_div2 ra_mod2 ra_pow2.

Section ra_notdiv_pow2.

  (* f n m = 0 if 2^n does not divides m 
      and <> 0 if 2^n divides m *)

  Definition notdiv_pow2 n m := ite_rel (rem m (power n 2)) 1 0.

  Fact notdiv_pow2_spec_1 n m : notdiv_pow2 n m <> 0 <-> divides (power n 2) m.
  Proof.
    unfold notdiv_pow2.
    generalize (power n 2); clear n; intros n.
    unfold ite_rel; case_eq (rem m n).
    * intros H; split; try discriminate; intros _.
      exists (div m n).
      generalize (div_rem_spec1 m n); lia.
    * intros k Hk; split; try lia; intros H _.
      apply divides_rem_eq in H; lia.
  Qed.

  Fact notdiv_pow2_spec_2 n m : notdiv_pow2 n m = 0 <-> ~ divides (power n 2) m.
  Proof. rewrite <- notdiv_pow2_spec_1; lia. Qed.

  Definition ra_notdiv_pow2 : recalg 2.
  Proof.
    ra root ra_ite.
    + ra root ra_rem.
      * ra arg pos1.
      * ra root ra_pow2.
        ra arg pos0.
    + ra cst 1.
    + ra cst 0.
  Defined.

  Fact ra_notdiv_pow2_prim_rec : prim_rec ra_notdiv_pow2.
  Proof. ra prim rec. Qed.
   
  Fact ra_notdiv_pow2_val n m : ⟦ra_notdiv_pow2⟧ (n##m##vec_nil) (notdiv_pow2 n m).
  Proof.
    exists (rem m (power n 2)##1##0##vec_nil); split.
    + apply ra_ite_val.
    + pos split; simpl; auto.
      exists (m##power n 2##vec_nil); split.
      * apply ra_rem_val; generalize (@power_ge_1 n 2); intros; lia.
      * pos split; simpl; auto.
        exists (n##vec_nil); split; auto.
        pos split; simpl; auto.
  Qed.

End ra_notdiv_pow2.

Hint Resolve ra_notdiv_pow2_prim_rec ra_notdiv_pow2_val : core.
Opaque ra_notdiv_pow2.

Section ra_lsum.

  (* Given a prim rec algo recalg 1 and n
      returns f 0 v + f 1 v + ... + f (n-1) v *) 

  Variable (n : nat) (f : recalg (S n)) (Hf : prim_rec f).

  Let Hf' : forall v, exists x, ⟦f⟧ v x.
  Proof. apply prim_rec_tot; auto. Qed.

  Let h : recalg (S (S n)).
  Proof.
    ra root ra_plus.
    + apply ra_comp with (1 := f).
      apply vec_set_pos.
      intros p; invert pos p.
      * apply (ra_proj pos0).
      * apply (ra_proj (pos_nxt (pos_nxt p))).
    + ra arg pos1.
  Defined.

  Let h_prim_rec : prim_rec h.
  Proof. ra prim rec. Qed.

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
      intros p; generalize (H4 p); vec pos simpl.
    + intros (y & H1 & H2).
      exists (y##x##vec_nil); split; subst; auto.
      pos split; simpl; auto.
      exists (i##v); split; auto.
      pos split; simpl; auto.
      vec pos simpl.
  Qed.

  Opaque h.

  Definition ra_lsum : recalg (S n).
  Proof.
    apply ra_rec.
    + ra cst 0.
    + apply h.
  Defined.

  Fact ra_lsum_prim_rec : prim_rec ra_lsum.
  Proof. ra prim rec. Qed.

  Fact ra_lsum_spec i v lr : 
          Forall2 ⟦f⟧ (map (fun x => x##v) (list_an 0 i)) lr
       -> ⟦ra_lsum⟧ (i##v) (lsum lr).
  Proof.
    revert lr.
    induction i as [ | i IHi ]; intros lr H.
    + simpl in H.
      apply Forall2_nil_inv_l in H; subst lr; simpl.
      red; simpl; apply ra_cst_n_val.
    + replace (S i) with (i+1) in H by lia.
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
      * apply Hh; exists yn; split; auto; lia.
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
    intros p; rewrite list_an_spec; intros Hp; apply H; lia.
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
      apply lt_le_trans with (S k); try lia.
      apply lsum_le, vec_list_In_iff.
      exists (nat2pos Hp).
      specialize (Hw (nat2pos Hp)).
      rewrite pos2nat_nat2pos in Hw.
      revert H2 Hw; apply ra_rel_fun. }
    clear H Hw.
    revert H1 H2.
    generalize (lsum (vec_list w)).
    intros [ | k ]; intros; try lia; exists k; auto.
  Qed.

End ra_lsum.

Hint Resolve ra_lsum_prim_rec : core.
Opaque ra_lsum.

Definition nat_test_eq a b := ite_rel (a-b) (b-a) 1.

Fact nat_test_eq_spec0 a : nat_test_eq a a = 0.
Proof. 
  unfold nat_test_eq.
  replace (a-a) with 0; simpl; lia.
Qed.

Fact nat_test_eq_spec1 a b : a <> b -> nat_test_eq a b > 0.
Proof.
  intros H.
  destruct (lt_eq_lt_dec a b) as [ [] | ]; try tauto; unfold nat_test_eq.
  + replace (a-b) with 0; simpl; lia.
  + replace (a-b) with (S (a-S b)); simpl; lia.
Qed.

Fact nat_test_eq_spec a b : nat_test_eq a b = 0 <-> a = b.
Proof.
  split.
  + intros H.
    destruct (eq_nat_dec a b) as [ | D ]; auto.
    apply nat_test_eq_spec1 in D; lia.
  + intros ->; apply nat_test_eq_spec0.
Qed.

Section ra_choice3.

  (* if   x=0 then p 
      elif x=1 then q
               else r *)

  Definition ra_choice3 : recalg 4.
  Proof.
    ra root ra_ite.
    + ra root ra_eq.
      * ra arg pos0.
      * ra cst 0.
    + ra arg pos1.
    + ra root ra_ite.
      * ra root ra_eq.
        - ra arg pos0.
        - ra cst 1.
      * ra arg pos2.
      * ra arg pos3.
  Defined.

  Fact ra_choice3_prim_rec : prim_rec ra_choice3.
  Proof. ra prim rec. Qed.

  Fact ra_choice3_val b x y z : ⟦ra_choice3⟧ (b##x##y##z##vec_nil) 
                                  (match b with 0 => x | 1 => y | _ => z end).
  Proof.
    exists (nat_test_eq b 0##x##match b with 1 => y | _ => z end##vec_nil).
    simpl; split.
    { apply ra_ite_rel; simpl.
      destruct b as [ | [] ]; simpl; auto. }
    pos split; simpl; auto.
    + exists (b##0##vec_nil); split.
      * apply ra_eq_val.
      * pos split; simpl; auto.
    + exists (nat_test_eq b 1##y##z##vec_nil); split; simpl; auto.
      * apply ra_ite_rel; simpl.
        destruct b as [ | [] ]; simpl; auto.
      * pos split; simpl; auto.
        exists (b##1##vec_nil); split.
        - apply ra_eq_val.
        - pos split; simpl; auto.
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
    + rewrite H3; try lia.
      apply ra_choice3_val.
  Qed.

End ra_choice3.

Hint Resolve ra_choice3_prim_rec : core.
