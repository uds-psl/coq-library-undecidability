(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* Require Import dio_expr dio_logic dio_elem dio_poly. *)

Require Import List Arith Omega.

Require Import utils_tac utils_list sums rel_iter pos vec.
Require Import fractran_defs prime_seq.
Require Import dio_logic dio_bounded dio_rt_closure dio_single.

Set Implicit Arguments.

Section fractran_dio.

  Notation "l /F/ x → y" := (fractran_step l x y) (at level 70, no associativity).

  (* Fractran step is a diophantine relation *)

  Lemma dio_rel_fractran_step l x y : 𝔻P x -> 𝔻P y -> 𝔻R (fun ν => l /F/ x ν → y ν).
  Proof.
    intros Hx Hy.
    induction l as [ | (p,q) l IHl ].
    + apply dio_rel_equiv with (fun _ => False); auto.
      intros v; rewrite fractran_step_nil_inv; split; tauto.
    + apply dio_rel_equiv with (1 := fun v => fractran_step_cons_inv p q l (x v) (y v)); auto.
  Defined.

  Hint Resolve dio_rel_fractran_step.

  (* Hence Fractan step* (refl. trans. closure) is diophantine *)

  Theorem dio_rel_fractran_rt l x y : 
             Forall (fun c => snd c <> 0) l 
          -> 𝔻P x
          -> 𝔻P y
          -> 𝔻R (fun ν => fractran_compute l (x ν) (y ν)).
  Proof.
    intros Hl Hx Hy.
    destruct (fractran_step_bound Hl) as (k & Hk).
    apply dio_rel_exst, dio_rel_rel_iter with (1 := Hk); auto.
  Defined.

  (* Fractran stop is a diophantine relation *)

  Theorem dio_rel_fractran_stop l x : 𝔻P x -> 𝔻R (fun ν => fractran_stop l (x ν)).
  Proof.
    intros Hx.
    induction l as [ | (p,q) l IHl ].
    + apply dio_rel_equiv with (fun _ => True); auto.
      intro v; split; auto; intros _ ?.
      rewrite fractran_step_nil_inv; auto.
    + apply dio_rel_equiv with (1 := fun v => fractan_stop_cons_inv p q l (x v)); auto.
  Defined.

  Hint Resolve dio_rel_fractran_rt dio_rel_fractran_stop.

  (* We start with the case of regular Fractran programs that do not
     contain (_,0) "fractions" *)

  (* Hence Halting from the value x is diophantine *)

  Theorem FRACTRAN_HALTING_diophantine_1 ll x : 
           fractran_regular ll 
        -> 𝔻P x 
        -> 𝔻R (fun ν => FRACTRAN_HALTING (ll,x ν)).
  Proof.
    intros; apply dio_rel_exst, dio_rel_conj; auto.
  Defined.

  Theorem FRACTRAN_HALTING_diophantine_0 ll : 
           fractran_regular ll 
        -> 𝔻R (fun ν => FRACTRAN_HALTING (ll,ν 0)).
  Proof.
    intros; apply FRACTRAN_HALTING_diophantine_1; auto.
  Defined.

  Notation remove_zero_den := (fun l : list (nat*nat) => filter (fun c => if eq_nat_dec (snd c) 0 then false else true) l).

  Let remove_zero_den_Forall l : fractran_regular (remove_zero_den l).
  Proof.
    unfold fractran_regular.
    induction l as [ | (p,q) ]; simpl; auto.
    destruct (eq_nat_dec q 0); auto.
  Qed.

  Hint Resolve FRACTRAN_HALTING_diophantine_1.

  (* We can also show the result for arbitrary Fractran programs
     but the proof is more complicated in that case *)

  Theorem FRACTRAN_HALTING_on_diophantine ll x : 𝔻P x -> 𝔻R (fun ν => FRACTRAN_HALTING (ll,x ν)).
  Proof.
    intros Hx.
    destruct (FRACTAN_cases ll) as [ [ [ H1 | H1 ] | (p & mm & H1 & H2 & H3 & H4) ] | (p & q & mm & H1 & H2 & H3 & H4 & H5) ].
    + exists df_false; intros v; rewrite FRACTRAN_HALTING_0_num, df_false_spec; tauto.
    + apply FRACTRAN_HALTING_diophantine_1; trivial.
    + destruct FRACTRAN_HALTING_diophantine_0 with (ll := remove_zero_den ll) as (f & Hf).
      { apply remove_zero_den_Forall. }
      assert (forall ν, FRACTRAN_HALTING (ll, x ν) <-> x ν <> 0 /\ FRACTRAN_HALTING (remove_zero_den ll, x ν)
                                                   \/  x ν = 0 /\  exists y, y <> 0 /\ FRACTRAN_HALTING (remove_zero_den ll, y)) as H5.
      { intros v; subst ll.
        destruct (eq_nat_dec (x v) 0) as [ H | H ].
        + rewrite H, FRACTRAN_HALTING_hard; auto.
          split.
          * intros (y & G1 & G2); right; split; auto; exists y; split; auto.
            rewrite <- FRACTRAN_HALTING_l_1_no_zero_den; auto; discriminate.
          * intros [ ([] & _) | (_ & y & G1 & G2) ]; auto.
            exists y; split; auto.
            apply FRACTRAN_HALTING_l_1_no_zero_den; auto; try discriminate.
        + rewrite <- FRACTRAN_HALTING_l_1_no_zero_den; auto; try discriminate.
          split; tauto. }
      apply dio_rel_equiv with (1 := H5); dio_rel_auto.
    + assert (forall ν, FRACTRAN_HALTING (ll, x ν) <-> x ν <> 0 /\ FRACTRAN_HALTING (remove_zero_den ll, x ν)) as H6.
      { intros v; subst ll.
        destruct (eq_nat_dec (x v) 0) as [ H | H ].
        * rewrite H, FRACTRAN_HALTING_on_zero_first_no_zero_den; auto.
          split; tauto; omega.
        * rewrite  FRACTRAN_HALTING_l_1_no_zero_den; auto; try discriminate; tauto. }
       apply dio_rel_equiv with (1 := H6); dio_rel_auto.
  Defined.

  Theorem FRACTRAN_HALTING_diophantine l x : 𝔻R (fun _ => FRACTRAN_HALTING (l,x)).
  Proof. apply FRACTRAN_HALTING_on_diophantine; auto. Defined.

End fractran_dio.

Local Notation power := (mscal mult 1).

Fact power_expo x y : power x y = y^x.
Proof.
  induction x as [ | x IHx ]; simpl.
  + rewrite power_0; auto.
  + rewrite power_S; f_equal; auto.
Qed.

Theorem FRACTRAN_HALTING_dio_single l x :
     fractran_regular l
  -> { e : dio_single nat Empty_set | l /F/ x ↓ <-> dio_single_pred e (fun _ => 0) }.
Proof.
  intros Hl.
  generalize (@FRACTRAN_HALTING_diophantine_1 _ (fun _ => x) Hl); intros H1.
  spec in H1; auto.
  destruct dio_rel_single with (1 := H1) as ((p,q) & He).
  unfold FRACTRAN_HALTING in He.
  exists (dp_inst_par (fun _ => 0) p, dp_inst_par (fun _ => 0) q).
  rewrite He with (ν := fun _ => 0).
  unfold dio_single_pred; simpl.
  split; intros (phi & Hphi); exists phi; revert Hphi;
    repeat rewrite dp_inst_par_eval; auto.
Qed.

Section exp_diophantine.

  (* for fixed n i j, the function v => exp i <v(j),...,v(n-1+j)> has a diophantine representation *)

  Let exp_dio n i j y : 𝔻P y -> 𝔻R (fun v => y v = exp i (fun2vec j n v)).
  Proof.
    revert j i y; induction n as [ | n IHn ]; intros j i y Hy.
    + simpl; dio_rel_auto.
    + assert (H : forall v, y v = exp i (fun2vec j (S n) v)
                        <-> exists q1 q2, y v = q1*q2 
                                       /\ q1 = power (v j) (qs i) 
                                       /\ q2 = exp (S i) (fun2vec (S j) n v)).
      { intros v; simpl fun2vec; rewrite exp_cons; split.
        * exists (qs i^v j), (exp (S i) (fun2vec (S j) n v));
            rewrite power_expo; auto.
        * intros (q1 & q2 & H & ? & ?); subst.
          rewrite H, power_expo; auto. }
      apply dio_rel_equiv with (1 := H); clear H.
      do 2 apply dio_rel_exst.
      apply dio_rel_conj; auto.
      apply dio_rel_conj; auto.
      assert (H : dio_rel (fun v => v 0 = exp (S i) (fun2vec (3+j) n v))).
      { apply IHn; auto. }
      revert H; apply dio_rel_equiv.
      intros v; rewrite fun2vec_lift with (f := fun i => v (S i)).
      rewrite fun2vec_lift; simpl; tauto.
  Qed.

  (* for a fixed n, the relation 
  
         ν 0 = ps 1 * (qs 1)^(ν 1) * ... * (qs n)^(ν n) 

     has a diophantine representation *)

  Hint Resolve exp_dio.

  Fact exp_diophantine n : 𝔻R (fun ν => ν 0 = ps 1 * exp 1 (fun2vec 0 n (fun x => ν (S x)))).
  Proof.
    apply dio_rel_equiv with (fun v => exists y, v 0 = ps 1 * y 
                                    /\ y = exp 1 (fun2vec 0 n (fun x => v (S x)))).
    + intro v; split.
      * exists (exp 1 (fun2vec 0 n (fun x => v (S x)))); auto.
      * intros (y & H1 & <-); auto.
    + apply dio_rel_exst, dio_rel_conj; auto.
      apply dio_rel_equiv with (fun v => v 0 = exp 1 (fun2vec 2 n v)); auto.
      intro; repeat rewrite <- fun2vec_lift; tauto.
  Qed.

End exp_diophantine.

Hint Resolve exp_diophantine.

Theorem FRACTRAN_HALTING_on_exp_diophantine n l : 
     fractran_regular l -> 𝔻R (fun ν => l /F/ ps 1 * exp 1 (fun2vec 0 n ν) ↓).
Proof.
  intros Hl.
  apply dio_rel_compose with (R := fun x v => l /F/ x ↓); auto.
  apply FRACTRAN_HALTING_diophantine_1; auto.
Qed.

Check FRACTRAN_HALTING_on_exp_diophantine.
Print Assumptions FRACTRAN_HALTING_on_exp_diophantine.
