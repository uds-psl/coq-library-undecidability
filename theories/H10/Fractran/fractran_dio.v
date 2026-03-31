(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* ** FRACTRAN termination is Diophantine *)

(* Require Import dio_expr dio_logic dio_elem dio_poly. *)

From Stdlib Require Import List Arith.

From Undecidability.Shared.Libs 
  Require Import utils_tac utils_list sums rel_iter gcd pos vec.

From Undecidability.FRACTRAN 
  Require Import FRACTRAN fractran_utils prime_seq.

From Undecidability.H10.Dio 
  Require Import dio_logic dio_bounded dio_rt_closure dio_single dio_expo.

Set Implicit Arguments.

Section fractran_dio.

  Notation "l /F/ x → y" := (fractran_step l x y) (at level 70, no associativity).

  (* Fractran step is a diophantine relation, by induction on l *)

  Lemma dio_rel_fractran_step l x y : 𝔻F x -> 𝔻F y -> 𝔻R (fun ν => l /F/ x ν → y ν).
  Proof.
    intros Hx Hy.
    induction l as [ | (p,q) l IHl ].
    + by dio equiv (fun _ => False).
      abstract (intros v; rewrite fractran_step_nil_inv; split; tauto).
    + dio by lemma (fun v => fractran_step_cons_inv p q l (x v) (y v)).
  Defined.

  Hint Resolve dio_rel_fractran_step : dio_rel_db.

  (* Hence Fractan step* (refl. trans. closure) is diophantine *)

  Corollary dio_rel_fractran_rt l x y : 
                     𝔻F x -> 𝔻F y -> 𝔻R (fun ν => fractran_compute l (x ν) (y ν)).
  Proof. intros; apply dio_rel_rt; dio auto. Defined.

  (* Fractran stop is a diophantine relation *)

  Lemma dio_rel_fractran_stop l x : 𝔻F x -> 𝔻R (fun ν => fractran_stop l (x ν)).
  Proof.
    intros Hx.
    induction l as [ | (p,q) l IHl ].
    + by dio equiv (fun _ => True).
      abstract(intro v; split; auto; intros _ ?; rewrite fractran_step_nil_inv; auto).
    + dio by lemma (fun v => fractan_stop_cons_inv p q l (x v)).
  Defined.

  Definition fractran_eval_old P n m := fractran_compute P n m /\ fractran_stop P m.

  Hint Resolve dio_rel_fractran_rt dio_rel_fractran_stop : dio_rel_db.

  Lemma dio_rel_fractran_eval l x y : 
      𝔻F x -> 𝔻F y -> 𝔻R (fun ν => fractran_eval_old l (x ν) (y ν)).
  Proof.
    intros Hx Hy.  unfold fractran_eval_old.
    dio auto.
  Defined.

  (* We start with the case of regular Fractran programs that do not
     contain (_,0) "fractions" *)

  (* Hence Halting from the value x is diophantine *)

  Theorem FRACTRAN_HALTING_on_diophantine ll x :
                      𝔻F x -> 𝔻R (fun ν => FRACTRAN_HALTING (ll,x ν)).
  Proof. intros; dio auto. Defined.

End fractran_dio.

Corollary FRACTRAN_HALTING_diophantine_0 ll : 𝔻R (fun ν => FRACTRAN_HALTING (ll,ν 0)).
Proof. intros; apply FRACTRAN_HALTING_on_diophantine; dio auto. Defined.

Corollary FRACTRAN_HALTING_diophantine l x : 𝔻R (fun _ => FRACTRAN_HALTING (l,x)).
Proof. apply FRACTRAN_HALTING_on_diophantine; dio auto. Defined.

Section exp_diophantine.

  Abbreviation power := (mscal mult 1).

  Fact power_expo x y : power x y = y^x.
  Proof.
    induction x as [ | x IHx ]; simpl.
    + rewrite power_0; auto.
    + rewrite power_S; f_equal; auto.
  Qed.

  (* for fixed n i j, the function v => exp i <v(j),...,v(n-1+j)> has a diophantine representation *)

  Let exp_dio n i j : 𝔻F (fun v => exp i (fun2vec j n v)).
  Proof.
    revert j i; induction n as [ | n IHn ]; intros j i.
    + simpl; dio auto.
    + by dio equiv (fun v => power (v j) (qs i) * exp (S i) (fun2vec (S j) n v)).
      abstract (intros v; simpl fun2vec; rewrite exp_cons, power_expo; auto).
  Defined.

  Let exp_dio_lift n i j : 𝔻F (fun v => exp i (fun2vec j n v⭳)).
  Proof.
    revert j i; induction n as [ | n IHn ]; intros j i.
    + simpl; dio auto.
    + by dio equiv (fun v => power (v (S j)) (qs i) * exp (S i) (fun2vec (S j) n v⭳)).
      abstract (intros v; simpl fun2vec; rewrite exp_cons, power_expo; auto).
  Qed.

  (* for a fixed n, the relation 
  
         ν 0 = ps 1 * (qs 1)^(ν 1) * ... * (qs n)^(ν n) 

     has a diophantine representation *)

  Fact fractran_exp_diophantine n : 𝔻F (fun ν => ps 1 * exp 1 (fun2vec 0 n ν)).
  Proof. dio auto. Defined.

  Fact fractran_exp_diophantine' n : 𝔻F (fun ν => ps 1 * exp 2 (fun2vec 1 n ν⭳)).
  Proof. eapply dio_fun_mult. dio auto. eapply exp_dio_lift. Qed.

  Fact fractran_exp_diophantine'' : 𝔻F (fun ν => ν 1 * qs 1 ^ ν 2).
  Proof. 
    by dio equiv (fun ν => ν 1 * power  (ν 2) (qs 1)).
    intros. now rewrite power_expo.
  Qed.
  
End exp_diophantine.

#[export] Hint Resolve fractran_exp_diophantine fractran_exp_diophantine' fractran_exp_diophantine'' : dio_fun_db.

Theorem FRACTRAN_HALTING_on_exp_diophantine n l :  
                     𝔻R (fun ν => l /F/ ps 1 * exp 1 (fun2vec 0 n ν) ↓).
Proof.
  apply dio_rel_compose with (R := fun x v => l /F/ x ↓); [ dio auto | ].
  apply FRACTRAN_HALTING_on_diophantine; dio auto.
Qed.

Theorem fractran_eval_old_diophantine n l :  
                     𝔻R (fun ν => fractran_eval_old l (ps 1 * exp 2 (fun2vec 1 n ν⭳)) (ν 0 * qs 1 ^ (ν 1))).
Proof.
  apply dio_rel_compose with (R := fun x v => fractran_eval_old l x _); [ dio auto | ]. 
  apply dio_rel_compose with (R := fun x v => fractran_eval_old l _ x); [ dio auto | ].
  apply dio_rel_fractran_eval; dio auto.
Qed. 

Theorem fractran_eval_diophantine n l :  
                     𝔻R (fun ν => fractran_eval l (ps 1 * exp 2 (fun2vec 1 n ν⭳)) (ν 0 * qs 1 ^ (ν 1))).
Proof.
  edestruct fractran_eval_old_diophantine as [? H].
  eexists. setoid_rewrite FRACTRAN_sss.eval_iff. exact H.
Qed. 

Theorem fractran_computable_diophantine n l :  
                     𝔻R (fun ν => exists j, fractran_eval l (ps 1 * exp 2 (fun2vec 1 n ν)) (j * qs 1 ^ (ν 0)) /\ ~ divides (qs 1) j).
Proof.
  dio auto. eapply fractran_eval_diophantine.
Qed.

Theorem FRACTRAN_HALTING_dio_single E l x : { e : dio_single nat E | l /F/ x ↓ <-> dio_single_pred e (fun _ => 0) }.
Proof.
  generalize (@FRACTRAN_HALTING_on_diophantine l (fun _ => x)); intros H1.
  spec in H1; dio_rel_auto.
  destruct dio_rel_single with (1 := H1) as ((p,q) & He).
  unfold FRACTRAN_HALTING in He.
  exists (dp_inst_par E (fun _ => 0) p, dp_inst_par E (fun _ => 0) q).
  rewrite He with (ν := fun _ => 0).
  unfold dio_single_pred; simpl.
  split; intros (phi & Hphi); exists phi; revert Hphi;
    repeat rewrite dp_inst_par_eval; auto.
Qed.
