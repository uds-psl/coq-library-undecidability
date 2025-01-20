(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW
  Require Import utils subcode sss.

From Undecidability.MinskyMachines Require Export MM.
From Undecidability.MinskyMachines.MMenv Require Import env. 

Set Implicit Arguments.

(* * Minsky Machines

    A Minsky machine has n registers and there are just two instructions
 
    1/ INC x   : increment register x by 1
    2/ DEC x k : decrement register x by 1 if x > 0
                 or jump to k if x = 0

  *)

(* Semantics for MM based on environments *)

Section Minsky_Machine_env_based.

  Variable (X : Set) (X_eq_dec : eqdec X).

  Definition mm_state := (nat*env X nat)%type.

  Local Notation " e ⇢ x " := (@get_env _ _ e x).
  Local Notation " e ⦃  x ⇠ v ⦄ " := (@set_env _ _ X_eq_dec e x v).

  (* Minsky machine small step semantics *)

  Inductive mm_sss_env : mm_instr X -> mm_state -> mm_state -> Prop :=
    | in_mm_sss_env_inc   : forall i x v,                   INC x  // (i,v) -1> (1+i,v⦃x⇠S(v⇢x)⦄)
    | in_mm_sss_env_dec_0 : forall i x k v,   v⇢x = O   -> DEC x k // (i,v) -1> (k,v)
    | in_mm_sss_env_dec_1 : forall i x k v u, v⇢x = S u -> DEC x k // (i,v) -1> (1+i,v⦃x⇠u⦄)
  where "i // s -1> t" := (mm_sss_env i s t).

  Fact mm_sss_env_fun i s t1 t2 : i // s -1> t1 -> i // s -1> t2 -> t1 = t2.
  Proof.
    intros []; subst.
    inversion 1; subst; auto.
    inversion 1; subst; auto.
    rewrite H in H6; discriminate.
    inversion 1; subst; auto.
    rewrite H in H6; discriminate.
    rewrite H in H6; inversion H6; subst; auto.
  Qed.
  
  Fact mm_sss_env_total ii s : { t | ii // s -1> t }.
  Proof.
    destruct s as (i,v).
    destruct ii as [ x | x j ]; [ | case_eq (v⇢x); [ | intros k ]; intros E ].
    * exists (1+i,v⦃x⇠S(v⇢x)⦄); constructor.
    * exists (j,v); constructor; auto.
    * exists (1+i,v⦃x⇠k⦄); constructor; auto.
  Qed.
  
  Fact mm_sss_env_INC_inv x i v j w : INC x // (i,v) -1> (j,w) -> j=1+i /\ w = v⦃x⇠S(v⇢x)⦄.
  Proof. inversion 1; subst; auto. Qed.
  
  Fact mm_sss_env_DEC0_inv x k i v j w : v⇢x = O -> DEC x k // (i,v) -1> (j,w) -> j = k /\ w = v.
  Proof. 
    intros H; inversion 1; subst; auto; rewrite H in H2; try discriminate.
  Qed.
  
  Fact mm_sss_env_DEC1_inv x k u i v j w : v⇢x = S u -> DEC x k // (i,v) -1> (j,w) -> j=1+i /\ w = v⦃x⇠u⦄.
  Proof. 
    intros H; inversion 1; subst; auto; rewrite H in H2; try discriminate.
    inversion H2; subst; auto.
  Qed.

  Notation "P // s -[ k ]-> t" := (sss_steps mm_sss_env P k s t).
  Notation "P // s -+> t" := (sss_progress mm_sss_env P s t).
  Notation "P // s ->> t" := (sss_compute mm_sss_env P s t).
  
  Fact mm_env_progress_INC P i x v st :
         (i,INC x::nil) <sc P
      -> P // (1+i,v⦃x⇠S(v⇢x)⦄) ->> st
      -> P // (i,v) -+> st.
  Proof.
    intros H1 H2.
    apply sss_progress_compute_trans with (2 := H2).
    apply subcode_sss_progress with (1 := H1).
    exists 1; split; auto; apply sss_steps_1.
    apply in_sss_step with (l := nil).
    simpl; lia.
    constructor; auto.
  Qed.
  
  Corollary mm_env_compute_INC P i x v st : 
         (i,INC x::nil) <sc P 
      -> P // (1+i,v⦃x⇠S(v⇢x)⦄) ->> st 
      -> P // (i,v) ->> st.
  Proof. intros; apply sss_progress_compute; eapply mm_env_progress_INC; eauto. Qed.
  
  Fact mm_env_progress_DEC_0 P i x k v st :
         (i,DEC x k::nil) <sc P
      -> v⇢x = O 
      -> P // (k,v) ->> st
      -> P // (i,v) -+> st.
  Proof.
    intros H1 H2 H3.
    apply sss_progress_compute_trans with (2 := H3).
    apply subcode_sss_progress with (1 := H1).
    exists 1; split; auto; apply sss_steps_1.
    apply in_sss_step with (l := nil).
    simpl; lia.
    constructor; auto.
  Qed.
  
  Corollary mm_env_compute_DEC_0 P i x k v st : 
         (i,DEC x k::nil) <sc P 
      -> v⇢x = O 
      -> P // (k,v) ->> st 
      -> P // (i,v) ->> st.
  Proof. intros; apply sss_progress_compute; eapply mm_env_progress_DEC_0; eauto. Qed.
  
  Fact mm_env_progress_DEC_S P i x k v u st :
         (i,DEC x k::nil) <sc P
      -> v⇢x = S u 
      -> P // (1+i,v⦃x⇠u⦄) ->> st
      -> P // (i,v) -+> st.
  Proof.
    intros H1 H2 H3.
    apply sss_progress_compute_trans with (2 := H3).
    apply subcode_sss_progress with (1 := H1).
    exists 1; split; auto; apply sss_steps_1.
    apply in_sss_step with (l := nil).
    simpl; lia.
    constructor; auto.
  Qed.
  
  Corollary mm_env_compute_DEC_S P i x k v u st : 
           (i,DEC x k::nil) <sc P 
        -> v⇢x = S u 
        -> P // (1+i,v⦃x⇠u⦄) ->> st 
        -> P // (i,v) ->> st.
  Proof. intros; apply sss_progress_compute; eapply mm_env_progress_DEC_S; eauto. Qed.
  
  Fact mm_env_steps_INC_inv k P i x v st :
         (i,INC x::nil) <sc P
      -> k <> 0
      -> P // (i,v) -[k]-> st
      -> exists k', k' < k /\ P // (1+i,v⦃x⇠S(v⇢x)⦄) -[k']-> st.
  Proof.
    intros H1 H2 H4.
    apply sss_steps_inv in H4.
    destruct H4 as [ (? & ?) | (k' & st2 & ? & H4 & H5) ]; subst; auto.
    destruct H2; auto.
    apply sss_step_subcode_inv with (1 := H1) in H4.
    exists k'; split.
    lia.
    inversion H4; subst; auto.
  Qed.
  
  Fact mm_env_steps_DEC_0_inv k P i x p v st :
         (i,DEC x p::nil) <sc P
      -> k <> 0
      -> v⇢x = 0
      -> P // (i,v) -[k]-> st
      -> exists k', k' < k /\ P // (p,v) -[k']-> st.
  Proof.
    intros H1 H2 H3 H4.
    apply sss_steps_inv in H4.
    destruct H4 as [ (? & ?) | (k' & st2 & ? & H4 & H5) ]; subst; auto.
    destruct H2; auto.
    apply sss_step_subcode_inv with (1 := H1) in H4.
    exists k'; split.
    lia.
    inversion H4; subst; auto.
    rewrite H3 in H9; discriminate.
  Qed.
  
  Fact mm_env_steps_DEC_1_inv k P i x p v u st :
         (i,DEC x p::nil) <sc P
      -> k <> 0
      -> v⇢x = S u
      -> P // (i,v) -[k]-> st
      -> exists k', k' < k /\ P // (1+i,v⦃x⇠u⦄) -[k']-> st.
  Proof.
    intros H1 H2 H3 H4.
    apply sss_steps_inv in H4.
    destruct H4 as [ (? & ?) | (k' & st2 & ? & H4 & H5) ]; subst; auto.
    destruct H2; auto.
    apply sss_step_subcode_inv with (1 := H1) in H4.
    exists k'; split.
    lia.
    inversion H4; subst; auto; rewrite H3 in H9.
    discriminate.
    inversion H9; subst; auto.
  Qed.
  
End Minsky_Machine_env_based.

Local Notation "P // s -[ k ]-> t" := (sss_steps (@mm_sss_env _ _) P k s t).
Local Notation "P // s -+> t" := (sss_progress (@mm_sss_env _ _) P s t).
Local Notation "P // s ->> t" := (sss_compute (@mm_sss_env _ _) P s t).

Tactic Notation "mm" "env" "INC" "with" uconstr(a) := 
  match goal with
    | |- _ // _ -+> _ => apply mm_env_progress_INC with (x := a)
    | |- _ // _ ->> _ => apply mm_env_compute_INC with (x := a)
  end; auto.

Tactic Notation "mm" "env" "DEC" "zero" "with" uconstr(a) uconstr(b) := 
  match goal with
    | |- _ // _ -+> _ => apply mm_env_progress_DEC_0 with (x := a) (k := b)
    | |- _ // _ ->> _ => apply mm_env_compute_DEC_0 with (x := a) (k := b)
  end; auto.

Tactic Notation "mm" "env" "DEC" "S" "with" uconstr(a) uconstr(b) uconstr(c) := 
  match goal with
    | |- _ // _ -+> _ => apply mm_env_progress_DEC_S with (x := a) (k := b) (u := c)
    | |- _ // _ ->> _ => apply mm_env_compute_DEC_S with (x := a) (k := b) (u := c)
  end; auto.

Tactic Notation "mm" "env" "stop" := exists 0; apply sss_steps_0; auto.

(* The Halting problem for MM, for linear logic encoding, we restrict
   to a very specific halting problem. Starting from (1,v), does the
   MM halt at state (0,vec_zero) *)
