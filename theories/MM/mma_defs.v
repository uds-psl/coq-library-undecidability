(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

From Undecidability.Shared.Libs.DLW Require Import Utils.utils Vec.pos Vec.vec.
From Undecidability.ILL.Code Require Import subcode sss.
From Undecidability.ILL.Mm Require Export mm_defs.

Set Implicit Arguments.

Tactic Notation "rew" "length" := autorewrite with length_db.

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).

(** * Alternate Minsky Machines such that two counters are enough for undec

    Minsky machine has n registers and there are just two instructions
 
    1/ INC x   : increment register x by 1
    2/ DEC x k : if x > 0 then decrement register x by 1 and jump to k

    If no jump occurs, then implicitly, the jump is to the next instruction

    We show that they simulated FRACTRAN
  *)

(** ** Semantics for MMA based on vectors *)

Section Minsky_Machine_alternate.

  Variable (n : nat).

  (* Minsky machine small step semantics *)

  Inductive mma_sss : mm_instr (pos n) -> mm_state _ -> mm_state _ -> Prop :=
    | in_mma_sss_inc   : forall i x v,                   INC x   // (i,v) -1> (1+i,v[(S (v#>x))/x])
    | in_mma_sss_dec_0 : forall i x k v,   v#>x = O   -> DEC x k // (i,v) -1> (1+i,v)
    | in_mma_sss_dec_1 : forall i x k v u, v#>x = S u -> DEC x k // (i,v) -1> (k,v[u/x])
  where "i // s -1> t" := (mma_sss i s t).

  Fact mma_sss_fun i s t1 t2 : i // s -1> t1 -> i // s -1> t2 -> t1 = t2.
  Proof.
    intros []; subst.
    inversion 1; subst; auto.
    inversion 1; subst; auto.
    rewrite H in H6; discriminate.
    inversion 1; subst; auto.
    rewrite H in H6; discriminate.
    rewrite H in H6; inversion H6; subst; auto.
  Qed.
  
  Fact mma_sss_total ii s : { t | ii // s -1> t }.
  Proof.
    destruct s as (i,v).
    destruct ii as [ x | x j ]; [ | case_eq (v#>x); [ | intros k ]; intros E ].
    * exists (1+i,v[(S (v#>x))/x]); constructor.
    * exists (1+i,v); constructor; auto.
    * exists (j,v[k/x]); constructor; auto.
  Qed.
  
  Fact mma_sss_INC_inv x i v j w : INC x // (i,v) -1> (j,w) -> j=1+i /\ w = v[(S (v#>x))/x].
  Proof. inversion 1; subst; auto. Qed.
  
  Fact mma_sss_DEC0_inv x k i v j w : v#>x = O -> DEC x k // (i,v) -1> (j,w) -> j = 1+i /\ w = v.
  Proof. 
    intros H; inversion 1; subst; auto; rewrite H in H2; try discriminate.
  Qed.
  
  Fact mma_sss_DEC1_inv x k u i v j w : v#>x = S u -> DEC x k // (i,v) -1> (j,w) -> j=k /\ w = v[u/x].
  Proof. 
    intros H; inversion 1; subst; auto; rewrite H in H2; try discriminate.
    inversion H2; subst; auto.
  Qed.

  Notation "P // s -[ k ]-> t" := (sss_steps mma_sss P k s t).
  Notation "P // s -+> t" := (sss_progress mma_sss P s t).
  Notation "P // s ->> t" := (sss_compute mma_sss P s t).
  
  Fact mma_sss_progress_INC P i x v st :
         (i,INC x::nil) <sc P
      -> P // (1+i,v[(S (v#>x))/x]) ->> st
      -> P // (i,v) -+> st.
  Proof.
    intros H1 H2.
    apply sss_progress_compute_trans with (2 := H2).
    apply subcode_sss_progress with (1 := H1).
    exists 1; split; auto; apply sss_steps_1.
    apply in_sss_step with (l := nil).
    simpl; omega.
    constructor; auto.
  Qed.
  
  Corollary mma_sss_compute_INC P i x v st : (i,INC x::nil) <sc P -> P // (1+i,v[(S (v#>x))/x]) ->> st -> P // (i,v) ->> st.
  Proof. intros; apply sss_progress_compute; eapply mma_sss_progress_INC; eauto. Qed.
  
  Fact mma_sss_progress_DEC_0 P i x k v st :
         (i,DEC x k::nil) <sc P
      -> v#>x = O 
      -> P // (1+i,v) ->> st
      -> P // (i,v) -+> st.
  Proof.
    intros H1 H2 H3.
    apply sss_progress_compute_trans with (2 := H3).
    apply subcode_sss_progress with (1 := H1).
    exists 1; split; auto; apply sss_steps_1.
    apply in_sss_step with (l := nil).
    simpl; omega.
    constructor; auto.
  Qed.
  
  Corollary mma_sss_compute_DEC_0 P i x k v st : (i,DEC x k::nil) <sc P -> v#>x = O -> P // (1+i,v) ->> st -> P // (i,v) ->> st.
  Proof. intros; apply sss_progress_compute; eapply mma_sss_progress_DEC_0; eauto. Qed.
  
  Fact mma_sss_progress_DEC_S P i x k v u st :
         (i,DEC x k::nil) <sc P
      -> v#>x = S u 
      -> P // (k,v[u/x]) ->> st
      -> P // (i,v) -+> st.
  Proof.
    intros H1 H2 H3.
    apply sss_progress_compute_trans with (2 := H3).
    apply subcode_sss_progress with (1 := H1).
    exists 1; split; auto; apply sss_steps_1.
    apply in_sss_step with (l := nil).
    simpl; omega.
    constructor; auto.
  Qed.
  
  Corollary mma_sss_compute_DEC_S P i x k v u st : (i,DEC x k::nil) <sc P -> v#>x = S u -> P // (k,v[u/x]) ->> st -> P // (i,v) ->> st.
  Proof. intros; apply sss_progress_compute; eapply mma_sss_progress_DEC_S; eauto. Qed.
  
  Fact mma_sss_steps_INC_inv k P i x v st :
         (i,INC x::nil) <sc P
      -> k <> 0
      -> P // (i,v) -[k]-> st
      -> exists k', k' < k /\ P // (1+i,v[(S (v#>x))/x]) -[k']-> st.
  Proof.
    intros H1 H2 H4.
    apply sss_steps_inv in H4.
    destruct H4 as [ (? & ?) | (k' & st2 & ? & H4 & H5) ]; subst; auto.
    destruct H2; auto.
    apply sss_step_subcode_inv with (1 := H1) in H4.
    exists k'; split.
    omega.
    inversion H4; subst; auto.
  Qed.
  
  Fact mma_sss_steps_DEC_0_inv k P i x p v st :
         (i,DEC x p::nil) <sc P
      -> k <> 0
      -> v#>x = 0
      -> P // (i,v) -[k]-> st
      -> exists k', k' < k /\ P // (1+i,v) -[k']-> st.
  Proof.
    intros H1 H2 H3 H4.
    apply sss_steps_inv in H4.
    destruct H4 as [ (? & ?) | (k' & st2 & ? & H4 & H5) ]; subst; auto.
    destruct H2; auto.
    apply sss_step_subcode_inv with (1 := H1) in H4.
    exists k'; split.
    omega.
    inversion H4; subst; auto.
    rewrite H3 in H9; discriminate.
  Qed.
  
  Fact mma_sss_steps_DEC_1_inv k P i x p v u st :
         (i,DEC x p::nil) <sc P
      -> k <> 0
      -> v#>x = S u
      -> P // (i,v) -[k]-> st
      -> exists k', k' < k /\ P // (p,v[u/x]) -[k']-> st.
  Proof.
    intros H1 H2 H3 H4.
    apply sss_steps_inv in H4.
    destruct H4 as [ (? & ?) | (k' & st2 & ? & H4 & H5) ]; subst; auto.
    destruct H2; auto.
    apply sss_step_subcode_inv with (1 := H1) in H4.
    exists k'; split.
    omega.
    inversion H4; subst; auto; rewrite H3 in H9.
    discriminate.
    inversion H9; subst; auto.
  Qed.

End Minsky_Machine_alternate.

Local Notation "P // s -+> t" := (sss_progress (@mma_sss _) P s t).
Local Notation "P // s ->> t" := (sss_compute (@mma_sss _) P s t).
Local Notation "P // s ↓" := (sss_terminates (@mma_sss _) P s). 

Tactic Notation "mma" "sss" "INC" "with" uconstr(a) := 
  match goal with
    | |- _ // _ -+> _ => apply mma_sss_progress_INC with (x := a)
    | |- _ // _ ->> _ => apply mma_sss_compute_INC with (x := a)
  end; auto.

Tactic Notation "mma" "sss" "DEC" "0" "with" uconstr(a) uconstr(b) := 
  match goal with
    | |- _ // _ -+> _ => apply mma_sss_progress_DEC_0 with (x := a) (k := b)
    | |- _ // _ ->> _ => apply mma_sss_compute_DEC_0 with (x := a) (k := b)
  end; auto.

Tactic Notation "mma" "sss" "DEC" "S" "with" uconstr(a) uconstr(b) uconstr(c) := 
  match goal with
    | |- _ // _ -+> _ => apply mma_sss_progress_DEC_S with (x := a) (k := b) (u := c)
    | |- _ // _ ->> _ => apply mma_sss_compute_DEC_S with (x := a) (k := b) (u := c)
  end; auto.
    
Tactic Notation "mma" "sss" "stop" := exists 0; apply sss_steps_0; auto.

Definition MMA2_PROBLEM := (list (mm_instr (pos 2)) * vec nat 2)%type.
Definition MMA2_HALTING (P : MMA2_PROBLEM) := (1,fst P) // (1,snd P) ↓.




