(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Certified Undecidability of Intuitionistic Linear Logic via Binary Stack Machines and Minsky Machines. Yannick Forster and Dominique Larchey-Wendling. CPP '19. http://uds-psl.github.io/ill-undecidability/ *)

Require Import Undecidability.StackMachines.BSM.

From Stdlib Require Import List Bool Lia Nat.

From Undecidability.Shared.Libs.DLW 
  Require Import list_bool pos vec sss.

Set Implicit Arguments.

(** * Halting problem for binary stack machines BSM_HALTING  *)

(* * Binary Stack Machines
   Binary stack machines have n stacks and there are just two instructions
  
   1/ POP s p q : pops the value on stack s and
                  if Empty then jumps to q 
                  if Zero then jumps to p
                  if One then jumps to next instruction,
   2/ PUSH s b : pushes the value b on stack s and jumps to next instructions 

 *)

(* Inductive bsm_instr n : Set := *)
(*   | bsm_pop  : pos n -> nat -> nat -> bsm_instr n *)
(*   | bsm_push : pos n -> bool -> bsm_instr n *)
(*   . *)
Arguments bsm_pop {n}.
Arguments bsm_push {n}.

Notation POP  := bsm_pop.
Notation PUSH := bsm_push.

(* ** Semantics for BSM *)

Section Binary_Stack_Machine.

  Variable (n : nat).

  Definition bsm_state := (nat*vec (list bool) n)%type.

  Local Notation "e #> x" := (vec_pos e x).
  Local Notation "e [ v / x ]" := (vec_change e x v).

  Inductive bsm_sss : bsm_instr n -> bsm_state -> bsm_state -> Prop :=
    | in_bsm_sss_pop_E : forall i x p q v,    v#>x = nil      -> POP x p q // (i,v) -1> (  q,v)
    | in_bsm_sss_pop_0 : forall i x p q v ll, v#>x = Zero::ll -> POP x p q // (i,v) -1> (  p,v[ll/x])
    | in_bsm_sss_pop_1 : forall i x p q v ll, v#>x = One ::ll -> POP x p q // (i,v) -1> (1+i,v[ll/x])
    | in_bsm_sss_push  : forall i x b v,                         PUSH x b  // (i,v) -1> (1+i,v[(b::v#>x)/x])
  where "i // s -1> t" := (bsm_sss i s t).

End Binary_Stack_Machine.

Lemma eval_to_sss_compute n i (P : list (bsm_instr n)) c (v : vec (list bool) n) c' v' :
  eval n (i, P) (c, v) (c', v') -> sss_compute (@bsm_sss _) (i,P) (c, v) (c', v').
Proof.
  generalize (i, P) as iP.
  generalize (c, v) as cv.
  generalize (c', v') as c'v'. clear.
  induction 1 as [ i P c v
                 | i P c v j b c' v' H1 H2 H [k IH]
                 | i P c v j c1 c2 c' v' l H1 H2 H3 H [k IH]
                 | i P c v j c1 c2 c' v' l H1 H2 H3 H [k IH]   
                 | i P c v j c1 c2 c' v' H1 H2 H3 H [k IH] ].
  - exists 0. econstructor.
  - exists (1 + k).
    eapply nth_error_split in H2 as (l1 & l2 & -> & Hl).
    repeat econstructor.
    + f_equal. lia.
    + now replace (1 + c) with (c + 1) by lia.
  - exists (1 + k).
    eapply nth_error_split in H2 as (l1 & l2 & -> & Hl).
    econstructor; [ | eauto]. 
    repeat econstructor.
    + f_equal. lia.
    + replace (c + 1) with (1 + c) by lia. econstructor. eauto.
  - exists (1 + k).
    eapply nth_error_split in H2 as (l1 & l2 & -> & Hl).
    econstructor; [ | eauto].
    repeat econstructor.
    * f_equal. lia.
    * eauto.
  - exists (1 + k).
    eapply nth_error_split in H2 as (l1 & l2 & -> & Hl).
    econstructor; [ | eauto].
    repeat econstructor.
    + f_equal. lia.
    + eauto.
Qed.

Lemma eval_to_sss_out_code n i (P : list (bsm_instr n)) c (v : vec (list bool) n) c' v' :
  eval n (i, P) (c, v) (c', v') -> subcode.out_code (fst (c', v')) (i, P).
Proof.
  generalize (i, P) as iP.
  generalize (c, v) as cv.
  generalize (c', v') as c'v'. clear.
  induction 1 as [ i P c v
                 | i P c v j b c' v' H1 H2 H IH
                 | i P c v j c1 c2 c' v' l H1 H2 H3 H IH
                 | i P c v j c1 c2 c' v' l H1 H2 H3 H IH
                 | i P c v j c1 c2 c' v' H1 H2 H3 H IH]; cbn in *.
  all: lia.
Qed.

Lemma sss_output_to_eval n i (P : list (bsm_instr n)) c (v : vec (list bool) n) c' v' :
  sss_output (@bsm_sss _) (i,P) (c, v) (c', v') -> eval n (i, P) (c, v) (c', v').
Proof.
  generalize (i, P) as iP.
  generalize (c, v) as cv.
  generalize (c', v') as c'v'. clear.
  intros ? ? ? [[k H1] H2].
  induction H1 as [cv | n0 st1 st2 (c', v') (k & l & i & r & d & -> & -> & HH) H IH] in * |- *.
  - destruct iP as (i, P), cv as (c, v);
      try destruct c'v' as (c', v').
    econstructor. cbn in *. lia.
  - revert IH H H2.
    inversion_clear HH as [ | | | ]; subst; intros IH' HHH IH % IH'; clear IH'.
    + eapply eval_bsm_pop_empty; [ lia | | eauto ..].
      rewrite nth_error_app2; [ | lia].
      now replace (k + length l - k - length l) with 0 by lia.
    + eapply eval_bsm_pop_false; [ lia | | eauto ..].
      rewrite nth_error_app2; [ | lia].
      now replace (k + length l - k - length l) with 0 by lia.
    + eapply eval_bsm_pop_true; [ lia | | eauto ..].
      * rewrite nth_error_app2; [ | lia].
        now replace (k + length l - k - length l) with 0 by lia.
      * now replace (k + length l + 1) with (1 + (k + length l)) by lia.
    + eapply eval_bsm_push; [ lia | | eauto ..].
      * rewrite nth_error_app2; [ | lia].
        now replace (k + length l - k - length l) with 0 by lia.
      * now replace (k + length l + 1) with (1 + (k + length l)) by lia.
Qed.

Theorem eval_iff n i (P : list (bsm_instr n)) c (v : vec (list bool) n) c' v' :
  eval n (i, P) (c, v) (c', v') <-> sss_output (@bsm_sss _) (i,P) (c, v) (c', v').
Proof.
  split.
  - intros H. split.
    + now eapply eval_to_sss_compute.
    + eapply eval_to_sss_out_code. eassumption.
  - intros H. now eapply sss_output_to_eval.
Qed.

(* The Halting problem for BSM *)
  
Definition BSM_PROBLEM := { n : nat & { i : nat & { P : list (bsm_instr n) & vec (list bool) n } } }.

Local Notation "P // s ↓" := (sss_terminates (@bsm_sss _) P s).

Definition BSMn_HALTING n (P : BSMn_PROBLEM n) :=
  match P with existT _ i (existT _ P v) => (i,P) // (i,v) ↓ end.

Arguments BSMn_HALTING : clear implicits.

Definition BSM_HALTING (P : BSM_PROBLEM) := 
  match P with existT _ n (existT _ i (existT _ P v)) => (i,P) // (i,v) ↓ end.

Lemma Halt_BSM_iff P :
  Halt_BSM P <-> BSM_HALTING P.
Proof.
  destruct P as (n & i & P & v); cbn.
  split.
  - intros (c' & v' & H % eval_iff). eexists. eauto.
  - intros [(c', v') H % eval_iff]. eauto.
Qed.
