(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Bool Arith Lia.

From Undecidability.Shared.Libs.DLW 
  Require Import subcode sss.

From Undecidability.TM
  Require Import SBTM.

From Undecidability.TM
  Require Export PCTM.

Import PCTMNotations SBTMNotations ListNotations.

Set Implicit Arguments.

Set Default Proof Using "Type".

#[local] Notation "i // s -1> t" := (pctm_sss i s t).
#[local] Notation "P // s -[ k ]-> t" := (sss_steps pctm_sss P k s t).
#[local] Notation "P // s ->> t" := (sss_compute pctm_sss P s t).
#[local] Notation "P // s -+> t" := (sss_progress pctm_sss P s t).

Section PC_based_Turing_Machine.

  Implicit Type P : (nat*list pctm_instr)%type.

  Tactic Notation "mydiscr" := 
    match goal with H: ?x = _, G : ?x = _ |- _ => rewrite H in G; discriminate end.

  Tactic Notation "myinj" := 
    match goal with H: ?x = _, G : ?x = _ |- _ => rewrite H in G; inversion G; subst; auto end.      
  
  (* pctm_sss is a functional relation *)
      
  Fact pctm_sss_fun ρ s t1 t2 : ρ // s -1> t1 -> ρ // s -1> t2 -> t1 = t2.
  Proof. intros []; subst; inversion 1; subst; auto; try mydiscr; myinj. Qed.

  (* pctm_sss is an informativelly total relation *) 
  
  Fact pctm_sss_total ρ s : { s' | ρ // s -1> s' }.
  Proof.
    destruct s as (i,t).
    destruct ρ as [ d | b | j | j ].
    + exists (1+i,mv d t); constructor.
    + destruct t as ((l,x),r).
      exists (1+i,(l,b,r)); constructor.
    + destruct t as ((l,b),r).
      exists (if b then 1+i else j,(l,b,r)); constructor.
    + exists (j,t); constructor.
  Qed. 

  Fact pctm_sss_total' ρ s : exists s', ρ // s -1> s'.
  Proof. destruct (pctm_sss_total ρ s); firstorder. Qed.

  Tactic Notation "solve" "progress" :=
    let H := fresh 
    in intros H;
       apply sss_progress_compute_trans;
       apply subcode_sss_progress with (1 := H);
       exists 1; split; auto; apply sss_steps_1;
       apply in_sss_step with (l := nil); [ simpl; lia | ];
       try (constructor; auto).

  Fact pctm_progress_MV P i d t st :
         (i,[MV d]) <sc P
      -> P // (1+i,mv d t) ->> st
      -> P // (i,t) -+> st.
  Proof. solve progress. Qed.

  Fact pctm_progress_WR P i b t st :
         (i,[WR b]) <sc P
      -> P // (1+i,wr t b) ->> st
      -> P // (i,t) -+> st.
  Proof. solve progress. Qed.

  Fact pctm_progress_JZ P i j t st :
         (i,[JZ j]) <sc P
      -> P // (if rd t then 1+i else j,t) ->> st
      -> P // (i,t) -+> st.
  Proof. solve progress. Qed.

 Fact pctm_progress_JMP P i j t st :
         (i,[JMP j]) <sc P
      -> P // (j,t) ->> st
      -> P // (i,t) -+> st.
  Proof. solve progress. Qed.

  Hint Resolve pctm_progress_MV pctm_progress_WR 
               pctm_progress_JZ pctm_progress_JMP : core.

  Tactic Notation "solve" "compute" :=
    intros; apply sss_progress_compute; eauto.
 
  Fact pctm_compute_MV P i d t st :
         (i,[MV d]) <sc P
      -> P // (1+i,mv d t) ->> st
      -> P // (i,t) ->> st.
  Proof. solve compute. Qed.

  Fact pctm_compute_WR P i b t st :
         (i,[WR b]) <sc P
      -> P // (1+i,wr t b) ->> st
      -> P // (i,t) ->> st.
  Proof. solve compute. Qed.

  Fact pctm_compute_JZ P i j t st :
         (i,[JZ j]) <sc P
      -> P // (if rd t then 1+i else j,t) ->> st
      -> P // (i,t) ->> st.
  Proof. solve compute. Qed.

  Fact pctm_compute_JMP P i j t st :
         (i,[JMP j]) <sc P
      -> P // (j,t) ->> st
      -> P // (i,t) ->> st.
  Proof. solve compute. Qed.

End PC_based_Turing_Machine.

Tactic Notation "pctm" "sss" "MV" "with" uconstr(a) := 
  match goal with
    | |- _ // _ -+> _ => apply pctm_progress_MV with (d := a)
    | |- _ // _ ->> _ => apply pctm_compute_MV with (d := a)
  end; auto.

Tactic Notation "pctm" "sss" "WR" "with" uconstr(a) := 
  match goal with
    | |- _ // _ -+> _ => apply pctm_progress_WR with (b := a)
    | |- _ // _ ->> _ => apply pctm_compute_WR with (b := a)
  end; auto.

Tactic Notation "pctm" "sss" "JZ" "with" uconstr(a) := 
  match goal with
    | |- _ // _ -+> _ => apply pctm_progress_JZ with (j := a)
    | |- _ // _ ->> _ => apply pctm_compute_JZ with (j := a)
  end; auto.

Tactic Notation "pctm" "sss" "JMP" "with" uconstr(a) := 
  match goal with
    | |- _ // _ -+> _ => apply pctm_progress_JMP with (j := a)
    | |- _ // _ ->> _ => apply pctm_compute_JMP with (j := a)
  end; auto.

Tactic Notation "pctm" "sss" "stop" := exists 0; apply sss_steps_0; auto.

