(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* Certified Undecidability of Intuitionistic Linear Logic via Binary Stack Machines and Minsky Machines. Yannick Forster and Dominique Larchey-Wendling. CPP '19. http://uds-psl.github.io/ill-undecidability/ *)

Require Import List Arith Relations.

Set Implicit Arguments.

Section self_contained_mm2.

  (** Two counters Minsky machines. Counters are named A and B

      For instructions: INC{A,B} | DEC{A,B} j 

      j is a conditional jump PC index which occurs
      when the counter has non-zero value 
  *)

  Inductive mm2_instr : Set :=
    | mm2_inc_a : mm2_instr
    | mm2_inc_b : mm2_instr
    | mm2_dec_a : nat -> mm2_instr
    | mm2_dec_b : nat -> mm2_instr.

  Reserved Notation "i '//' r '⇢' s" (at level 70, no associativity).
  Reserved Notation "P '//' r '→' s" (at level 70, no associativity).
  Reserved Notation "P '//' r '↠' s" (at level 70, no associativity).
  Reserved Notation "P '//' r ↓" (at level 70, no associativity).

  Notation mm2_state := (nat*(nat*nat))%type.

  (** Instruction step semantics:

      ρ // x ⇢ y : instruction ρ transforms state x into state y 

      Notice that the jump occurs on the non-zero case when DEC

   *)

  Inductive mm2_atom : mm2_instr -> mm2_state -> mm2_state -> Prop :=
    | in_mm2s_inc_a  : forall i   a b, mm2_inc_a   // (i,(  a,  b)) ⇢ (1+i,(S a,  b))
    | in_mm2s_inc_b  : forall i   a b, mm2_inc_b   // (i,(  a,  b)) ⇢ (1+i,(  a,S b))
    | in_mm2s_dec_aS : forall i j a b, mm2_dec_a j // (i,(S a,  b)) ⇢ (  j,(  a,  b))
    | in_mm2s_dec_bS : forall i j a b, mm2_dec_b j // (i,(  a,S b)) ⇢ (  j,(  a,  b))
    | in_mm2s_dec_a0 : forall i j   b, mm2_dec_a j // (i,(  0,  b)) ⇢ (1+i,(  0,  b))
    | in_mm2s_dec_b0 : forall i j a,   mm2_dec_b j // (i,(  a,  0)) ⇢ (1+i,(  a,  0))
  where "ρ // x ⇢ y" := (mm2_atom ρ x y).

  (** instruction ρ occurs at PC index i in the program (1,P) *)

  Definition mm2_instr_at (ρ : mm2_instr) i P := exists l r, P = l++ρ::r /\ 1+length l = i.

  (** Program step semantics:

      program P with first instruction at PC index 1 transforms 
      state x into state y in one step, using instruction a PC index (fst x) *)

  Definition mm2_step P x y := exists ρ, mm2_instr_at ρ (fst x) P /\ ρ // x ⇢ y.

  Notation "P // x → y" := (mm2_step P x y).
 
  (** Halting condition: program P cannot progress anymore *)

  Definition mm2_stop P s := forall s', ~ P // s → s'.

  (** reflexive and transitive closure of program step semantics *)

  Notation "P // x ↠ y" := (clos_refl_trans _ (mm2_step P) x y).

  Definition mm2_terminates P s := exists s', P // s ↠ s' /\ mm2_stop P s'.

  Notation "P // s ↓" := (mm2_terminates P s).

  Definition MM2_PROBLEM := (list mm2_instr * nat * nat)%type.

  Definition MM2_HALTING (P : MM2_PROBLEM) := 
    match P with (P,a,b) => P // (1,(a,b)) ↓ end.

  Definition MM2_HALTS_ON_ZERO (P : MM2_PROBLEM) := 
    match P with (P,a,b) => P // (1,(a,b)) ↠ (0,(0,0)) end.

End self_contained_mm2.

