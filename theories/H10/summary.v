(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Yannick Forster            [+]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [+] Affiliation Saarland Univ. *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* Summary file for "Hilbert's tenth problem in Coq" 
   by D. Larchey-Wendling and Y. Forster *)

Require Import Arith ZArith List.

From Undecidability.Shared.Libs.DLW
  Require Import utils_tac pos vec sss.

From Undecidability.Synthetic Require Import Undecidability.

Require Import Undecidability.TM.TM.

From Undecidability.PCP
  Require Import PCP PCP_undec HaltTM_1_to_PCPb.

From Undecidability.MinskyMachines
  Require Import MM PCPb_to_MM MUREC_MM.

From Undecidability.FRACTRAN
  Require Import FRACTRAN FRACTRAN_undec MM_FRACTRAN.

From Undecidability.H10 
  Require Import H10 FRACTRAN_DIO H10_undec H10Z H10Z_undec.

From Undecidability.H10.Dio 
  Require Import dio_logic dio_elem dio_single.

From Undecidability.MuRec
  Require Import recalg H10_to_MUREC_HALTING.

Import ReductionChainNotations UndecidabilityNotations.

Set Implicit Arguments.

Local Infix "∈" := In (at level 70).

(* This summary file gives pointers to the main definitions
   necessary to understand the reduction chain described
   in Theorem "Hilberts_Tenth_entire_chain" below as
   well as the extra reduction H10 ⪯ H10Z 

   Some definitions of problems are easy and short:
     - PCP, more precisely the Post correspondence problem for Boolean strings
     - FRACTRAN, more precisely, termination for FRACTRAN programs
     - H10(Z), solvability of a single Diophantine equation
         over nat (or Z)
   
   Some definitions of problems are easy but long:
     - Satisfaction for Diophantine logic
     - Satisfiability for lists of elementary Diophantine constraints
   
   Some definitions of problems are more complicated:
     - Halting for single tape Turing machines
     - Halting for Minsky machines
     - Termination for µ-recursive algorithms
*) 

(* Definition of many one reductions in the synthetic approach *)

About "⪯".
Print reduction.
Print reduces.

(* HaltTM n is halting for Turing machines with n tapes 
   Beware that the definition of Turing machines is NOT 
   straightforward. *)

Print HaltTM.
Print HaltsTM.
Print eval.

(* The Post correspondance problem for Boolean strings 
   This inductive definition is very straightforward *)

Print dPCPb.
Print dPCP.
Print stack.
Print card.
Print derivable.

(* The halting problem for n-counters Minsky machines 
   The definition is not straightforward *)

Print mm_instr.
Print MM_PROBLEM.
Print mm_sss.
Print sss_output.
Print sss_terminates.
Print MM_HALTING.

(* The halting problem for FRACTRAN programs 
   The definition is quite straightforward *)

Print FRACTRAN_PROBLEM.
Print fractran_step.       (* with l /F/ x → y *)
Print fractran_steps.
Print fractran_compute.
Print fractran_stop.
Print fractran_terminates. (* with notation l /F/ x ↓ *)
Print FRACTRAN_HALTING.

(* The satisfaction problem for Diophantine logic
   formulas. A long but relativelly straightforward
   definition *)

Print dio_op.
Print dio_formula.
Print de_op_sem.
Print df_op_sem.
Print df_pred.
Print DIO_LOGIC_SAT.

(* The satisfiability problem for list of elementary 
   Diophantine constraints. A quite simple definition *)

Print dio_op.
Print dio_elem_expr.
Print dio_constraint.
Print DIO_ELEM_PROBLEM.
Print de_op_sem.
Print dee_eval.
Print dc_eval.
Print DIO_ELEM_SAT.

(* The solvability of a single diophantine equation 
   with parameters. A quite direct definition. *)

Print dio_polynomial.
Print dio_single.
Print DIO_SINGLE_PROBLEM.
Print dp_eval.
Print dio_single_pred.
Print DIO_SINGLE_SAT.

(* The solvability of a single diophantine equation 
   with 0 parameters. A direct definition for the
   case of natural numbers, see below for relative integers *)

Print dio_polynomial.
Print pos.         (* The type of indices/positions from 0 to n-1 *)
Print Fin.t.
Print H10_PROBLEM. (* pos 0 is an empty type *)
Print dp_eval.
Print dio_single_pred.
Print H10.

(* The termination problem for µ-recursive algorithm.
   A not so trivial definition with a complex dependent
   inductive type for µ-rec algos with an empty vector
   of parameters. *)

Print recalg.  (* µ-rec algos with n parameters *) 
Print ra_rel.  (* the computes relation *)
Print MUREC_PROBLEM.
Print MUREC_HALTING.

(* The notation ⎩ ... ⪯ₘ ... ⪯ₘ ... ⎭ helps
   at typing reduction chains but is immediately
   unfolded *)

Theorem Hilberts_Tenth_entire_chain : 
  ⎩ HaltTM 1 ⪯ₘ 
    dPCPb ⪯ₘ 
    MM_HALTING ⪯ₘ 
    FRACTRAN_HALTING ⪯ₘ 
    DIO_LOGIC_SAT ⪯ₘ 
    DIO_ELEM_SAT ⪯ₘ 
    DIO_SINGLE_SAT ⪯ₘ 
    H10 ⪯ₘ 
    MUREC_HALTING ⪯ₘ 
    MM_HALTING ⎭.
Proof.
  msplit 8.
  + apply reduces_transitive with (1 := HaltTM_1_to_PCPb).
    exists id; exact PCPb_iff_dPCPb.PCPb_iff_dPCPb.
  + apply reduces_transitive with (2 := PCPb_MM_HALTING).
    exists id; intro; symmetry; apply PCPb_iff_dPCPb.PCPb_iff_dPCPb. 
  + apply MM_FRACTRAN_HALTING.
  + apply FRACTRAN_HALTING_DIO_LOGIC_SAT.
  + apply DIO_LOGIC_ELEM_SAT.
  + apply DIO_ELEM_SINGLE_SAT.
  + apply DIO_SINGLE_SAT_H10.
  + apply H10_MUREC_HALTING.
  + apply MUREC_MM_HALTING.
Qed.

Check Hilberts_Tenth_entire_chain.
(* We check no axioms are hidden in the proof, this takes quite some time *)
Print Assumptions Hilberts_Tenth_entire_chain.

Theorem Hilberts_Tenth_from_PCP : dPCPb ⪯ H10.
Proof.
  do 6 (eapply reduces_transitive; [ apply Hilberts_Tenth_entire_chain | ]).
  apply reduces_reflexive.
Qed.

(* The solvability of a single diophantine equation 
   with 0 parameters. A direct definition for the
   case of relative integers *)

Print H10Z.dio_polynomial.
Print H10Z_PROBLEM. (* pos 0 is an empty type *)
Print H10Z.dp_eval.
Print H10Z.

Check H10_H10Z.
(* We check no axioms are hidden in the proof, this takes quite some time *)
Print Assumptions H10_H10Z.


 
