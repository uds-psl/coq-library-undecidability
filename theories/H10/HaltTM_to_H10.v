Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.TM.Halting.
Require Import Undecidability.H10.H10.

Require Import Undecidability.H10.HaltTM_to_FRACTRAN_HALTING.
Require Import Undecidability.H10.FRACTRAN_DIO.

(** Many-one reduction from Turing machine halting to Hilbert's tenth problem *)
Lemma HaltTM_to_H10 : HaltTM 1 ⪯ H10.
Proof.
  apply (reduces_transitive HaltTM_to_FRACTRAN_HALTING).
  apply (reduces_transitive FRACTRAN_HALTING_DIO_LOGIC_SAT).
  apply (reduces_transitive DIO_LOGIC_ELEM_SAT).
  apply (reduces_transitive DIO_ELEM_SINGLE_SAT).
  exact DIO_SINGLE_SAT_H10.
Qed.

(* 
  reduction chain as described in
    Dominique Larchey-Wendling, Yannick Forster:
    Hilbert's Tenth Problem in Coq. FSCD 2019: 27:1-27:20 
*)
Require Import Undecidability.PCP.PCP.
Require Import Undecidability.ILL.Mm.mm_defs.
Require Import Undecidability.H10.Fractran.fractran_defs.
Require Import Undecidability.PCP.Reductions.HaltTM_to_PCP.
Require Import Undecidability.ILL.UNDEC.
Require Import Undecidability.H10.MM_FRACTRAN.

Theorem Hilberts_Tenth : 
  HaltTM 1 ⪯ PCP
  /\ PCP ⪯ MM_HALTING
  /\ MM_HALTING ⪯ FRACTRAN_HALTING
  /\ FRACTRAN_HALTING ⪯ DIO_LOGIC_SAT	
  /\ DIO_LOGIC_SAT ⪯ DIO_ELEM_SAT	
  /\ DIO_ELEM_SAT ⪯ DIO_SINGLE_SAT	
  /\ DIO_SINGLE_SAT ⪯ H10.	
Proof.
  split; [exact HaltTM_to_PCP | ].
  split; [exact PCP_MM_HALTING | ].
  split; [exact MM_FRACTRAN_HALTING | ].
  split; [exact FRACTRAN_HALTING_DIO_LOGIC_SAT | ].
  split; [exact DIO_LOGIC_ELEM_SAT | ].
  split; [exact DIO_ELEM_SINGLE_SAT | ].
  exact DIO_SINGLE_SAT_H10.
Qed.
