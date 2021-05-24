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

(* Standalone file for "Hilbert's tenth problem in Coq" 
   by D. Larchey-Wendling and Y. Forster 

   Herein we present a standalone version of the many-one
   reduction from Boolean PCP (BPCP) to H10 over N (H10nat).

            BPCP ⪯ₘ H10nat

   Both BPCP and H10nat are straightforward to implement, 
   as explained below. The library versions dBPCb and H10 may 
   be more elaborate because they need to cover more use cases 
   than just this result. Of course the proof of the reduction 
   itself is not trivial at all and in here we only provide
   the reductions easy BPCPd ⪯ₘ dPCPb and H10 ⪯ₘ H10nat
   as translation layers, and otherwise use the reduction
   chain dPCPb ⪯ₘ .... ⪯ₘ H10 from summary.v for the 
   hard part.

   We also give a standalone definition of many-one reductions
   and show that it matches exactly the library definition.

   Notice that we do not have such "straightforward" definitions
   for Turing machines or Minsky machines or µ-recursive functions.

   We think the two problems BPCP and H10nat are critical/central
   enough to show that we do not hide anything under the carpet
   of deeply nested definitions. The command "Print Assumptions"
   checks that no axioms or missing proofs or proof holes are 
   involved.

   The purist might notice that we still assume some
   definitions from the Bool, Arith and List modules
   of the Standard Library of Coq, which we take for 
   granted instead of reproducing them here:

   Bool: bool
   Arith: "nat", "plus/+" and "mult/*"
   List: "list", "In/∈" and "app/++" 

   If you are unfamiliar with those, then BPCP and H10nat 
   might not be so straightforward after all...

*)

Require Import Arith List Lia.

From Undecidability.Shared.Libs.DLW   Require Import utils_tac pos.
From Undecidability.Synthetic         Require Import Undecidability.
From Undecidability.PCP               Require Import PCP.
From Undecidability.H10               Require Import dio_logic dio_single H10 summary.

Set Implicit Arguments.

Local Infix "∈" := In (at level 70). (* List membership as defined in StdLib *)

(* A standalone definition of Boolean PCP *)

Local Reserved Notation "R ⊳ u ∕ l" (at level 70, format "R  ⊳  u ∕ l").

Inductive BPCP_derive (R : list (list bool * list bool)) : list bool -> list bool -> Prop :=
  | in_BPCP_0 : forall p q, (p,q) ∈ R -> R ⊳ p∕q
  | in_BPCP_1 : forall p q u l, (p,q) ∈ R -> R ⊳ u∕l -> R ⊳ (p++u)∕(q++l)
where "R ⊳ u ∕ l" := (BPCP_derive R u l).

Definition BPCP R := exists s, R ⊳ s∕s.

Section dPCPb_BPCP.

  (* The reduction/equivalence between:
       - dBPCPd from the library 
       - the above standalone BPCP defined above 

     You do not need to understand that (small) proof *)

  Variable R : list (list bool * list bool).

  Local Fact derive_BPCP_derive u l : derivable R u l <-> R ⊳ u∕l.
  Proof. split; (induction 1; [ constructor 1 | constructor 2 ]; auto). Qed.

  Local Fact dPCPb_BPCP : dPCPb R <-> BPCP R.
  Proof. split; intros (s & ?); exists s; now apply derive_BPCP_derive. Qed.

End dPCPb_BPCP.

(* A standalone definition of H10nat as a single polynomial
   equation p = q where unknowns range over an enumerable 
   type (eg nat) and interpreted over natural numbers. 
   There are no parameters, only unknowns *)

Notation U := nat. (* Type of unknowns *)

Inductive poly : Set :=
  | poly_unk : U -> poly
  | poly_cst : nat -> poly
  | poly_add : poly -> poly -> poly
  | poly_mul : poly -> poly -> poly.

Local Notation "£ x" := (poly_unk x) (at level 1, format "£ x").
Local Notation "⌞ c ⌟" := (poly_cst c) (at level 1, format "⌞ c ⌟").
Local Infix "⊕" := poly_add (at level 50, left associativity).
Local Infix "⊗" := poly_mul (at level 48, left associativity).

Local Reserved Notation "⟦ p ⟧ φ" (at level 40, format "⟦ p ⟧  φ").

Fixpoint poly_eval (φ : U -> nat) p :=
  match p with
    | £x  => φ x
    | ⌞c⌟ => c
    | p⊕q => ⟦p⟧ φ + ⟦q⟧ φ
    | p⊗q => ⟦p⟧ φ * ⟦q⟧ φ
  end
where "⟦ p ⟧ φ" := (poly_eval φ p).

(* A polynomial equation e : p = q is a pair (p,q) of poly *)
Definition H10nat (e : poly*poly) := let (p,q) := e in exists φ, ⟦p⟧ φ = ⟦q⟧ φ.

Section H10_H10nat.

  (* The reduction from 
       - H10 as defined in the library, unknowns ranging over pos n
         and parameters over the empty type pos 0
       - H10nat as defined above, unknows ranging over U/nat 
         and without parameters *)

  Section dp2p.
 
    Variable (n : nat).

    Local Fixpoint dp2p (p : dio_polynomial (pos n) (pos 0)) : poly :=
      match p with
        | dp_nat c => ⌞c⌟
        | dp_var x => £(pos2nat x)
        | dp_par a => pos_O_invert _ a
        | dp_comp do_add p q => dp2p p ⊕ dp2p q
        | dp_comp do_mul p q => dp2p p ⊗ dp2p q
      end.

    Variable (φ : pos n -> nat) (ψ : U -> nat).

    Local Definition valuations_match := forall x, φ x = ψ (pos2nat x).

    Hypothesis Hφψ : valuations_match. 

    Fact dp2p_spec p ν : dp_eval φ ν p = ⟦dp2p p⟧ ψ.
    Proof.
      induction p as [ | | a | [] ]; simpl; auto.
      invert pos a.
    Qed.

  End dp2p.

  Local Fact H10_H10nat : H10 ⪯ H10nat.
  Proof.
    apply reduces_dependent; exists.
    intros (n,(p,q)).
    exists (dp2p p,dp2p q); simpl.
    split.
    + intros (phi & Hphi). 
      set (psi i := match le_lt_dec n i with left _ => 0 | right H => phi (nat2pos H) end).
      assert (Hpsi : valuations_match phi psi).
      { intro x; unfold psi.
        generalize (pos2nat_prop x); intros Hx.
        destruct (le_lt_dec n (pos2nat x)) as [ H | H ]; try lia.
        f_equal; symmetry; apply nat2pos_pos2nat. }
      exists psi.
      eq goal Hphi; f_equal; apply dp2p_spec; auto.
    + intros (psi & Hpsi).
      exists (fun x => psi (pos2nat x)).
      eq goal Hpsi; f_equal; symmetry; apply dp2p_spec; red; simpl; auto.
  Qed.

End H10_H10nat.

(* The same definition as the library but with the definition of reduction inlined *)
Local Definition many_one_reduces X Y (P : X -> Prop) (Q : Y -> Prop) :=
  exists f : X -> Y, forall x, P x <-> Q (f x).

(* And indeed they are the same *)
Goal many_one_reduces = @reduces. 
Proof. reflexivity. Qed.

Local Infix "⪯ₘ" := many_one_reduces (at level 70).

Theorem BPCP_many_one_reduces_to_H10nat : BPCP ⪯ₘ H10nat.
Proof.
  change (BPCP ⪯ H10nat).
  eapply reduces_transitive with (Q := dPCPb).
  1: { exists id; intro; symmetry; apply dPCPb_BPCP. }
  do 6 (eapply reduces_transitive; [ apply Hilberts_Tenth_entire_chain | ]).
  apply H10_H10nat.
Qed.

Check BPCP_many_one_reduces_to_H10nat.
(* We check no axioms are hidden in the proof, this takes quite some time *)
Print Assumptions BPCP_many_one_reduces_to_H10nat.

 
