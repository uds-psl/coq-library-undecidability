(*************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(*************************************************************)

Require Import List Permutation.

From Undecidability.Shared.Libs.DLW 
  Require Import utils.

From Undecidability.ILL Require Import ILL CLL.

Set Implicit Arguments.

Section mapping_ill_to_cll.

  (* Syntatic translations from/to ILL and CLL formulas *)

  Reserved Notation "[ f ]" (at level 1).
  Reserved Notation "⟨ f ⟩" (at level 1).

  Fixpoint ill_cll f :=
    match f with
      | ill_var v  => cll_var v
      | ill_cst ill_bot => cll_cst cll_bot
      | ill_cst ill_top => cll_cst cll_top
      | ill_cst ill_1   => cll_cst cll_1
      | ill_ban f => cll_una cll_bang [f]
      | ill_bin ill_times f g => cll_bin cll_times [f] [g]
      | ill_bin ill_with f g => cll_bin cll_with [f] [g]
      | ill_bin ill_plus f g => cll_bin cll_plus [f] [g]
      | ill_bin ill_limp f g => cll_bin cll_limp [f] [g]
    end
  where "[ f ]" := (ill_cll f).

  Fixpoint cll_ill f :=
    match f with
      | cll_var v => ill_var v
      | cll_cst cll_bot => ill_cst ill_bot
      | cll_cst cll_top => ill_cst ill_top
      | cll_cst cll_1 => ill_cst ill_1
      | cll_una cll_bang f => ill_ban ⟨f⟩
      | cll_bin cll_times f g => ill_bin ill_times ⟨f⟩ ⟨g⟩
      | cll_bin cll_with  f g => ill_bin ill_with ⟨f⟩ ⟨g⟩
      | cll_bin cll_plus  f g => ill_bin ill_plus ⟨f⟩ ⟨g⟩
      | cll_bin cll_limp  f g => ill_bin ill_limp ⟨f⟩ ⟨g⟩
      | _ => ill_cst ill_bot  (* arbitrary value *)
    end
  where "⟨ f ⟩" := (cll_ill f).

  Fixpoint from_ill f := 
    match f with
      | cll_var _ => True
      | cll_cst cll_bot => True
      | cll_cst cll_top => True
      | cll_cst cll_1 => True
      | cll_una cll_bang f => from_ill f
      | cll_bin cll_times f g => from_ill f /\ from_ill g
      | cll_bin cll_with  f g => from_ill f /\ from_ill g
      | cll_bin cll_plus  f g => from_ill f /\ from_ill g
      | cll_bin cll_limp  f g => from_ill f /\ from_ill g
      | _ => False
    end.

  Fact ill_cll_ill f : ⟨[f]⟩ = f.
  Proof. induction f as [ | [] | | [] ]; simpl; f_equal; auto. Qed.

  Fact cll_ill_cll f : from_ill f -> [⟨f⟩] = f.
  Proof.
    induction f as [ | [] | [] | [] ]; simpl; try tauto; intros; f_equal; tauto.
  Qed.

  Fact ill_cll_from_ill f : from_ill [f].
  Proof. induction f as [ | [] | | [] ]; simpl; tauto. Qed. 

  Fixpoint cll_has_bot_zero_neg f := 
    match f with
      | cll_var _ => False
      | cll_cst c => c = cll_bot \/ c = cll_0
      | cll_una m f => m = cll_neg \/ cll_has_bot_zero_neg f
      | cll_bin _ f g => cll_has_bot_zero_neg f \/ cll_has_bot_zero_neg g
    end.

  Fixpoint ill_has_bot f := 
    match f with
      | ill_var _ => False
      | ill_cst ill_bot => True
      | ill_ban f => ill_has_bot f
      | ill_bin _ f g => ill_has_bot f \/ ill_has_bot g
      | _ => False
    end.

  Fact cll_ill_has_bot f : cll_has_bot_zero_neg f -> ill_has_bot ⟨f⟩.
  Proof. 
    induction f as  [ | [] | [] | [] ]; simpl; try tauto.
    all: intros []; auto; discriminate. 
  Qed.

  Fact ill_cll_has_bot f : ill_has_bot f -> cll_has_bot_zero_neg [f].
  Proof. induction f as [ | [] | | [] ]; simpl; tauto. Qed.

  Fact ill_cll_has_bot_eq f : ill_has_bot f <-> cll_has_bot_zero_neg [f].
  Proof.
    split.
    + apply ill_cll_has_bot.
    + intros H.
      apply cll_ill_has_bot in H.
      now rewrite ill_cll_ill in H.
  Qed.

End mapping_ill_to_cll.

(* Some basic commutativity lemmas for the ILL <-> CLL translations over lists *)

Notation "[ f ]" := (ill_cll f).
Notation "⟨ f ⟩" := (cll_ill f).

Notation "⟦ Γ ⟧" := (map ill_cll Γ).
Notation "⟪ Γ ⟫" := (map cll_ill Γ).

Local Hint Resolve ill_cll_ill : core.

Fact ill_cll_ill_list Γ : ⟪⟦Γ⟧⟫ = Γ.
Proof. induction Γ; simpl; f_equal; auto. Qed.

Fact ill_cll_lbang Γ : ⟦map ill_ban Γ⟧ = ‼⟦Γ⟧.
Proof. induction Γ; simpl; f_equal; auto. Qed.

Fact cll_ill_lbang Γ : ⟪‼Γ⟫ = map ill_ban ⟪Γ⟫.
Proof. induction Γ; simpl; f_equal; auto. Qed.
