
From Undecidability.TM Require Export Util.Prelim Util.TM_facts.
Require Export Undecidability.TM.Compound.TMTac.
Require Import Undecidability.TM.Code.Code.
Require Export Undecidability.TM.Basic.Mono Undecidability.TM.Compound.Multi.
(* the above imports sidestep the import of ProgrammingTools below to avoid the dependency on Hoare *)
(*From Undecidability.TM Require Import ProgrammingTools.*)

Set Default Goal Selector "!".

(* We add these three symbols the alphabets of every machine. [START] is the first symbol of the encoding and [STOP] is always the right-most symbol. [UNKNOWN] is always ignored (it serves as the default symbol for the alphabet-lift, see [ChangeAlphabet]). *)
Inductive boundary : Type :=
| START   : boundary
| STOP    : boundary
| UNKNOWN : boundary.

(* Declare discreteness of [boundary] *)
#[global]
Instance boundary_eq : eq_dec boundary.
Proof. unfold dec. decide equality. Defined. (* because definition *)

(* Declare finiteness of [boundary] *)
#[global]
Instance boundary_fin : finTypeC (EqType boundary).
Proof. split with (enum := [START; STOP; UNKNOWN]). cbn. intros []; cbn; reflexivity. Defined. (* because definition *)

(* Because every machine is defined on an alphabet [Σ^+], the notation adds the discreteness and finiteness constructors, to cast [Σ^+ : finType]. *)
Notation "sig '^+'" := (FinType (EqType (boundary + sig) % type)) (at level 0) : type_scope.

Inductive sigTape (sig : Type) : Type :=
| LeftBlank (marked : bool)
| RightBlank (marked : bool)
| NilBlank (* always marked *)
| MarkedSymbol (s : sig)
| UnmarkedSymbol (s : sig).

#[global]
Instance sigTape_eq (sig : Type) : eq_dec sig -> eq_dec (sigTape sig).
Proof. intros. hnf. decide equality; now apply Dec; auto. Defined. (* because definition *)

Arguments LeftBlank {sig} marked.
Arguments RightBlank {sig} marked.
Arguments NilBlank {sig}.
Arguments MarkedSymbol {sig}.
Arguments UnmarkedSymbol {sig}.

#[global]
Instance sigTape_fin (sig : finType) : finTypeC (EqType (sigTape sig)).
Proof.
  split with (enum := LeftBlank true :: LeftBlank false :: RightBlank true :: RightBlank false :: NilBlank ::
                                map MarkedSymbol enum ++ map UnmarkedSymbol enum).
  intros [ [ | ] | [ | ] | | | ]; cbn; auto.
  1-5: f_equal. 1-5: now rewrite <- countSplit, !countMap_zero.
  - rewrite <- countSplit. rewrite countMap_injective, countMap_zero by congruence. now rewrite enum_ok.
  - rewrite <- countSplit. rewrite countMap_injective, countMap_zero by congruence. now rewrite enum_ok.
Qed.

Definition isMarked (sig : Type) (s : sigTape sig) : bool :=
  match s with
  | LeftBlank marked => marked
  | RightBlank marked => marked
  | NilBlank => true
  | MarkedSymbol _ => true
  | UnmarkedSymbol _ => false
  end.

Definition encode_tape (sig : Type) (t : tape sig) : list (sigTape sig) :=
  match t with
  | niltape _ => [NilBlank]
  | leftof r rs => LeftBlank true :: UnmarkedSymbol r :: map UnmarkedSymbol rs ++ [RightBlank false]
  | midtape ls m rs => LeftBlank false :: map UnmarkedSymbol (rev ls) ++ MarkedSymbol m :: map UnmarkedSymbol rs ++ [RightBlank false]
  | rightof l ls => LeftBlank false :: map UnmarkedSymbol (rev ls) ++ [UnmarkedSymbol l; RightBlank true]
  end.

Definition encode_tapes (sig : Type) (n : nat) (t : tapes sig n) :=
  encode_list (@encode_tape sig) (Vector.to_list t).

Arguments encode_tapes {sig n}.

(* Compute encode_tapes [| niltape nat; midtape [3;2;1] 4 [5;6;7]; leftof 1 [2;3];rightof 3 [2;1] |]. *)

Lemma vector_cast_refl (X : Type) (n1 : nat) (H1 : n1 = n1) (v : Vector.t X n1) :
  Vector.cast v H1 = v.
Proof. induction v; cbn; f_equal; auto. Qed.
