Require Export Undecidability.TM.Code.CodeTM Undecidability.TM.Code.ChangeAlphabet.
Require Export Undecidability.TM.Compound.TMTac.
Require Export Undecidability.TM.Basic.Mono Undecidability.TM.Compound.Multi.
(* the above imports sidestep the import of ProgrammingTools below to avoid the dependency on Hoare *)
(*From Undecidability.TM Require Import ProgrammingTools.*)

From Undecidability Require Import TM.Util.VectorPrelim.

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

Definition isNilBlank {sig : Type} (s : sigTape sig) : bool :=
  match s with
    NilBlank => true
  | _ => false
  end.

Definition isLeftBlank {sig : Type} (s : sigTape sig) : bool :=
  match s with
  | LeftBlank _  => true
  | _ => false
  end.

Definition isVoidBlank {sig : Type} (s : sigTape sig) : bool :=
  match s with
  | RightBlank _ => true
  | _ => false
  end.

Definition isSymbol {sig : Type} (s : sigTape sig) : bool :=
  match s with
  | UnmarkedSymbol _ | MarkedSymbol _ => true
  | _ => false
  end.

Definition encode_tape (sig : Type) (t : tape sig) : list (sigTape sig) :=
  match t with
  | niltape _ => [NilBlank]
  | leftof r rs => LeftBlank true :: UnmarkedSymbol r :: map UnmarkedSymbol rs ++ [RightBlank false]
  | midtape ls m rs => LeftBlank false :: map UnmarkedSymbol (rev ls) ++ MarkedSymbol m :: map UnmarkedSymbol rs ++ [RightBlank false]
  | rightof l ls => LeftBlank false :: map UnmarkedSymbol (rev ls) ++ [UnmarkedSymbol l; RightBlank true]
  end.

#[global]
Instance Encode_tape (sig : Type) : codable (sigTape sig) (tape sig) :=
  {|
    encode := @encode_tape sig;
  |}.


(* Compute encode_tape (niltape nat). *)
(* Compute encode_tape (midtape [3;2;1] 4 [5;6;7]). *)
(* Compute encode_tape (leftof 1 [2;3]). *)
(* Compute encode_tape (rightof 3 [2;1]). *)

Definition encode_tapes (sig : Type) (n : nat) (t : tapes sig n) :=
  encode_list (@Encode_tape sig) (vector_to_list t).

Arguments encode_tapes {sig n}.


#[global]
Instance Encode_tapes (sig : Type) (n : nat) : codable (sigList (sigTape sig)) (tapes sig n) :=
  {|
    encode := @encode_tapes sig n;
  |}.


(* Compute encode_tapes [| niltape nat; midtape [3;2;1] 4 [5;6;7]; leftof 1 [2;3];rightof 3 [2;1] |]. *)

Lemma vector_cast_refl (X : Type) (n1 : nat) (H1 : n1 = n1) (v : Vector.t X n1) :
  Vector.cast v H1 = v.
Proof. induction v; cbn; f_equal; auto. Qed.

