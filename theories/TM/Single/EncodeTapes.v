From Undecidability Require Import ProgrammingTools.

From Undecidability Require Export PrettyBounds.SizeBounds.

From Undecidability Require Import TM.Util.VectorPrelim.


Inductive sigTape (sig : Type) : Type :=
| LeftBlank (marked : bool)
| RightBlank (marked : bool)
| NilBlank (* always marked *)
| MarkedSymbol (s : sig)
| UnmarkedSymbol (s : sig).

Instance sigTape_eq (sig : Type) : eq_dec sig -> eq_dec (sigTape sig).
Proof. intros. hnf. decide equality; now apply Dec; auto. Defined.

Arguments LeftBlank {sig} marked.
Arguments RightBlank {sig} marked.
Arguments NilBlank {sig}.
Arguments MarkedSymbol {sig}.
Arguments UnmarkedSymbol {sig}.

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

Definition isRightBlank {sig : Type} (s : sigTape sig) : bool :=
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

Instance Encode_tape (sig : Type) : codable (sigTape sig) (tape sig) :=
  {|
    encode := @encode_tape sig;
  |}.


(* Compute encode_tape (niltape nat). *)
(* Compute encode_tape (midtape [3;2;1] 4 [5;6;7]). *)
(* Compute encode_tape (leftof 1 [2;3]). *)
(* Compute encode_tape (rightof 3 [2;1]). *)


(** Moving does not change the number of symbols. *)
Goal forall (sig : Type) (m : move) (t : tape sig), length (encode_tape (tape_move t m)) = length (encode_tape t).
Proof.
  intros.
  destruct m eqn:E1, t eqn:E2; cbn; auto.
  - now rewrite !app_length.
  - destruct l; cbn; auto. rewrite !app_length. f_equal. rewrite !map_length. cbn. rewrite !app_length. cbn. lia.
  - destruct l0; cbn; auto. rewrite !app_length. f_equal. rewrite !app_length. cbn. rewrite !map_length. cbn. rewrite !app_length. cbn. lia.
Qed.
  



Definition encode_tapes (sig : Type) (n : nat) (t : tapes sig n) :=
  encode_list (@Encode_tape sig) (vector_to_list t).

Arguments encode_tapes {sig n}.


Instance Encode_tapes (sig : Type) (n : nat) : codable (sigList (sigTape sig)) (tapes sig n) :=
  {|
    encode := @encode_tapes sig n;
  |}.


(* Compute encode_tapes [| niltape nat; midtape [3;2;1] 4 [5;6;7]; leftof 1 [2;3];rightof 3 [2;1] |]. *)


Fixpoint split_vector {X : Type} {n : nat} (v : Vector.t X n) (k : nat) : Vector.t X (min k n) * Vector.t X (n-k).
Proof.
  destruct k as [ | k']; cbn.
  - split. apply Vector.nil.
    eapply Vector.cast. apply v. abstract lia.
  - destruct v as [ | x n' v']; cbn.
    + split. apply Vector.nil. apply Vector.nil.
    + specialize (split_vector X n' v' k') as (rec1&rec2).
      split. apply Vector.cons. apply x. apply rec1. apply rec2.
Defined.


Lemma vector_cast_refl (X : Type) (n1 : nat) (H1 : n1 = n1) (v : Vector.t X n1) :
  Vector.cast v H1 = v.
Proof. induction v; cbn; f_equal; auto. Qed.

Lemma vector_cast_ext (X : Type) (m n : nat) (H1 H2 : n = m) (v : Vector.t X n) :
  Vector.cast v H1 = Vector.cast v H2.
Proof.
  revert H1 H2. revert m. induction v as [ | x n v IH]; intros.
  - cbn. destruct m. reflexivity. congruence.
  - cbn. destruct m. congruence. f_equal. auto.
Qed.

Lemma vector_cast_2 (X : Type) (n m : nat) (H1 : n = m) (H2 : m = n) (v : Vector.t X n) :
  Vector.cast (Vector.cast v H1) H2 = v.
Proof.
  revert H2 H1. revert m. induction v as [ | x n v IH]; intros.
  - cbn. destruct m; cbn. reflexivity. congruence.
  - cbn. destruct m; cbn. congruence. f_equal. auto.
Qed.


Lemma split_vector_correct (X : Type) (n : nat) (v : Vector.t X n) (k : nat) (H : min k n + (n-k) = n) :
  Vector.cast (Vector.append (fst (split_vector v k)) (snd (split_vector v k))) H = v.
Proof.
  revert n v H. induction k as [ | k IH]; intros; cbn.
  - destruct v; cbn; f_equal. apply vector_cast_2.
  - revert k H IH. destruct v as [ | x n v]; intros.
    + cbn. reflexivity.
    + cbn. specialize (IH _ v (f_equal Init.Nat.pred H)). destruct (split_vector v k) as [rec1 rec2] eqn:E. cbn in *. f_equal. auto.
Qed.

Lemma split_nat (n k : nat) : min k n + (n-k) = n.
Proof.
  revert n. induction k as [ | ? IH]; intros; cbn.
  - lia.
  - destruct n; cbn; f_equal; auto.
Qed.
  

(* Compute split_vector [| 1; 2; 3; 4 |] 1. *)
(* Compute let (x,y) := split_vector [| 1; 2; 3; 4 |] 1 in Vector.append x y. *)


Lemma sizeOfTape_encodeTape sig' (t : tape sig') :
| encode_tape t | = let l := sizeOfTape t in if 0 =? l then 1 else 2 + sizeOfTape t.
Proof.
  destruct t;cbn - [Nat.eqb].
  all:repeat (autorewrite with list;cbn [length]).
  1:easy.
  2,3:rewrite !Nat.add_succ_r. all:cbn [Nat.eqb]. all:Lia.nia.
Qed.


Lemma sizeOfTape_encodeTape_le sig' (t : tape sig') :
| encode_tape t | <= 2 + sizeOfTape t.
Proof.
  rewrite sizeOfTape_encodeTape. cbn;destruct _;Lia.nia.
Qed.
