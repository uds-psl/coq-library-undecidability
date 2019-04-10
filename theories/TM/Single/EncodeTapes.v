Require Import ProgrammingTools.



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


Compute encode_tape (niltape nat).
Compute encode_tape (midtape [3;2;1] 4 [5;6;7]).
Compute encode_tape (leftof 1 [2;3]).
Compute encode_tape (rightof 3 [2;1]).


(** Moving does not change the number of symbols. *)
Goal forall (sig : Type) (m : move) (t : tape sig), length (encode_tape (tape_move t m)) = length (encode_tape t).
Proof.
  intros.
  destruct m eqn:E1, t eqn:E2; cbn; auto.
  - now rewrite !app_length.
  - destruct l; cbn; auto. rewrite !app_length. f_equal. rewrite !map_length. cbn. rewrite !app_length. cbn. omega.
  - destruct l0; cbn; auto. rewrite !app_length. f_equal. rewrite !app_length. cbn. rewrite !map_length. cbn. rewrite !app_length. cbn. omega.
Qed.
  


(* We encode a vector of tapes simply as a list of tapes *)

Fixpoint vector_to_list (X : Type) (n : nat) (v : Vector.t X n) : list X :=
  match v with
  | Vector.nil _ => List.nil
  | Vector.cons _ x n v' => x :: vector_to_list v'
  end.


Lemma vector_to_list_correct (X : Type) (n : nat) (v : Vector.t X n) :
  vector_to_list v = Vector.to_list v.
Proof.
  induction v.
  - cbn. auto.
  - cbn. f_equal. auto.
Qed.

Lemma vector_to_list_length (X : Type) (n : nat) (v : Vector.t X n) :
  length (vector_to_list v) = n.
Proof.
  induction v.
  - cbn. auto.
  - cbn. f_equal. auto.
Qed.


Lemma vector_to_list_map (X Y : Type) (f : X -> Y) (n : nat) (v : Vector.t X n) :
  map f (vector_to_list v) = vector_to_list (Vector.map f v).
  induction v.
  - cbn. auto.
  - cbn. f_equal. auto.
Qed.

Lemma vector_to_list_cast (X : Type) (n1 n2 : nat) (H : n1 = n2) (v : Vector.t X n1) :
  vector_to_list (Vector.cast v H) = vector_to_list v.
Proof. subst. rename n2 into n. induction v as [ | x n v IH]; cbn; f_equal; auto. Qed.

Lemma vector_to_list_eta (X : Type) (n : nat) (v : Vector.t X (S n)) :
  Vector.hd v :: vector_to_list (Vector.tl v) = vector_to_list v.
Proof. destruct_vector. cbn. reflexivity. Qed.

Lemma vector_to_list_map2_eta (X Y Z : Type) (n : nat) (f : X -> Y -> Z) (xs : Vector.t X (S n)) (ys : Vector.t Y (S n)) :
  f (Vector.hd xs) (Vector.hd ys) :: vector_to_list (Vector.map2 f (Vector.tl xs) (Vector.tl ys)) =
  vector_to_list (Vector.map2 f xs ys).
Proof. now destruct_vector. Qed.
  

Definition encode_tapes (sig : Type) (n : nat) (t : tapes sig n) :=
  encode_list (@Encode_tape sig) (vector_to_list t).

Arguments encode_tapes {sig n}.


Instance Encode_tapes (sig : Type) (n : nat) : codable (sigList (sigTape sig)) (tapes sig n) :=
  {|
    encode := @encode_tapes sig n;
  |}.


Compute encode_tapes [| niltape nat; midtape [3;2;1] 4 [5;6;7]; leftof 1 [2;3];rightof 3 [2;1] |].


Fixpoint split_vector {X : Type} {n : nat} (v : Vector.t X n) (k : nat) : Vector.t X (min k n) * Vector.t X (n-k).
Proof.
  destruct k as [ | k']; cbn.
  - split. apply Vector.nil.
    eapply Vector.cast. apply v. abstract omega.
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
  - omega.
  - destruct n; cbn; f_equal; auto.
Qed.
  

Compute split_vector [| 1; 2; 3; 4 |] 1.
Compute let (x,y) := split_vector [| 1; 2; 3; 4 |] 1 in Vector.append x y.
