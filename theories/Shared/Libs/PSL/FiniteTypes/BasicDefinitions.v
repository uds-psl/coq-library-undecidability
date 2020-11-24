(* * Basic definitions of decidablility and Functions
- includes basic Lemmas about said functions 
 *)

From Undecidability.Shared.Libs.PSL Require Export Base.

(* * Definition of useful tactics *)

(* dec is used to destruct all decisions appearing in the goal or assumptions. *)
Ltac dec := repeat (destruct Dec).

(* This tactic completely solves listComplete goals for base types *)
Ltac listComplete := intros x; simpl; dec; destruct x; try congruence.
(* simplifies (decision x = x) *)
Ltac deq x := destruct (Dec (x=x)) as [[]  | isnotequal]; [> | contradict isnotequal; reflexivity] .



(* Function that takes two lists and returns the list of all pairs of elements from the two lists *)
Fixpoint prodLists {X Y: Type} (A: list X) (B: list Y) {struct A} :=
  match A with
  | nil => nil
  | cons x A' => map (fun y => (x,y)) B ++ prodLists A' B end.

(* Crossing any list with the empty list always yields the empty list *)
Lemma prod_nil (X Y: Type) (A: list X) :
  prodLists A ([]: list Y) = [].
Proof.
  induction A.
  - reflexivity.
  - cbn. assumption.
Qed.

(* This function takes a (A: list X) and yields a list (option X) which for every x in A contains Some x. The resultung list also contains None. The order is preserved. None is the first element of the resulting list. *)

Definition toOptionList {X: Type} (A: list X) :=
  None :: map (@Some _) A .

(* This function counts the number of occurences of an element in a given list and returns the result *)
Fixpoint count (X: Type) `{eq_dec X}  (A: list  X) (x:  X) {struct A} : nat :=
  match A with
  | nil => O
  | cons y A' =>  if Dec (x=y) then S(count A' x) else count A' x end.

Definition toSumList1 {X: Type}  (Y: Type) (A: list X): list (X + Y) :=
  map inl A.
Definition toSumList2 {Y: Type}  (X: Type) (A: list Y): list (X + Y) :=
  map inr A.

(* * Basic lemmas about functions *)

(* In the list containing all pairs of (x,y') with y' from a list B the pair (x,y) is contained exactly as many times as y is contained in the list B. *)

Lemma countMap (X Y: eqType) (x:X) (B: list Y) y :
  count ( map (fun y => (x,y)) B) (x, y) = count B y.
Proof.
  induction B.
  - reflexivity.
  - simpl. dec;  congruence.
Qed.

(* If a list is split somewhere in two list the number of occurences of an element in the list is equal to the sum of the number of occurences in the left and the right part. *)

Lemma countSplit (X: eqType) (A B: list X) (x: X)  : count A x + count B x = count (A ++ B) x.
Proof.
  induction A.
  - reflexivity.
  - cbn. decide (x=a).
    +cbn. f_equal; exact IHA.
    + exact IHA.
Qed.

(* In a list of tupels with x as a left element the number of tupels with something different from x as a left element is 0. *)
Lemma countMapZero  (X Y: eqType) (x x':X) (B: list Y) y : x' <> x -> count  ( map (fun y => (x,y)) B) (x', y) =0.
Proof.
  intros ineq. induction B.
  - reflexivity.
  -  simpl. dec.
     + inversion e; congruence.
     + exact IHB.
Qed.


Lemma notInZero (X: eqType) (x: X) A :
  not (x el A) <-> count A x = 0.
Proof.
  split; induction A.
  -  reflexivity.
  - intros H. cbn in *. dec.
    + exfalso. apply H. left. congruence.
    + apply IHA. intros F. apply H. now right.
  - tauto.
  - cbn. dec.
    + subst a. lia.
    + intros H [E | E].
      * now symmetry in E.
      * tauto.
Qed.

Lemma countIn (X:eqType) (x:X) A:
  count A x > 0 -> x el A.
Proof.
  induction A.
  - cbn. lia.
  - cbn.  dec.
    + intros. left. symmetry. exact e.
    + intros. right. apply IHA. exact H.
Qed.

Lemma InCount (X:eqType) (x:X) A:
  x el A -> count A x > 0.
Proof.
  induction A.
  - intros [].
  - intros [[] | E]; cbn.
    + deq a. lia.
    + specialize (IHA E). dec; lia.
Qed.

Lemma count_in_equiv (X: eqType) (x:X) A : count A x > 0 <-> x el A.
Proof.
  split.
  - apply countIn.
  - apply InCount.
Qed.


Lemma countApp (X: eqType) (x: X) (A B: list X) :
  count (A ++ x::B) x > 0.
Proof.
  auto using InCount.
Qed.


(*  Dupfree Lists containing every x countain x exactly once *)
Lemma dupfreeCount (X: eqType) (x:X) (A: list X) : dupfree A -> x el A -> count A x = 1.
Proof.
  intros D E. induction D.
  -  contradiction E.
  - cbn. dec.
    + f_equal. subst x0. now apply notInZero.
    + destruct E as [E | E]; [> congruence | auto].
Qed.        

(* toSumlist1 does not change the number of occurences of an existing element in the list *)
Lemma toSumList1_count (X: eqType) (x: X) (Y: eqType) (A: list X) :
  count (toSumList1 Y A) (inl x) =  count A x .
Proof.
  induction A; simpl; dec; congruence.  
Qed.

(* toSumlist2 odes not change the numbe of occurences of an existing element in the list *)
Lemma toSumList2_count (X Y: eqType) (y: Y) (A: list Y):
  count (toSumList2 X A) (inr y) = count A y.
Proof.
  induction A; simpl; dec; congruence.  
Qed.

(* to sumList1 does not produce inr proofs *)
Lemma toSumList1_missing (X Y: eqType) (y: Y) (A: list X):
  count (toSumList1 Y A ) (inr y) = 0.                           
Proof.
  induction A; dec; firstorder.
Qed.

(* toSumlist2 does not produce inl proofs *)
Lemma toSumList2_missing (X Y: eqType) (x: X) (A: list Y):
  count (toSumList2 X A ) (inl x) = 0.                           
Proof.
  induction A; dec; firstorder.
Qed.


(* * Cardinality Lemmas for lists*)
Lemma cons_incll (X: Type) (A B: list X) (x:X) : x::A <<= B -> A <<= B.
Proof.
  unfold "<<=". auto.
Qed.

Lemma card_length_leq (X: eqType) (A: list X) : card A <= length A.
Proof.
  induction A; auto. cbn. dec; lia.
Qed.

(* * Various helpful Lemmas *)


(* If the concatenation of two lists is nil then each list was nil *)
Lemma appendNil (X: Type) (A B: list X) :
  A ++ B = nil -> A = nil /\ B = nil.
Proof.
  intros H. assert (|A ++ B| = 0) by now rewrite H.
  rewrite app_length in H0. rewrite <- !length_zero_iff_nil. lia.
Qed.

Lemma countZero (X: eqType) (x: X) (A: list X) : count A x = 0 -> not (x el A).
Proof.
  induction A; cbn in *; dec; firstorder congruence.
Qed.

(* The product of two numbers is greater zero if both numbers are greater zero *)
Lemma NullMul a b : a > 0 -> b > 0 -> a * b > 0.
Proof.
  induction 1; cbn; lia.
Qed.