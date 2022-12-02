(* * Basic definitions of decidablility and Functions
- includes basic Lemmas about said functions 
 *)

From Undecidability.Shared.Libs.PSL Require Export Base.
From Undecidability.Shared.Libs.PSL Require Import FinTypesDef.

(* * Definition of useful tactics *)

(* dec is used to destruct all decisions appearing in the goal or assumptions. *)
Ltac dec := repeat (destruct Dec).

(* simplifies (decision x = x) *)
Ltac deq x := destruct (Dec (x=x)) as [[]  | isnotequal]; [> | contradict isnotequal; reflexivity] .

Lemma count_count_occ {X : Type} {HX : eq_dec X} (l : list X) x : count l x = count_occ HX l x.
Proof.
  induction l as [|y l IH]; [easy|].
  cbn. rewrite IH. unfold Dec. now destruct (HX x y); destruct (HX y x); congruence.
Qed.

(* This function takes a (A: list X) and yields a list (option X) which for every x in A contains Some x. The resultung list also contains None. The order is preserved. None is the first element of the resulting list. *)

Definition toOptionList {X: Type} (A: list X) :=
  None :: map (@Some _) A .

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
  now rewrite !count_count_occ, count_occ_app.
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
  rewrite count_count_occ. now apply count_occ_not_In.
Qed.

Lemma countIn (X:eqType) (x:X) A:
  count A x > 0 -> x el A.
Proof.
  rewrite count_count_occ. now intros ?%count_occ_In.
Qed.

(*  Dupfree Lists containing every x countain x exactly once *)
Lemma dupfreeCount (X: eqType) (x:X) (A: list X) : NoDup A -> x el A -> count A x = 1.
Proof.
  intros D E. induction D.
  - contradiction E.
  - cbn. dec.
    + f_equal. subst x0. now apply notInZero.
    + destruct E as [E | E]; [> congruence | auto].
Qed.        
