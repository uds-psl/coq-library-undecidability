(* 
  Finite multiset constratins with one constant 0 and unary function h
  (h^n 0) is represented as a natural number

  Terms t, u are
    t, u ::= n : list nat | x : nat | t ⊍ u | t ⩀ u | h (t)
    where x ranges over multiset variables
  
  Constraints 𝒞 are
    𝒞 ::= t = u 

  Constraints (t1 = u1),...,(tn = un) are satisfied, if 
    ϕ(t1) ≡ ϕ(u1),..., ϕ(tn) ≡ ϕ(un) for some ϕ : nat -> list nat
    where ≡ is equality up to permutation 
  *)

Require Import Arith.
Require Import List.
Import ListNotations.


Set Implicit Arguments.

Inductive mset : Set :=
  | mset_const : list nat -> mset
  | mset_var : nat -> mset
  | mset_plus : mset -> mset -> mset
  | mset_cap : mset -> mset -> mset
  | mset_h : mset -> mset.

(*
(* list equality up to permutation *)
Fixpoint mset_eq (A B : list nat) : Prop := 
  match A with
  | [] => B = []
  | (n :: A) => exists (B1 B2 : list nat), B = B1 ++ (n :: B2) /\ (mset_eq A (B1 ++ B2))
  end.
*)

(* list equality up to permutation *)
Definition mset_eq (A B : list nat) : Prop := 
  forall c, In c A \/ In c B -> count_occ Nat.eq_dec A c = count_occ Nat.eq_dec B c.
Notation "A ≡ B" := (mset_eq A B) (at level 65).

(* removes the first occurrence of n in A, fails otherwise *)
Fixpoint mset_try_remove (n : nat) (A : list nat) : option (list nat) :=
  match A with
  | [] => None
  | (m :: A) => if Nat.eqb n m then Some A else option_map (cons n) (mset_try_remove n A)
  end.

(* intersection of two multisets *)
Fixpoint mset_intersect (A B : list nat) : list nat :=
  match A with
  | [] => []
  | (n :: A) => 
    match mset_try_remove n B with
    | None => mset_intersect A B
    | Some(B) => n :: (mset_intersect A B)
    end
  end.

(* interpret an mset wrt. a valuation ϕ *)
Fixpoint mset_sem (ϕ : nat -> list nat) (A : mset) : list nat :=
  match A with
    | mset_const l => l
    | mset_var x => ϕ x
    | mset_plus A B => (mset_sem ϕ A) ++ (mset_sem ϕ B)
    | mset_cap A B => mset_intersect (mset_sem ϕ A) (mset_sem ϕ B)
    | mset_h A => map S (mset_sem ϕ A)
  end.

(* list of constraints *)
Definition MsetU_PROBLEM := list (mset * mset).
(* is there a valuation ϕ that satisfies all contraints *)
Definition MsetU_SAT (l : MsetU_PROBLEM) := 
  exists (ϕ : nat -> list nat), forall (A B : mset), In (A, B) l -> (mset_sem ϕ A) ≡ (mset_sem ϕ B).

Notation "t ⊍ u" := (mset_plus t u) (at level 40).
Notation "t ⩀ u" := (mset_cap t u) (at level 39).
Notation "'h' t" := (mset_h t) (at level 38).
(*Notation "• x" := (mset_var x) (at level 38, format "• x") : nat_scope.*)
Notation "• l" := (mset_const l) (at level 38, format "• l").

Coercion mset_var : nat >-> mset.

(*
Definition MsetU_SAT_ϕ (ϕ : nat -> list nat) (l : MsetU_PROBLEM) := 
  forall (A B : mset), In (A, B) l -> (mset_sem ϕ A) ≡ (mset_sem ϕ B).
*)


Definition mset_sat (ϕ : nat -> list nat) (l : MsetU_PROBLEM) := 
  Forall (fun '(A, B) => (mset_sem ϕ A) ≡ (mset_sem ϕ B)) l.

Require Import ssreflect ssrbool ssrfun.
Require Import PeanoNat.
Require Import Psatz.

Require Import Facts.
Require Import ListFacts.
Require Import UserTactics.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Arguments mset_eq !A !B.
Arguments mset_intersect !A !B.

(*
Notation "n .+1" := (Datatypes.S n) (at level 2, left associativity, format "n .+1").
Notation "n .-1" := (Nat.pred n) (at level 2, left associativity, format "n .-1").
*)

(* list facts *)

Lemma singleton_length {X : Type} {A : list X} : length A = 1 -> exists a, A = [a].
Proof.
  case : A.
  - done.
  - move => a A /=. case. move /length_zero_iff_nil => ->. by eexists.
Qed.

Lemma exists_max {A} : length A > 0 -> exists a, In a A /\ Forall (fun b => a >= b) A.
Proof.
Admitted.


Section Mset.

  Lemma eq_length {A B} : A ≡ B -> length A = length B.
  Admitted.
(*
Proof.
  elim : A B.
  - by move=> B ->.
  - move=> n A IH B. rewrite /mset_eq -/mset_eq. move=> [B1 [B2 [-> +]]].
    move /IH => /= ->. rewrite ? app_length => /=. by lia.
Qed.  
  *)

  Lemma eq_in {A B} : A ≡ B -> forall c, (In c A <-> In c B).
  Proof.
  Admitted.
  
  Lemma eq_refl {A} : A ≡ A.
  Proof.
    done.
  Qed.
  
  Lemma eq_symm {A B} : A ≡ B -> B ≡ A.
  Proof.
    by firstorder.
  Qed.
  
  Lemma mset_eq_trans {A B C} : A ≡ B -> B ≡ C -> A ≡ C.
  Proof.
    move /copy => [/eq_in + +] /copy [/eq_in + +].
    by firstorder.
  Qed.

  (*
  Lemma eq_app {A B} : A ++ B ≡ B ++ A.
  Proof.
  Admitted.

  Lemma eq_cons {a A} : a :: A ≡ A ++ [a].
  Proof.
    rewrite -/(app [a] A). by apply: eq_app.
  Qed.
  *)

  Lemma eq_consE {a A B} : (a :: A) ≡ B -> exists B1 B2, B = B1 ++ (a :: B2) /\ A ≡ (B1 ++ B2).
  Proof.
  Admitted.

  Lemma eq_cons_iff {a A B} : (a :: A) ≡ (a :: B) <-> A ≡ B.
  Proof.
  Admitted.


  Lemma eq_nilE {A} : [] ≡ A -> A = [].
  Proof.
  Admitted.
End Mset.


(* satisfied iff variable 0 is evaluated to repeat 0 (pow 2 n) for n > 0 *)
Definition encode_bound : MsetU_PROBLEM :=
  let x := 1 in let y := 2 in let z := 3 in 
    [ 
      (x ⊍ y, •[0] ⊍ (h x)); 
      (y ⊍ (x ⊍ z) ⊍ (x ⊍ z), 0 ⊍ (h (x ⊍ z)));
      (0 ⩀ (x ⊍ y), •[0] ⩀ (x ⊍ y))
    ].


Lemma count_occ_app {X : Type} {D : forall x y : X, {x = y} + {x <> y}} {A B c}:
  count_occ D (A ++ B) c = count_occ D A c + count_occ D B c.
Proof.
Admitted.

(*
Lemma count_occ_cons {X : Type} {D : forall x y : X, {x = y} + {x <> y}} {A a c}:
  count_occ D (a :: A) c = (if D a c then 1 else 0) + count_occ D A c.
Proof.
  rewrite /count_occ /is_left. by case: (D a c).
Qed.
*)

Lemma count_occ_cons {X : Type} {D : forall x y : X, {x = y} + {x <> y}} {A a c}:
  count_occ D (a :: A) c = count_occ D (locked [a]) c + count_occ D A c.
Proof.
  rewrite /count_occ /is_left -lock. by case: (D a c).
Qed.

Lemma eq_lr {A B A' B'}:
  A ≡ A' -> B ≡ B' -> (A ≡ B) = (A' ≡ B').
Admitted.

Lemma app_cons_spec {X : Type} {a : X} {A : list X} : a :: A = (locked [a]) ++ A.
Proof. by rewrite -lock. Qed.


(* solves trivial multiset equalities *)
Ltac mset_eq_trivial := 
  move=> ? ?; rewrite ? (count_occ_app, count_occ_cons, count_occ_nil); unlock; by lia.


Lemma seq_last start length : seq start (S length) = (seq start length) ++ [start + length].
Proof.
  elim : length start.
    move => * /=. f_equal. by lia.
  move => length IH start /=. f_equal.
  have -> : start + S length = (S start) + length by lia.
  by apply : IH.
Qed.

Lemma cons_length {X : Type} {a : X} {A : list X} : length (a :: A) = 1 + length A.
Proof. done. Qed.

Lemma eq_in_iff {A B} : A ≡ B -> forall c, In c A <-> In c B.
Proof.
Admitted.

Lemma eq_Forall_iff {A B} : A ≡ B -> forall P, (Forall P A <-> Forall P B).
Proof.
Admitted.

Lemma nil_or_ex_max (A : list nat) : A = [] \/ exists a, In a A /\ Forall (fun b => a >= b) A.
Proof.
  case: A.
    by left.
  move=> ? ?. right. apply: exists_max => /=. by lia.
Qed.
  

(* forces instance to be a sequence *)
(* first constraint of encode bound *)
Lemma seq_spec A B : A ++ B ≡ [0] ++ (map S A) ->
  exists n, A ≡ seq 0 n /\ B = [n].
Proof.
  move /copy => [/eq_length + +].
  rewrite ? app_length map_length => /= H.
  have : length B = 1 by lia. clear H.
  move /singleton_length => [n ? Heq]. subst B. 
  exists n. constructor => //.
  move: n Heq.
  elim /(measure_ind (@length nat)) : A => A.
  case: (nil_or_ex_max A).
    move=> -> _ n /=. move /eq_consE => [? [? [+ /eq_nilE /app_eq_nil [? ?]]]].
    subst => /=. by case=> <-.
  move=> [m [+ ?]].
  move /(in_split _ _) => [A1 [A2 ?]]. subst A.
  move=> IH n.
  move /copy => [H +].
  have: n = 1+m.
    move : H.
    move /eq_in_iff /(_ (1+m)) /iffRL.
    apply: unnest. 
      rewrite ? (in_app_iff, in_cons_iff, map_app, map_cons). by auto.
    rewrite in_app_iff. case.
      grab Forall. move /Forall_forall. move=> + H. move /(_ _ H). by lia.
    rewrite /In /plus. by case.
  move=> ?. subst n.
  under (eq_lr (A' := (1 + m) :: (A1 ++ A2) ++ [m]) (B' := (1 + m) :: 0 :: map S (A1 ++ A2))).
  all: rewrite -/(mset_eq _ _).
    by mset_eq_trivial.
    rewrite ? map_app map_cons /plus. by mset_eq_trivial.
  move /eq_cons_iff /IH.
  apply: unnest.
    rewrite ? app_length cons_length. by lia.
  move => ?.
  under (eq_lr (A' := m :: (A1 ++ A2)) (B' := m :: (seq 0 m))).
  all: rewrite -/(mset_eq _ _).
    by mset_eq_trivial.
    rewrite seq_last /plus. by mset_eq_trivial.
  by apply /eq_cons_iff.
Qed.

Lemma mset_intersect_eq {A B C} : B ≡ C -> mset_intersect A B = mset_intersect A C.
Proof.
Admitted.


Tactic Notation "induction" "on" hyp(x) "with" "measure" uconstr(f) :=
  let H := fresh in pose H := f; pattern x in H; 
  match goal with [H := ?f x |- _] => (clear H; elim/(measure_ind f) : x) end.

(* forces B to contain small elements *)
(* second constraint of encode bound *)
Lemma element_bound_lt_spec A B n : 
  [n] ++ A ++ A ≡ B ++ (map S A) -> Forall (fun m => n >= m) B.
Proof.
  case: (nil_or_ex_max A).
    move=> ->.
    rewrite ? app_nil_r. move /eq_consE => [? [? [+ +]]].
    move=> ->. move /eq_nilE /app_eq_nil => [-> ->].
    by constructor.
  move=> [a [? ?]].
  move /copy => [/eq_in_iff /(_ (S a)) /iffRL].
  apply: unnest.
    rewrite ? in_app_iff in_map_iff. by eauto.
  rewrite ? in_app_iff.
  have ? : ~ In (S a) A. 
    move=> ?. grab Forall. move /Forall_forall /(_ (S a) ltac:(assumption)). by lia.
  case; last by firstorder.
  case; last done.
  move=> -> /eq_Forall_iff /(_ (fun b => S a >= b)) /iffLR.
  rewrite ? Forall_app_iff.
  apply: unnest.
    constructor; constructor => //.
    1-2: grab Forall; apply /Forall_impl; move => *; by lia.
  by move=> [+].
Qed.


Lemma in_seq {a n} : a < n -> In a (seq 0 n).
Proof.
Admitted.

Lemma in_intersect {a A B} : In a (mset_intersect A B) <-> (In a A /\ In a B).
Proof.
Admitted.

(* forces B to contain zeroes *)
(* third constraint of encode bound *)
Lemma element_bound_eq_spec A n : mset_intersect A (seq 0 n) ≡ mset_intersect [0] (seq 0 n) ->
  Forall (fun a => n > a) A -> Forall (fun a => 0 = a) A.
Proof.
  move => *.
  case: (Forall_dec (fun m => 0 = m) _ A) => //. 
    by apply: Nat.eq_dec.
  rewrite <- Exists_Forall_neg; first last.
    move=> x. case: (Nat.eq_dec 0 x); by auto.
  move/Exists_exists => [a [? ?]]. exfalso.
  grab Forall. move /Forall_forall /(_ a ltac:(assumption)).
  move=> ?. have: a < n by lia.
  move /in_seq => ?.
  grab mset_eq. move /eq_in_iff /(_ a).
  rewrite ? in_intersect.
  by firstorder.
Qed.

(* any solution of encode_bound substitutes variable 0 by a multiset of 0s *)
Lemma encode_bound_spec ϕ : mset_sat ϕ encode_bound -> Forall (fun a => 0 = a) (ϕ 0).
Proof.
  rewrite /encode_bound /mset_sat.
  rewrite ? Forall_cons_iff. move=> [+ [+ [+ _]]].
  
  move=> /=.
  move: (ϕ 3) => D. move: (ϕ 2) => C. move: (ϕ 1) => B. move: (ϕ 0) => A.
  move /seq_spec => [n [? HB]]. subst C.
  move /element_bound_lt_spec => ?.
  have HBn: B ++ [n] ≡ seq 0 (1+n).
    rewrite seq_last => /=.
    under (eq_lr (A' := [n] ++ B) (B' := [n] ++ seq 0 n)).
    all: rewrite -/(mset_eq _ _).
      by mset_eq_trivial.
      by mset_eq_trivial.
      by apply /eq_cons_iff.
  rewrite ? (mset_intersect_eq HBn).
  move /element_bound_eq_spec. apply.
  grab Forall. apply /Forall_impl => *. by lia.
Qed.

Lemma encode_bound_sat ϕ n : 
    let x := 1 in
    let y := 2 in 
    let z := 3 in 
    ϕ 0 = repeat 0 (Nat.pow 2 n) -> ϕ x = [n] -> ϕ y = seq 0 n -> 
    ϕ z = flat_map (fun i => repeat i (Nat.pred (Nat.pow 2 (n-i)))) (seq 0 n) ->
    mset_sat ϕ encode_bound.
  Proof.
    rewrite /encode_bound /MsetU_SAT_ϕ2. rewrite ? Forall_cons_iff.
    move : (3) => z. move : (2) => y. move : (1) => x. move=> /=.
    move=> -> -> -> ->.
    split.
      admit. (* easy *)
    split.
      admit. (* hard *)  
    split.
      admit. (* easy *)
    done.
Admitted.



Definition encode_nat (u : nat) : MsetU_PROBLEM :=
  let x := 1+u in
  let y := 2+u in 
  let z := 3+u in 
  let v := 4+u in
  let w := 5+u in
    [ 
      (x ⊍ y, (h y) ⊍ '[0]); 
      (x ⊍ (y ⊍ z) ⊍ (y ⊍ z), (h (y ⊍ z)) ⊍ v);
      (y ⩀ v, '[0]);
      (mset_var u, v ⊍ w)
    ].

(*
(* A = [0,...,0] of length n encodes the natural number n *)
Definition encodes_nat (A : list nat) := Forall (eq 0) A. 
*)

(* A = [0,...,0] of length n encodes the natural number n *)
Definition encodes_nat (A : list nat) (n : nat) : Prop := 
  A = repeat 0 n. 


Lemma encode_nat_spec ϕ v : MsetU_SAT_ϕ2 ϕ (encode_nat v) -> Forall (fun a => 0 = a) (mset_sem ϕ v).
Proof.
  rewrite /encode_nat /MsetU_SAT_ϕ2.
  move: (1+v)=> x. move: (2+v)=> y. move: (3+v)=> z.
  rewrite ? Forall_cons_iff. move=> [+ [+ [+ _]]].

  move => /=.
Admitted.

Lemma encode_nat_sat ϕ u n : 
  let x := 1+u in
  let y := 2+u in 
  let z := 3+u in 
  let v := 4+u in
  let w := 5+u in
  ϕ u = repeat 0 n -> ϕ x = [n] -> ϕ y = seq 0 n -> 
  ϕ z = flat_map (fun i => repeat i (Nat.pred (Nat.pow 2 (n-i)))) (seq 0 n) ->
  ϕ v = repeat 0 (Nat.pow 2 n) -> ϕ w = repeat 0 ((Nat.pow 2 n) - n) ->
  MsetU_SAT_ϕ2 ϕ (encode_nat u).
Proof.
  rewrite /encode_nat /MsetU_SAT_ϕ2. rewrite ? Forall_cons_iff.
  move => /= -> -> -> -> -> ->.
  split. 
    admit. (* easy *)
  split.
    admit. (* hard *)  
  split.
    
    move=> x y z v w *. rewrite /encode_nat /MsetU_SAT_ϕ2.
  
  rewrite -/x -/y -/z -/v -/w.
  move=> /=.
  split.
    
  
Qed.


Lemma second_prod_constraint A n : 
  (seq 0 n) ++ A ≡ (repeat 0 n) ++ (map S A) -> n+(length A)+(length A) = n*n.
Proof.
  elim: n A.
  admit. (* easy *)
  move => n IH A H.
  have : exists A', A ≡ (repeat 0 n) ++ (map S A'). admit.
  move => [A' HA'].
  move : (eq_length HA'). rewrite app_length repeat_length map_length. move=> ->.
  suff: (n + length A' + length A' = n * n) by move=> ?; nia.
  apply: IH.
  admit. (* doable, but tricky *)
Admitted.


Definition encode_sum (x y z : nat) : MsetU_PROBLEM :=
  [(x ⊍ y, mset_var z)].

Lemma encode_sum_spec ϕ x y z : MsetU_SAT_ϕ2 ϕ (encode_sum x y z) -> 
  length (ϕ x) + length (ϕ y) = length (ϕ z).
Proof.
  rewrite /encode_sum /MsetU_SAT_ϕ2. 
  rewrite Forall_cons_iff. move=> [+ _]. move => /=.
  move /eq_length. by rewrite app_length.
Qed.


Definition encode_square (u v : nat) : MsetU_PROBLEM :=
  let x := 6+u in
  let y := 7+u in 
  let z := 8+u in 
  let v := 9+u in
  let w := 10+u in
  let t := 11+u in
  [
    (x ⊍ y, h y ⊍ '[0]);
    (y ⊍ z, h z ⊍ u);
    (z ⊍ w, h w ⊍ t); (*2*|t| = |u|*|u|-|u|*)
    (t ⊍ t ⊍ u, mset_var v)
  ].

Lemma encode_sum_spec ϕ x y : MsetU_SAT_ϕ2 ϕ (encode_square x y) -> 
  length (ϕ x) * length (ϕ x) = length (ϕ y).
Proof.
  rewrite /encode_sum /MsetU_SAT_ϕ2. 
  rewrite Forall_cons_iff. move=> [+ _]. move => /=.
  move /eq_length. by rewrite app_length.
Qed.