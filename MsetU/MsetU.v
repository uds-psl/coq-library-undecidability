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

Require Import List.
Import ListNotations.

Set Implicit Arguments.

Inductive mset : Set :=
  | mset_const : list nat -> mset
  | mset_var : nat -> mset
  | mset_plus : mset -> mset -> mset
  | mset_cap : mset -> mset -> mset
  | mset_h : mset -> mset.

(* list equality up to permutation *)
Fixpoint mset_eq (A B : list nat) : Prop := 
  match A with
  | [] => B = []
  | (n :: A) => exists (B1 B2 : list nat), B = B1 ++ (n :: B2) /\ (mset_eq A (B1 ++ B2))
  end.
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


Set Implicit Arguments.
Set Maximal Implicit Insertion.

Lemma eq_length {A B} : A ≡ B -> length A = length B.
Proof.
  elim : A B.
  - by move=> B ->.
  - move=> n A IH B. rewrite /mset_eq -/mset_eq. move=> [B1 [B2 [-> +]]].
    move /IH => /= ->. rewrite ? app_length => /=. by lia.
Qed.  
  
Lemma singleton_length {X : Type} {A : list X} : length A = 1 -> exists a, A = [a].
Proof.
  case : A.
  - done.
  - move => a A /=. case. move /length_zero_iff_nil => ->. by eexists.
Qed.


(* satisfied iff variable 0 is evaluated to repeat 0 (pow 2 n) for n > 0 *)
Definition encode_bound : MsetU_PROBLEM :=
  let x := 1 in let y := 2 in let z := 3 in 
    [ 
      (x ⊍ y, •[0] ⊍ (h x)); 
      (y ⊍ (x ⊍ z) ⊍ (x ⊍ z), 0 ⊍ (h (x ⊍ z)));
      (0 ⩀ (x ⊍ y), •[0] ⩀ x)
    ].

Lemma exists_max {A} : length A > 0 -> exists a, In a A /\ Forall (fun b => a >= b) A.
Proof.
Admitted.

Lemma mset_eq_spec {A B} : A ≡ B <-> forall c, In c A \/ In c B -> count_occ Nat.eq_dec A c = count_occ Nat.eq_dec B c.
Proof.
Admitted.

Lemma mset_eq_in {A B} : A ≡ B -> forall c, (In c A <-> In c B).
Proof.
Admitted.

Lemma mset_eq_refl {A} : A ≡ A.
Proof.
  by apply /mset_eq_spec.
Qed.

Lemma mset_eq_symm {A B} : A ≡ B -> B ≡ A.
Proof.
  rewrite ? mset_eq_spec. by firstorder.
Qed.

Lemma mset_eq_trans {A B C} : A ≡ B -> B ≡ C -> A ≡ C.
Proof.
  move /copy => [/mset_eq_in + +] /copy [/mset_eq_in + +].
  rewrite ? mset_eq_spec.
  by firstorder.
Qed.

Lemma count_occ_app {X : Type} {D : forall x y : X, {x = y} + {x <> y}} {A B c}:
  count_occ D (A ++ B) c = count_occ D A c + count_occ D B c.
Proof.
Admitted.

Lemma count_occ_cons {X : Type} {D : forall x y : X, {x = y} + {x <> y}} {A a c}:
  count_occ D (a :: A) c = (if D a c then 1 else 0) + count_occ D A c.
Proof.
  rewrite /count_occ /is_left. by case: (D a c).
Qed.

Lemma mset_eq_app {A B} : A ++ B ≡ B ++ A.
Proof.
  rewrite ? mset_eq_spec.
Admitted.

Lemma mset_eq_cons {a A} : a :: A ≡ A ++ [a].
Proof.
  rewrite -/(app [a] A). by apply: mset_eq_app.
Qed.

Lemma eq_lr {A B A' B'}:
  A ≡ A' -> B ≡ B' -> (A ≡ B) = (A' ≡ B').
Admitted.

Lemma app_cons_spec {X : Type} {a : X} {A : list X} : a :: A = [a] ++ A.
Proof. done. Qed.

Lemma eq_head {c A B} : (c :: A) ≡ (c :: B) -> A ≡ B.
Proof.
Admitted.

(* solves trivial multiset equalities *)
Ltac mset_eq_trivial := 
  apply /mset_eq_spec => ? ?; rewrite ? (count_occ_app, count_occ_cons, count_occ_nil); by lia.

Lemma seq_spec A B : A ++ B ≡ [0] ++ (map S A) ->
  exists n, A ≡ seq 0 n /\ B = [n].
Proof.
  move /copy => [/eq_length + +].
  rewrite ? app_length map_length => /= H.
  have : length B = 1 by lia. clear H.
  move /singleton_length => [n ? Heq]. subst B. 
  exists n. constructor => //.
  move: n Heq.
  elim /(measure_ind (@length nat)) : A.
  move => A. move lA : (length A) => k.
  case: k lA.
    move /length_zero_iff_nil => ? _. subst A.
    move=> n /=. move=> [? [? [+ /app_eq_nil [? ?]]]].
    subst => /=. by case=> <-.
  move=> k lA.
  have [m [+ ?]] := @exists_max A (ltac:(lia)).
  move /(in_split _ _) => [A1 [A2 ?]]. subst A.
  move=> IH n.
  have: n = 1+m. admit. (*doable*)
  move=> ?. subst n.

  simpl.
  under (eq_lr (A' := []) (B' := [])).

  Opaque mset_eq.

  under (eq_lr (A' := []) (B' := [])).
  rewrite /mset_eq.
  all: rewrite -/mset_eq.

  have Hl : (A1 ++ m :: A2) ++ [1 + m] ≡ (1 + m) :: (A1 ++ A2) ++ [m].
    by mset_eq_trivial.
  have Hr : 0 :: map S (A1 ++ m :: A2) ≡ (1 + m) :: 0 :: (map S (A1 ++ A2)).
    rewrite ? map_app map_cons. rewrite /plus. by mset_eq_trivial.
  
  rewrite (eq_lr Hl Hr). move=> /=.
    
    rewrite ? count_occ_app count_occ_cons.
    rewrite ? count_occ_cons.
    rewrite ? count_occ_app count_occ_cons. rewrite ? count_occ_app count_occ_cons.
    
    by lia.
  move=> Heql. under (eq_lr Heql).
    rewrite ? in_app_iff in_cons_iff.

  under (eq_lr mset_eq_app mset_eq_refl).

  move /mset_eq_trans.
  
  rewrite map_app map_cons.
  
  move => H.
  suff : (B1 ++ B2 ≡ seq 0 m).
  admit.
  apply : IH. admit.
  admit.

Lemma first_constraint_1 x y ϕ : MsetU_SAT_ϕ ϕ [(x ⊍ y, h y ⊍ •[0])] -> exists (n : nat), mset_sem ϕ x = [n].
Proof.
  rewrite /MsetU_SAT_ϕ.
  move /(_ (x ⊍ y) (h y ⊍ •[0]) ltac:(firstorder)).
  rewrite /mset_sem -/mset_sem.
  move /eq_length.
  rewrite ? app_length map_length => /= H.
  have : length (mset_sem ϕ x) = 1 by lia. clear H.
  move /singleton_length => [n ?]. eexists. by eassumption.
Qed.



Tactic Notation "induction" "on" hyp(x) "with" "measure" uconstr(f) :=
  let H := fresh in pose H := f; pattern x in H; 
  match goal with [H := ?f x |- _] => (clear H; elim/(measure_ind f) : x) end.

Lemma first_constraint_2 x y ϕ : MsetU_SAT_ϕ ϕ [(x ⊍ y, h y ⊍ '[0])] -> 
  exists (n : nat), mset_sem ϕ x = [n] /\ mset_sem ϕ y ≡ seq 0 n.
Proof.
  rewrite /MsetU_SAT_ϕ.
  move /(_ (x ⊍ y) (h y ⊍ '[0]) ltac:(firstorder)).
  rewrite /mset_sem -/mset_sem.
  move : (mset_sem ϕ x) => A.
  move : (mset_sem ϕ y) => B.
  move /duplicate => [/eq_length].
  rewrite ? app_length map_length => /= H.
  have : length A = 1 by lia. clear H.
  move /singleton_length => [n -> Heq]. exists n. constructor => //.
  move: n Heq.
  elim /(measure_ind (@length nat)) : B.
  clear => B. move lB : (length B) => l.
  case : l lB.  admit. (* easy *) 
  - move => ? lB IH.
    have : exists m, In m B /\ Forall (fun n => m >= n) B. admit.
    move => [m [+ ?]]. move => _.
    have : exists B1 B2, B = B1 ++ (m :: B2). admit.
    move => [B1 [B2 ?]]. subst B.
    move => n.
    have : n = 1+m. admit.
    move => ?. subst n. move => H.
    suff : (B1 ++ B2 ≡ seq 0 m).
    admit.
    apply : IH. admit.
    admit.
Admitted. (* easy *)

Lemma second_constraint A B n : 
  [n] ++ ((seq 0 n) ++ A) ++ ((seq 0 n) ++ A) ≡ (map S ((seq 0 n) ++ A)) ++ B -> 
  exists C, A ≡ [n] ++ C /\ Forall (fun m => n > m) C.
Proof.
(* use max A *)
Admitted.

Require Import ListFacts.
Require Import UserTactics.

Lemma third_constraint A n : mset_intersect A (seq 0 n) ≡ [0] ->
  Forall (fun m => n > m) A -> Forall (fun m => 0 = m) A.
Proof.
  move => *.
  case: (Forall_dec (fun m => 0 = m) _ A). admit.
  done.
  rewrite <- Exists_Forall_neg.

  move/Exists_exists => [a [? ?]]. exfalso.
  grab Forall. move/Forall_forall /(_ _ ltac:(eassumption)). admit. (* doable *)
Admitted.



Lemma encode_bound_sat ϕ n : 
    let x := 1 in
    let y := 2 in 
    let z := 3 in 
    ϕ 0 = repeat 0 (Nat.pow 2 n) -> ϕ x = [n] -> ϕ y = seq 0 n -> 
    ϕ z = flat_map (fun i => repeat i (Nat.pred (Nat.pow 2 (n-i)))) (seq 0 n) ->
    MsetU_SAT_ϕ2 ϕ encode_bound.
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

Lemma encode_bound_spec ϕ : MsetU_SAT_ϕ2 ϕ encode_bound -> Forall (fun a => 0 = a) (ϕ 0).
Proof.
  rewrite /encode_bound /MsetU_SAT_ϕ2.
  rewrite ? Forall_cons_iff. move=> [+ [+ [+ _]]].

  move => /=.
  move: (ϕ 3) => C. move: (ϕ 2) => B. move: (ϕ 1) => A. move: (ϕ 0) => X.
  have: exists n, A = [n] /\ B = seq 0 n. admit. (* here I NEED that B = seq 0 n*)
  move=> [n ?]. subst A. move=> _.
  have: Forall (fun a => n > a) (B ++ C). admit. move=> ?.
  have: Forall (fun a => n >= a) X. admit. move=> ?.
  move=> _. case: (mset_try_remove 0 B).
  move=> _. grab Forall. elim: X.
  admit.
  move => a X IH. rewrite ? Forall_cons_iff. move=> [? ?].
  move=> /=.

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