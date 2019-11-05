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

Lemma mset_satP {φ l} : mset_sat φ l <-> (forall (A B : mset), In (A, B) l -> (mset_sem φ A) ≡ (mset_sem φ B)).
Proof.
  rewrite /mset_sat Forall_forall. constructor.
  - move=> H A B. apply /H.
  - move=> H [A B]. apply /H.
Qed.

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

  Lemma eq_eq {A B}: A = B -> A ≡ B.
  Proof.
    by move=> ->.
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

  Lemma eq_app_iff {A B C} : (A ++ B) ≡ (A ++ C) <-> B ≡ C.
  Proof.
  Admitted.

  Lemma eq_map_iff {f} {A B}: map f A ≡ map f B <-> A ≡ B.
  Proof.
  Admitted.

  Lemma eq_nilE {A} : [] ≡ A -> A = [].
  Proof.
  Admitted.

  Lemma eq_singletonE {a A} : [a] ≡ A -> A = [a].
  Proof.
  Admitted.

  Lemma eq_repeatE {a A n} : repeat a n ≡ A -> A = repeat a n.
  Proof.
  Admitted.

  Lemma eq_mapE {A} : map S A ≡ A -> A = [].
  Proof.
  Admitted.

  Lemma eq_appI {A B A' B'} : A ≡ A' -> B ≡ B' -> A ++ B ≡ A' ++ B'.
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
  A ≡ A' -> B ≡ B' -> (A ≡ B) <-> (A' ≡ B').
Admitted.

Lemma app_cons_spec {X : Type} {a : X} {A : list X} : a :: A = (locked [a]) ++ A.
Proof. by rewrite -lock. Qed.


(* solves trivial multiset equalities *)
Ltac mset_eq_trivial := 
  move=> ? ?; rewrite ? (count_occ_app, count_occ_cons, count_occ_nil); unlock; by lia.

Lemma Forall_nil_iff {X: Type} {P: X -> Prop} : Forall P [] <-> True.
Proof. by constructor. Qed.


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

Lemma mset_intersect_eq {A B C} : B ≡ C -> mset_intersect A B = mset_intersect A C.
Proof.
Admitted.

Lemma in_seq {a n} : a < n -> In a (seq 0 n).
Proof.
Admitted.

Lemma in_intersect {a A B} : In a (mset_intersect A B) <-> (In a A /\ In a B).
Proof.
Admitted.

Lemma intersect_repeat {a n A} : n > 0 -> In a A -> mset_intersect (repeat a n) A = [a].
Proof.
Admitted.


Lemma seq_succ {m n} : seq m (S n) = m :: (seq (S m) n).
Proof.
  done.
Qed.


Lemma flat_map_cons {X Y : Type} {f : X -> list Y} {a A} : 
  flat_map f (a :: A) = (f a) ++ (flat_map f A).
Proof.
  done.
Qed.

Lemma repeat_succ {X : Type} {x : X} {n} : repeat x (S n) = x :: repeat x n.
Proof.
  done.
Qed.

Lemma repeat_add {X : Type} {x : X} {m n} : repeat x (m + n) = repeat x m ++ repeat x n.
Proof.
Admitted.

Lemma repeat_eq_length {X : Type} {x : X} {m n} : (m = n) <-> (repeat x m = repeat x n).
Proof.
Admitted.

Lemma repeat_map {X Y: Type} {f: X -> Y} {x: X} {n} : repeat (f x) n = map f (repeat x n).
Proof.
Admitted.

(* forces instance to be a sequence *)
(* first constraint of encode bound *)
(* type 1 constraint *)
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

(* type 1 constraint satisfied by any sequence *)
Lemma seq_sat n : (seq 0 n) ++ [n] ≡ [0] ++ (map S (seq 0 n)).
Proof.
  rewrite seq_shift - seq_last. 
  by apply: eq_refl.
Qed.

(* auxiliary lemma for nat_spec *)
Lemma nat_spec_aux n A B C : C ++ (n :: A) ≡ B ++ (map S A) -> 
  Forall (fun b => b = 0 \/ n < b) B -> 
  exists A' B', A ≡ (seq 0 n) ++ A' /\ B ≡ 0 :: B' /\ C ++ A' ≡ B' ++ (map S A').
Proof.
  elim: n A B.
    move=> A B /copy [/eq_in_iff /(_ 0) /iffLR].
    apply: unnest. 
      apply /in_app_iff. right. by firstorder done. 
    move /in_app_iff. case; first last.
      move /in_map_iff=> [? [? ?]]. by lia.
    move /(@in_split _ _) => [B1 [B2 ->]].
    under (eq_lr _ _ (A' := 0 :: (C ++ A)) (B' := 0 :: ((B1 ++  B2) ++ map S A))).
      by mset_eq_trivial.
      by mset_eq_trivial.
    move /eq_cons_iff => H _. exists A, (B1 ++ B2).
    split=> //. split=> //.
    by mset_eq_trivial.
  move=> n IH A B /copy [/eq_in_iff /(_ (S n)) /iffLR].
  apply: unnest. 
    apply /in_app_iff. right. by firstorder done.
  move /in_app_iff. case.
    move=> H _ /Forall_forall => /(_ _ H). by lia.
  move /in_map_iff=> [n' [+ +]]. case=> ?. subst n'.
  move /(@in_split _ _) => [A1 [A2 ?]]. subst A.
  under (eq_lr (A' := S n :: (C ++ (n :: (A1 ++ A2)))) (B' := S n :: (B ++ map S (A1 ++ A2)))).
    by mset_eq_trivial.
    move=> c. rewrite ? map_app map_cons. move: c. by mset_eq_trivial.
  move /eq_cons_iff => /IH + ?. apply: unnest.
    grab Forall. apply /Forall_impl. move=> ?. by lia.
  move=> [A' [B' [? [? ?]]]]. exists A', B'.
  split=> //.
  rewrite seq_last.
  under (eq_lr (A' := n :: (A1 ++ A2)) (B' := n :: (seq 0 n ++ A'))).
    by mset_eq_trivial.
    rewrite /plus. by mset_eq_trivial.
  rewrite -/(mset_eq _ _). by apply /eq_cons_iff.
Qed.


(* forces elements of A to be either zero or large enough *)
Lemma bound_spec {n A B C} : C ≡ seq 0 n -> (mset_intersect C A) ++ B ≡ [0] -> Forall (fun a => a = 0 \/ n <= a) A.
Proof.
  move => HC /eq_in => Heq.
  case: (Forall_dec (fun a : nat => a = 0 \/ n <= a) _ A) => //.
    case. 
      left; by left.
    move=> m.
    case: (le_lt_dec n (S m)) => ?.
      left; by right.
    right. by lia.
  rewrite <- Exists_Forall_neg; first last.
    move=> ?. by lia.
  move/Exists_exists => [a [? ?]]. exfalso.
  have ?: 0 <> a by lia. have: a < n by lia.
  move /in_seq => H. move: HC => /eq_in_iff /(_ a) /iffRL /(_ H){H} => ?.
  have H: In a (mset_intersect C A) by rewrite in_intersect.
  move: (Heq a) => /iffLR. rewrite in_app_iff.
  apply: unnest. by left.
  by case.
Qed.

Lemma bound_sat_aux {m n l} : m > 0 -> mset_intersect (seq m n) (repeat 0 l) = [].
Proof.
  elim: n m l.
    by done.
  move=> n IH m l Hm. rewrite /seq -/seq /mset_intersect -/mset_intersect.
  have: mset_try_remove m (repeat 0 l) = None.
    elim: l=> //.
    move=> a IH' /=.
    inspect_eqb. by rewrite IH'.
  move=> ->. apply /IH. by lia.
Qed.

(* bound constraints are satisfied *)
Lemma bound_sat {n} : (mset_intersect (seq 0 n) (repeat 0 n)) ++ (if n is 0 then [0] else []) ≡ [0].
Proof.
  case: n.
    by done.
  move=> n /=. rewrite app_nil_r. apply /eq_cons_iff.
  apply: eq_eq. by apply: bound_sat_aux.
Qed.


(* forces B to be a n zeroes and A to be of length in proportion to n squared *)
Lemma nat_spec n A B : (seq 0 n) ++ A ≡ B ++ (map S A) -> 
  Forall (fun b => b = 0 \/ n <= b) B -> B = repeat 0 n /\ length A + length A + n = n * n.
Proof.
  elim: n A B.
    move=> A B /copy [/eq_length] /=. rewrite ? app_length map_length.
    move=> ?. have: length B = 0 by lia. move /length_zero_iff_nil.
    move=> ->. rewrite /app. by move /eq_symm /eq_mapE => ->.
  move=> n IH A B. rewrite seq_last /plus -/plus.
  under (eq_lr _ eq_refl (A' := seq 0 n ++ (n :: A))).
    by mset_eq_trivial.
  move /nat_spec_aux => + H. apply: unnest.
    move: H. apply /Forall_impl => ?. by lia.
  move=> [A' [B' [HA' [HB']]]]. move /IH.
  apply: unnest.
    move: HB' => /eq_Forall_iff. move /(_ (fun b : nat => b = 0 \/ n <= b)) /iffLR.
    apply: unnest.
      grab Forall. apply /Forall_impl. move=> ?. by lia.
    move /Forall_cons_iff=> [_].
    apply /Forall_impl. move=> ?. by lia.
  move=> [? ?]. subst B'. move : HB'. rewrite -/(repeat 0 (S n)).
  move /eq_symm /eq_repeatE => ?. split=> //.
  move: HA' => /eq_length. rewrite app_length seq_length. by lia. 
Qed.

(* there exist solutions for nat contraints *)
Lemma nat_sat {n}:
  let A := flat_map (fun i => repeat i ((Nat.pred n) - i)) (seq 0 n) in
  (seq 0 n) ++ A ≡ (repeat 0 n) ++ (map S A).
Proof.
  move=> A. subst A.
  elim: n.
    by done.
  move=> n IH /=.
  apply /eq_cons_iff. rewrite ? Nat.sub_0_r.
  under (eq_lr _ eq_refl (A' := repeat 0 n ++ seq 1 n ++ flat_map (fun i : nat => repeat i (n - i)) (seq 1 n))).
  all: rewrite -/(mset_eq _ _).
    by mset_eq_trivial.
  apply /eq_app_iff. 
  move: IH => /(eq_map_iff (f := S)).
  
  rewrite <- seq_shift. rewrite ? flat_map_concat_map.
  rewrite ? map_app concat_map. rewrite ? map_map.
  move /(eq_lr _ _). apply.
  - apply /eq_app_iff. apply: eq_eq. f_equal. apply: map_ext => a.
    rewrite repeat_map. do 2 f_equal. by lia.
  - apply /eq_app_iff. apply: eq_eq. do 2 f_equal. apply: map_ext => a.
    rewrite repeat_map. do 2 f_equal. by lia. 
Qed.

(* [0] ++ [0,1] ++ [0,1,2] ++ ...*)
Definition pyramid n := flat_map (seq 0) (seq 0 n).

Lemma nat_sat_pyramid {n}: (seq 0 n) ++ (pyramid n) ≡ (repeat 0 n) ++ (map S (pyramid n)).
Proof.
  elim: n.
    by done.
  move=> n IH.
  rewrite /pyramid ? seq_last ? /plus. 
  rewrite ? flat_map_concat_map map_app concat_app.
  rewrite - ? flat_map_concat_map -/(pyramid _).
  rewrite map_app /flat_map ? app_nil_r /repeat -/(repeat _ n).
  rewrite - seq_last seq_shift.
  under (eq_lr 
    (A' := seq 0 (S n) ++ (seq 0 n ++ pyramid n)) 
    (B' := (0 :: seq 1 n) ++ (repeat 0 n ++ map S (pyramid n)))).
    by mset_eq_trivial.
    by mset_eq_trivial.
  rewrite -/(mset_eq _ _). by apply /eq_app_iff.
Qed.

Require NatNat.

Definition embed xy := NatNat.nat2_to_nat xy.
Definition unembed n := NatNat.nat_to_nat2 n.

Lemma embed_unembed {xy} : unembed (embed xy) = xy.
Proof.
  apply: NatNat.nat_nat2_cancel.  
Qed.

Lemma unembed_embed {n} : embed (unembed n) = n.
Proof.
  apply: NatNat.nat2_nat_cancel.  
Qed.

Opaque embed unembed.

Definition encode_nat (x: nat) : MsetU_PROBLEM :=
  let X := embed (x, 0) in
  let XX := embed (x, 1) in
  let Ax := embed (x, 2) in
  let Bx := embed (x, 3) in
  let Cx := embed (x, 4) in
  let Dx := embed (x, 5) in
  let Ex := embed (x, 6) in
    [
      (Ax ⊍ Bx, •[0] ⊍ (h Ax)); (* Ax = seq 0 (φ x) *)
      ((Ax ⩀ X) ⊍ Cx, •[0]); (* bounding constraints *)
      (Ax ⊍ Dx, X ⊍ (h Dx)); (* X is solved by n zeroes *)
      (Dx ⊍ Ex, XX ⊍ (h Ex)) (* XX is solved by sets of size proportional to the squared size of X *)
    ].

Lemma encode_nat_spec {φ x} : mset_sat φ (encode_nat x) -> 
  length (φ (embed (x, 1))) + length (φ (embed (x, 1))) + length (φ (embed (x, 0))) = 
    length (φ (embed (x, 0))) * length (φ (embed (x, 0))).
Proof.
  rewrite /mset_sat /encode_nat.
  rewrite ? Forall_cons_iff Forall_nil_iff /mset_sem.
  move=> [+ [+ [+ [+ _]]]].
  move: (φ (embed (x, 0)))=> X. move: (φ (embed (x, 1)))=> XX. 
  move: (φ (embed (x, 2)))=> A. move: (φ (embed (x, 3)))=> B.
  move: (φ (embed (x, 4)))=> C. move: (φ (embed (x, 5)))=> D. 
  move: (φ (embed (x, 6)))=> E.

  move /seq_spec => [n [Hseq _]].
  move /bound_spec => /(_ _ ltac:(eassumption)) HX.
  under (eq_lr _ eq_refl (A' := (seq 0 n) ++ D)).
    rewrite -/(mset_eq _ _).
    under (eq_lr (A' := D ++ A) (B' := D ++ seq 0 n)).
      by mset_eq_trivial.
      by mset_eq_trivial.
    rewrite -/(mset_eq _ _). by apply /eq_app_iff.
  move /nat_spec => /(_ ltac:(assumption)).
  move=> [/copy [+ ?] ?]. 
  move /(f_equal (@length nat)). rewrite repeat_length => ?.
  move /eq_length. rewrite ? app_length map_length.
  by lia.
Qed.

Lemma pyramid_shuffle {n} : seq 0 n ++ pyramid n ≡ repeat 0 n ++ map S (pyramid n).
Proof.
  elim: n.
    done.
  move=> n IH.
  rewrite /pyramid seq_last /plus flat_map_concat_map map_app concat_app.
  rewrite -flat_map_concat_map -/(pyramid _).
  rewrite ? map_app. cbn. rewrite ? app_nil_r.
  rewrite seq_shift.
  under (eq_lr 
    (A' := (seq 0 n ++ [n]) ++ (seq 0 n ++ pyramid n)) 
    (B' := (0 :: seq 1 n) ++ (repeat 0 n ++ map S (pyramid n)))).
    by mset_eq_trivial.
    by mset_eq_trivial.
  rewrite -/(mset_eq _ _).
  rewrite -seq_last -/(seq _ (S n)).
  by apply /eq_app_iff.
Qed.

Lemma encode_nat_sat_aux {n} : 
  pyramid n ++ flat_map pyramid (seq 0 n) ≡ repeat 0 (length (pyramid n)) ++ (map S (flat_map pyramid (seq 0 n))).
Proof.
  elim: n.
    by done.
  move=> n IH.
  rewrite /pyramid ? seq_last /plus ? (flat_map_concat_map, map_app, concat_app, app_length).
  rewrite - ? flat_map_concat_map -/pyramid -/(pyramid _).
  rewrite ? repeat_add seq_length.
  cbn. rewrite ? app_nil_r.
  under (eq_lr 
    (A' := (pyramid n ++ flat_map pyramid (seq 0 n)) ++ (seq 0 n ++ pyramid n))
    (B' := (repeat 0 (length (pyramid n)) ++ map S (flat_map pyramid (seq 0 n))) ++ (repeat 0 n ++ map S (pyramid n)))).
    by mset_eq_trivial.
    by mset_eq_trivial.
  rewrite -/(mset_eq _ _).
  apply: eq_appI.
    done.
  by apply: pyramid_shuffle.
Qed.

Definition encode_nat_vars φ x n : Prop :=
  φ (embed (x, 0)) = repeat 0 n /\
  φ (embed (x, 1)) = repeat 0 (length (pyramid n)) /\
  φ (embed (x, 2)) = seq 0 n /\
  φ (embed (x, 3)) = [n] /\
  φ (embed (x, 4)) = (if n is 0 then [0] else []) /\
  φ (embed (x, 5)) = pyramid n /\
  φ (embed (x, 6)) = flat_map pyramid (seq 0 n).

Lemma encode_nat_sat {φ x n} : 
  encode_nat_vars φ x n -> mset_sat φ (encode_nat x).
Proof.
  rewrite /encode_nat_vars /encode_nat /mset_sat ? Forall_cons_iff Forall_nil_iff /mset_sem.
  do 6 (move=> [->]). move=> ->.
  split. 
    by apply: seq_sat.
  split.
    by apply: @bound_sat.
  split.
    by apply: nat_sat_pyramid.
  split.
    by apply: encode_nat_sat_aux.
  done.
Qed.

(* represent constraints of shape 1 + x + y * y = z *)
Definition encode_constraint x y z := 
  encode_nat x ++ encode_nat y ++ encode_nat z ++ 
  let x := embed (x, 0) in
  let yy := embed (y, 1) in
  let y := embed (y, 0) in
  let z := embed (z, 0) in
  [ (•[0] ⊍ x ⊍ yy ⊍ yy ⊍ y, mset_var z) ].

(* if mset constraint has a solution, then uniform diophantine constraint is satisfied *)
Lemma encode_constraint_spec {φ x y z} : mset_sat φ (encode_constraint x y z) -> 
  1 + length (φ (embed (x, 0))) + length(φ (embed (y, 0))) * length(φ (embed (y, 0))) = length(φ (embed (z, 0))).
Proof.
  rewrite /encode_constraint /mset_sat. rewrite ? (Forall_app_iff).
  move => [/encode_nat_spec ? [/encode_nat_spec ? [ /encode_nat_spec ?]]].
  rewrite Forall_cons_iff Forall_nil_iff /mset_sem. move => [+ _].
  move /eq_length. rewrite ? app_length.
  have -> : (length [0] = 1) by done.
  by lia.
Qed.

Lemma encode_constraint_sat {φ x y z xn yn zn} : 
  encode_nat_vars φ x xn -> encode_nat_vars φ y yn -> encode_nat_vars φ z zn ->
  1 + xn + yn * yn = zn -> mset_sat φ (encode_constraint x y z).
Proof.
  move=> /copy [/encode_nat_sat ? Hx].
  move=> /copy [/encode_nat_sat ? Hy].
  move=> /copy [/encode_nat_sat ? Hz].
  rewrite /encode_constraint /mset_sat ? Forall_app_iff Forall_cons_iff Forall_nil_iff.
  move=> Hxyz.
  do 3 (split; [done|]).
  rewrite /mset_sem.
  move: Hx Hy Hz. rewrite /encode_nat_vars. move=> [-> _] [-> [-> _]] [-> _].
  split; first last.
    done.
  have ->: [0] = repeat 0 1 by done.
  rewrite - ? repeat_add. apply: eq_eq.
  f_equal. subst zn. clear. elim: yn.
    cbn. by lia.
  move=> yn IH. rewrite /pyramid seq_last /(plus 0 _) flat_map_concat_map map_app concat_app.
  rewrite -flat_map_concat_map -/(pyramid _).
  cbn. rewrite ? app_length seq_length. cbn. by lia.
Qed.


Require Import Problems.Reduction.
Require Import Problems.H10UC.


Definition encode_h10uc '(x, y, z) := encode_constraint x y z.

Lemma H10UC_to_MsetU : H10UC_SAT ⪯ MsetU_SAT.
Proof.
  exists (flat_map encode_h10uc).
  move=> h10ucs. constructor.
  - move=> [φ Hφ]. 
    pose ψ := (fun x => 
      match unembed x with
      | (x, 0) => repeat 0 (φ x)
      | (x, 1) => repeat 0 (length (pyramid (φ x)))
      | (x, 2) => seq 0 (φ x)
      | (x, 3) => [(φ x)]
      | (x, 4) =>  (if (φ x) is 0 then [0] else [])
      | (x, 5) => pyramid (φ x)
      | (x, 6) => flat_map pyramid (seq 0 (φ x))
      | _ => []
      end).
    exists ψ.
    elim: h10ucs Hφ.
      done.
    move=> [[x y] z] h10cs IH.
    move /Forall_forall. rewrite Forall_cons_iff. move=> [Hxyz /Forall_forall /IH].
    move=> {}IH A B.
    rewrite /flat_map -/(flat_map _) in_app_iff. case; first last.
      by apply /IH.
    rewrite /encode_h10uc.
    have := @encode_constraint_sat ψ x y z (φ x) (φ y) (φ z).
    apply: unnest.
      rewrite /encode_nat_vars.
      firstorder (by rewrite /ψ embed_unembed).
    apply: unnest.
      rewrite /encode_nat_vars.
      firstorder (by rewrite /ψ embed_unembed).
    apply: unnest.
      rewrite /encode_nat_vars.
      firstorder (by rewrite /ψ embed_unembed).
    apply: unnest.
      done.
    rewrite /mset_sat Forall_forall. apply.
  - move=> [φ]. rewrite - mset_satP /mset_sat. move=> Hφ.
    pose ψ := (fun x => length (φ (embed (x, 0)))).
    exists ψ.
    rewrite - Forall_forall.
    elim: h10ucs Hφ.
      done.
    move=> [[x y] z] h10ucs IH. rewrite /flat_map -/(flat_map _) Forall_app_iff.
    rewrite /(encode_h10uc _).
    move=> [/encode_constraint_spec Hxyz /IH ?].
    by constructor.
Qed.



Tactic Notation "induction" "on" hyp(x) "with" "measure" uconstr(f) :=
  let H := fresh in pose H := f; pattern x in H; 
  match goal with [H := ?f x |- _] => (clear H; elim/(measure_ind f) : x) end.

(*
  OLD CODE
*)


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



(* there is a solution that substitutes variable 0 by a multiset of size 2^n containing 0s *)
Lemma encode_bound_sat ϕ n : 
    let x := 1 in
    let y := 2 in 
    let z := 3 in 
    ϕ 0 = repeat 0 (Nat.pow 2 n) -> ϕ x = seq 0 n -> ϕ y = [n] -> 
    ϕ z = flat_map (fun i => repeat i (Nat.pred (Nat.pow 2 ((Nat.pred n)-i)))) (seq 0 n) ->
    mset_sat ϕ encode_bound.
  Proof.
    rewrite /encode_bound /mset_sat. rewrite ? Forall_cons_iff => /=.
    move=> -> -> -> ->.
    split.
      rewrite <- seq_last. by rewrite seq_shift.
    split.
      elim: n.
        done.
      pose A k m n := flat_map (fun i : nat => repeat i (Nat.pred (2 ^ (k - i)))) (seq m n).
      move=> n IH. rewrite -/(A _ _ _) in IH.
      rewrite ? seq_succ flat_map_cons Nat.sub_0_r Nat.pred_succ.
      
      rewrite -/(A _ _ _).
      under (eq_lr _ eq_refl (A' := 
        repeat 0 (2 ^ S n) ++ (([S n] ++ (seq 1 n) ++ A n 1 n) ++ (seq 1 n) ++ A n 1 n))).
      all: rewrite -/(mset_eq _ _).
        have -> : repeat 0 (2 ^ S n) = (0 :: repeat 0 (Nat.pred (2 ^ n))) ++ (0 :: repeat 0 (Nat.pred (2 ^ n))).
          rewrite <- ? repeat_succ. rewrite <- repeat_add. apply /repeat_eq_length.
          have : Nat.pow 2 n <> 0 by apply: Nat.pow_nonzero.
          move=> /=. by lia.
        by mset_eq_trivial.
      apply /eq_app_iff.
      rewrite <- seq_shift.
      have: A n 1 n = map S (A (Nat.pred n) 0 n).
        rewrite /A ? flat_map_concat_map. rewrite <- seq_shift. rewrite concat_map.
        rewrite ? map_map. f_equal.
        apply: map_ext => a. rewrite repeat_map.
        do 4 f_equal. by lia.
      have -> : [S n] = map S [n] by done.
      move=> ->. rewrite <- ? map_app.
      apply /eq_map_iff.
      under (eq_lr IH eq_refl).
        rewrite -/(mset_eq _ _). rewrite map_app.
        have -> : repeat 0 (2 ^ n) = 0 :: repeat 0 (Nat.pred (2 ^ n)).
          rewrite <- repeat_succ. f_equal.
          have : Nat.pow 2 n <> 0 by apply: Nat.pow_nonzero.
          by lia.
        by mset_eq_trivial.
    split.
      case: n.
        done.
      move=> n /=. rewrite /(mset_intersect []). rewrite intersect_repeat.
        have : Nat.pow 2 n <> 0 by apply: Nat.pow_nonzero. 
        by lia.
      by left.
      done.
    done.
Qed.

Lemma eq_h {A}: A ≡ map S A -> A = [].
Proof.
Admitted.

Lemma app_eq_head_r {a A B C} : A ++ B ≡ a :: C -> not (In a A) -> exists D, B ≡ a :: D.
Proof.
  move /eq_in_iff /(_ a) /iffRL. apply: unnest.
    by left.
  move /in_app_iff. case.
    by done.
  move /(in_split _ _) => [A1 [A2 ->]] _.
  exists (A1 ++ A2). by mset_eq_trivial.  
Qed.


Lemma eq_map_app_r {A B C}: A ++ B ≡ map S C -> exists D, B ≡ map S D.
Proof.
  elim: B A C.
    move=> *. by exists [].
  move=> b B IH A C /=. move /copy => [/eq_in_iff]. move /(_ b) /iffLR.
  apply: unnest.
    rewrite in_app_iff in_cons_iff. by firstorder.
  move /in_map_iff => [b' [?]]. subst b.
  move /(in_split _) => [C1 [C2 ?]]. subst C.
  rewrite map_app map_cons.
  under (eq_lr (A' := S b' :: (A ++ B)) (B' := S b' :: (map S C1 ++ map S C2))).
    1-2: by mset_eq_trivial.
  move /eq_cons_iff. rewrite <- map_app. move /IH => [C HC].
  exists (b' :: C).
  by apply /eq_cons_iff.
Qed.


Lemma eq_mapE {A B}: A ≡ map S B -> exists C, A = map S C.
Proof.
  elim: B A.
    move=> A /=. move /eq_symm /eq_nilE ->. by exists [].
  move=> a B IH A /=. move /copy => [/eq_in_iff]. move /(_ (S a)) /iffRL.
  apply: unnest.
    by left.
  move /(in_split _) => [A1 [A2 ?]]. subst A.
  under (eq_lr _ eq_refl (A' := S a :: (A1 ++ A2))).
    by mset_eq_trivial.
  move /eq_cons_iff /IH => [C HC].
  (* now we are talking equalities *)
Admitted.

(*A ++ B = map f C -> exists A' B', A = map f A' /\ B = map B'.*)

Lemma contains_repeat {n A B C} : map S B ++ A ≡ repeat 0 n ++ map S C -> exists D, A ≡ repeat 0 n ++ (map S D).
Proof.
  elim: n A.
    move=> A /=. by apply /eq_map_app_r.
  move=> n IH A /=. move /copy => [/app_eq_head_r]. apply: unnest.
    by move /in_map_iff => [? [?]].
  move=> [D ?].
  under (eq_lr _ eq_refl (A' := map S B ++ (0 :: D))).
    rewrite -/(mset_eq _ _). by apply /eq_app_iff.
  under (eq_lr _ eq_refl (A' := 0 :: (map S B ++ D))).
    by mset_eq_trivial.
  move /eq_cons_iff /IH. move=> [D' ?].
  exists D'.
  under (eq_lr (A' := 0 :: D) (B' := 0 :: D)).
  all: rewrite -/(mset_eq _ _) => //.
  by apply /eq_cons_iff /eq_symm.
Qed.

(* forces multiset size to be n*(n-1)/2 *)
Lemma quasi_square_spec {n A} : (seq 0 n) ++ A ≡ (repeat 0 n) ++ (map S A) -> 
  (length A) + (length A) + n = n * n.
Proof.
  elim: n A.
    by move=> A /= /eq_h ->.
  move=> n IH A.
  move=> /= /eq_cons_iff.
  move /copy => [H].
  rewrite <- seq_shift. move /contains_repeat.
  move=> [B HB]. move: H.
  move=> /=.
  under (eq_lr (A' := seq 1 n ++ (repeat 0 n ++ map S B)) (B' := repeat 0 n ++ map S (repeat 0 n ++ map S B))).
  all: rewrite -/(mset_eq _ _).
    by apply /eq_app_iff.
    by apply /eq_app_iff /eq_map_iff.
  under (eq_lr _ eq_refl (A' := repeat 0 n ++ seq 1 n ++ map S B)).
    by mset_eq_trivial.
  move /eq_app_iff. rewrite <- seq_shift. rewrite <- map_app.
  move /eq_map_iff. move /IH.
  move: HB => /eq_length. rewrite app_length map_length repeat_length.
  by nia.
Qed.

(* there exist solutions for quasi-square contraints *)
Lemma quasi_square_sat {n}:
  let A := flat_map (fun i => repeat i ((Nat.pred n) - i)) (seq 0 n) in
  (seq 0 n) ++ A ≡ (repeat 0 n) ++ (map S A).
Proof.
  move=> A. subst A.
  elim: n.
    by done.
  move=> n IH /=.
  apply /eq_cons_iff. rewrite ? Nat.sub_0_r.
  under (eq_lr _ eq_refl (A' := repeat 0 n ++ seq 1 n ++ flat_map (fun i : nat => repeat i (n - i)) (seq 1 n))).
  all: rewrite -/(mset_eq _ _).
    by mset_eq_trivial.
  apply /eq_app_iff. 
  move: IH => /(eq_map_iff (f := S)).
  
  rewrite <- seq_shift. rewrite ? flat_map_concat_map.
  rewrite ? map_app concat_map. rewrite ? map_map.
  move /(eq_lr _ _). apply.
  - apply /eq_app_iff. apply: eq_eq. f_equal. apply: map_ext => a.
    rewrite repeat_map. do 2 f_equal. by lia.
  - apply /eq_app_iff. apply: eq_eq. do 2 f_equal. apply: map_ext => a.
    rewrite repeat_map. do 2 f_equal. by lia. 
Qed.


Definition encode_square_aux (u : nat) : MsetU_PROBLEM :=
  let x := 6+u in
  let y := 7+u in 
  let z := 8+u in 
  let v := 9+u in
  let w := 10+u in
  [
    (x ⊍ y, h y ⊍ '[0]);
    (y ⊍ z, h z ⊍ u);
    (z ⊍ w, h w ⊍ t); (*2*|t| = |u|*|u|-|u|*)
    (t ⊍ t ⊍ u, mset_var v)
  ].



Obsolete


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