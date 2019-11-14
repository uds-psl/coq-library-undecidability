(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland Informatics Campus, Saarland University, Saarbrücken, Germany
*)

(* 
  Reduction from:
    Uniform H10 constraint solvability (H10UC)
  to:
    Finite multiset constraint solvability (FMsetC)
  
  References:
    [1] Paliath Narendran: Solving Linear Equations over Polynomial Semirings.
      LICS 1996: 466-472, doi: 10.1109/LICS.1996.561463
*)

Require Import ssreflect ssrbool ssrfun.
Require Import Arith Psatz.
Require Import List.
Import ListNotations.

From Undecidability Require Import Problems.FMsetC Problems.H10UC Problems.Reduction.

Notation "t ⊍ u" := (mset_term_plus t u) (at level 40).
Notation "'h' t" := (mset_term_h t) (at level 38).
Notation "•0" := mset_term_zero.

Coercion mset_term_var : nat >-> mset_term.

Section Facts.

  (* induction principle wrt. a decreasing measure f *)
  (* example: elim /(measure_ind length) : l. *)
  Lemma measure_ind {X: Type} (f: X -> nat) (P: X -> Prop) : 
    (forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
  Proof.
    apply: well_founded_ind.
    apply: Wf_nat.well_founded_lt_compat. move=> *. by eassumption.
  Qed.

  (* transforms a goal (A -> B) -> C into goals A and B -> C *)
  Lemma unnest {A B C: Prop} : A -> (B -> C) -> (A -> B) -> C.
  Proof. auto. Qed.

  Lemma unnest_t (X Y Z: Type): X -> (Y -> Z) -> (X -> Y) -> Z.
  Proof. by auto. Qed.

  (* duplicates argument *)
  Lemma copy {A: Prop} : A -> A * A.
  Proof. done. Qed.

End Facts.

Arguments mset_eq !A !B.

Definition mset_sat (φ : nat -> list nat) (l : FMsetC_PROBLEM) := 
  Forall (fun '(A, B) => (mset_sem φ A) ≡ (mset_sem φ B)) l.

Lemma mset_satP {φ l} : mset_sat φ l <-> (forall (A B : mset_term), In (A, B) l -> (mset_sem φ A) ≡ (mset_sem φ B)).
Proof.
  rewrite /mset_sat Forall_forall. constructor.
  - move=> H A B. apply /H.
  - move=> H [A B]. apply /H.
Qed.

(* list facts *)

Lemma singleton_length {X : Type} {A : list X} : length A = 1 -> exists a, A = [a].
Proof.
  case: A.
    done.
  move => a A /=. case. move /length_zero_iff_nil => ->. by eexists.
Qed.

Lemma nil_or_ex_max (A : list nat) : A = [] \/ exists a, In a A /\ Forall (fun b => a >= b) A.
Proof.
  elim: A.
    by left.
  move=> a A. case.
    move=> ->. right. exists a. split; by [left | constructor].
  move=> [b [Hb1 Hb2]]. right.
  case: (le_lt_dec a b)=> ?.
  - exists b. split; by [right | constructor].
  - exists a. split.
      by left.
    constructor.
      done.
    move: Hb2. apply /Forall_impl => ?. by lia.
Qed.

(* count_occ facts *)
Lemma count_occ_app {X : Type} {D : forall x y : X, {x = y} + {x <> y}} {A B c}:
count_occ D (A ++ B) c = count_occ D A c + count_occ D B c.
Proof.
  elim: A B.
    done.
  move=> a A IH B /=. rewrite IH. by case: (D a c).
Qed.

Lemma count_occ_cons {X : Type} {D : forall x y : X, {x = y} + {x <> y}} {A a c}:
count_occ D (a :: A) c = count_occ D (locked [a]) c + count_occ D A c.
Proof.
  rewrite /count_occ /is_left -lock. by case: (D a c).
Qed.

(* In facts *)
Lemma in_cons_iff : forall {A : Type} {a b : A} {l : list A}, In b (a :: l) <-> (a = b \/ In b l).
Proof. by constructor. Qed.

(* Forall facts *)
Lemma Forall_nil_iff {X: Type} {P: X -> Prop} : Forall P [] <-> True.
Proof. by constructor. Qed.

Lemma Forall_cons_iff {T: Type} {P: T -> Prop} {a l} :
  Forall P (a :: l) <-> P a /\ Forall P l.
Proof.
  constructor. 
    move=> H. by inversion H.
  move=> [? ?]. by constructor.
Qed.

Lemma Forall_singleton_iff {X: Type} {P: X -> Prop} {x} : Forall P [x] <-> P x.
Proof.
  rewrite Forall_cons_iff. by constructor; [case |].
Qed.

Lemma Forall_app_iff {T: Type} {P: T -> Prop} {A B}: Forall P (A ++ B) <-> Forall P A /\ Forall P B.
Proof.
  elim: A.
    constructor; by [|case].
  move=> ? ? IH /=. rewrite ? Forall_cons_iff ? IH.
  by tauto.
Qed.

(* usage: rewrite ? Forall_norm *)
Definition Forall_norm := (@Forall_app_iff, @Forall_singleton_iff, @Forall_cons_iff, @Forall_nil_iff).

(* Forall2 facts *)
Lemma Forall2_nil_rE {X Y: Type} {P: X -> Y -> Prop} {A}: Forall2 P A [] -> A = [].
Proof. move=> H. by inversion H. Qed.

Lemma Forall2_nil_lE {X Y: Type} {P: X -> Y -> Prop} {A}: Forall2 P [] A -> A = [].
Proof. move=> H. by inversion H. Qed.

Lemma Forall2_lastP {X Y: Type} {P: X -> Y -> Prop} {A B a b}:
  Forall2 P (A ++ [a]) (B ++ [b]) <-> Forall2 P A B /\ P a b.
Proof. 
  elim: A B => /=.
    move=> B. constructor.
      elim: B => /=.
        move=> H. by inversion H.
      move=> c B IH H. inversion H. subst.
      have := Forall2_nil_lE ltac:(eassumption). by move /app_eq_nil => [_].
    move=> [/Forall2_nil_lE ->] ? /=. by constructor.
  move=> c A IH. elim=> /=.
    constructor.
      move=> H. inversion H. subst.
      have := Forall2_nil_rE ltac:(eassumption). by move /app_eq_nil => [_].
    by move=> [/Forall2_nil_rE].
  move=> d B IH2. constructor.
    move=> H. inversion H. subst. constructor.
      constructor.
        done.
      have := iffLR (IH B) ltac:(eassumption). by case.
    have := iffLR (IH B) ltac:(eassumption). by case.
  move=> [H ?]. inversion H. subst. constructor.
    done.
  apply /IH. by constructor.
Qed.

(* seq facts *)
Lemma seq_last start length : seq start (S length) = (seq start length) ++ [start + length].
Proof.
  have -> : S length = length + 1 by lia.
  by rewrite seq_app.
Qed.

(* repeat facts *)
Lemma repeat_add {X : Type} {x : X} {m n} : repeat x (m + n) = repeat x m ++ repeat x n.
Proof.
  elim: m.
    done.
  move=> m IH. cbn. by f_equal.
Qed.

Lemma Forall_repeat {X: Type} {a} {A: list X} : Forall (fun b => a = b) A -> A = repeat a (length A).
Proof.
  elim: A.
    done.
  move=> b A IH. rewrite Forall_norm => [[? /IH ->]]. subst b.
  cbn. by rewrite repeat_length.
Qed.

(* bijection between nat and nat * nat *)
Module NatNat.

(* 0 + 1 + ... + n *)
Definition big_sum (n : nat) : nat := nat_rec _ 0 (fun i m => m + (S i)) n.

(* bijection from nat * nat to nat *)
Definition nat2_to_nat '(x, y) : nat := (big_sum (x + y)) + y.

Definition next_nat2 '(x, y) : nat * nat := if x is S x then (x, S y) else (S y, 0).

(* bijection from nat to nat * nat *)
Definition nat_to_nat2 (n : nat) : nat * nat := Nat.iter n next_nat2 (0, 0).

Lemma nat_nat2_cancel : cancel nat2_to_nat nat_to_nat2.
Proof.
  move=> a. move Hn: (nat2_to_nat a) => n.
  elim: n a Hn.
    case; case=> [|?]; case=> [|?]=> /=; by [|lia].
  move=> n IH [x y]. case: y => [|y] /=. case: x => [|x] //=.
  all: rewrite ? (Nat.add_0_r, Nat.add_succ_r); case.
    rewrite -/(nat2_to_nat (0, x)). by move /IH ->.
  rewrite -/(nat2_to_nat (S x, y)). by move /IH ->.
Qed.

Lemma nat2_nat_cancel : cancel nat_to_nat2 nat2_to_nat.
Proof.
  elim=> //=.
  move=> n. move: (nat_to_nat2 n) => [+ ?].
  case=> /= => [|?]; rewrite ? (Nat.add_0_r, Nat.add_succ_r) => /=; by lia.
Qed.

End NatNat.

(* eq facts *)
Lemma eq_refl {A} : A ≡ A.
Proof. done. Qed.

Lemma eq_eq {A B}: A = B -> A ≡ B.
Proof. by move=> ->. Qed.
  
Lemma eq_symm {A B} : A ≡ B -> B ≡ A.
Proof. by firstorder done. Qed.
  
Lemma eq_in_iff {A B} : A ≡ B -> forall c, In c A <-> In c B.
Proof.
  rewrite /mset_eq => H c. constructor=> Hc.
  - have := iffLR (count_occ_In Nat.eq_dec A c) Hc.
    move: (H c) => ->.
    by move /(count_occ_In Nat.eq_dec B c).
  - have := iffLR (count_occ_In Nat.eq_dec B c) Hc.
    move: (H c) => <-.
    by move /(count_occ_In Nat.eq_dec A c).
Qed.

Lemma eq_nilE {A} : [] ≡ A -> A = [].
Proof.
  case: A.
    done.
  move=> a A /eq_in_iff /(_ a) /iffRL. apply: unnest.
    by left.
  done.
Qed.

Lemma eq_trans {A B C} : A ≡ B -> B ≡ C -> A ≡ C.
Proof.
  rewrite /mset_eq => + + c.
  move=> /(_ c) + /(_ c).
  by move=> -> ->.
Qed.

Lemma eq_Forall_iff {A B} : A ≡ B -> forall P, (Forall P A <-> Forall P B).
Proof.
  move /eq_in_iff => H P.
  rewrite ? Forall_forall. constructor; by firstorder done.
Qed.

Lemma eq_lr {A B A' B'}:
  A ≡ A' -> B ≡ B' -> (A ≡ B) <-> (A' ≡ B').
Proof.
  move=> HA HB. constructor.
  - move /eq_trans. move /(_ _ HB). 
    move /(eq_trans _). by move /(_ _ (eq_symm HA)). 
  - move /eq_trans. move /(_ _ (eq_symm HB)). 
    move /(eq_trans _). by move /(_ _ HA).
Qed. 

Lemma eq_appI {A B A' B'} : A ≡ A' -> B ≡ B' -> A ++ B ≡ A' ++ B'.
Proof.
  rewrite /mset_eq => + + c. move=> /(_ c) + /(_ c).
  rewrite ? count_occ_app. by move=> -> ->.
Qed.

(* solves trivial multiset equalities *)
Ltac eq_trivial := 
  move=> ?; rewrite ? (count_occ_app, count_occ_cons, count_occ_nil); unlock; by lia.
    
Lemma eq_cons_iff {a A B} : (a :: A) ≡ (a :: B) <-> A ≡ B.
Proof.
  rewrite /mset_eq. constructor.
  all: move=> H c; move: {H}(H c); rewrite ? count_occ_cons ? in_cons_iff; unlock.
  all: by rewrite Nat.add_cancel_l.
Qed.

Lemma eq_app_iff {A B C} : (A ++ B) ≡ (A ++ C) <-> B ≡ C.
Proof.
  elim: A.
    done.
  move=> a A IH /=.
  by rewrite eq_cons_iff.
Qed.

Lemma eq_length {A B} : A ≡ B -> length A = length B.
  elim /(measure_ind (@length nat)) : A B.
  case.
    by move=> _ B /eq_nilE ->.
  move=> a A IH B /copy [/eq_in_iff /(_ a) /iffLR]. apply: unnest.
    by left.
  move /(@in_split _ _) => [B1 [B2 ->]].
  under (eq_lr eq_refl (B' := a :: (B1 ++ B2))).
    by eq_trivial.
  move /eq_cons_iff. move /IH. apply: unnest.
    done.
  rewrite ? app_length => /=. by lia.
Qed.

Lemma eq_repeatE {a A n} : repeat a n ≡ A -> A = repeat a n.
Proof.
  move=> /copy [/eq_length]. rewrite repeat_length => HlA.
  move /eq_Forall_iff /(_ (fun c => a = c)) /iffLR. apply: unnest.
    clear. elim: n.
      by constructor.
    firstorder (by constructor).
  subst n.
  elim: A.
    done.
  move=> b A IH /Forall_cons_iff [<-] /IH -> /=.
  by rewrite repeat_length.
Qed.

Lemma eq_singletonE {a A} : [a] ≡ A -> A = [a].
Proof.
  have -> : [a] = repeat a 1 by done.
  by move /eq_repeatE.
Qed.

Lemma eq_mapE {A} : map S A ≡ A -> A = [].
Proof.
  case (nil_or_ex_max A).
    done.
  move=> [a [Ha /Forall_forall HA]] /eq_in_iff /(_ (S a)) /iffLR.
  rewrite in_map_iff. apply: unnest.
    by exists a.
  move /HA. by lia.
Qed.

(* interpret a multiset as a polynomial at p *)
Section EvalPolynomial.

(* interpret a multiset as a polynomial at p *)
Definition eval p A := fold_right plus 0 (map (fun n => Nat.pow p n) A).

Lemma evalP {p A}: eval p A = fold_right plus 0 (map (fun n => Nat.pow p n) A).
Proof. done. Qed.

Lemma eval_consP {p a A} : eval p (a :: A) = p^a + eval p A.
Proof. done. Qed.

Lemma eval_singletonP {p a} : eval p [a] = p^a.
Proof. cbn. by lia. Qed.

Lemma eval_appP {p A B} : eval p (A ++ B) = eval p A + eval p B.
Proof.
  elim: A.
    done.
  move=> a A IH /=. rewrite ? eval_consP. by lia.
Qed.

Definition eval_norm := (@eval_appP, @eval_singletonP, @eval_consP).

Lemma eval_nat {p A} : Forall (fun a => 0 = a) A -> eval p A = length A.
Proof.
  elim: A.
    done.
  move=> a A IH. rewrite ? Forall_norm ? eval_consP /length - /(length _).
  by move=> [<- /IH ->].
Qed.

Lemma eval_monotone {p q A} : p < q -> eval p A < eval q A \/ Forall (fun a => 0 = a) A.
Proof.
  move=> ?. elim: A.
    by right.
  case.
    move=> A IH. rewrite ? eval_consP ? Forall_norm => /=.
    case: IH=> IH.
      left. by apply: lt_n_S.
    by right.
  move=> a A IH. left. rewrite ? eval_consP.
  have ? := Nat.pow_lt_mono_l p q (S a) ltac:(done) ltac:(done).
  case: IH.
    by lia.
  move /eval_nat => H. rewrite ? H. by lia.
Qed.

(* a non-increasing polynomial is degenerate *)
Lemma eval_nat_spec {p q A} : p < q -> eval p A = eval q A -> Forall (fun a => 0 = a) A.
Proof.
  move /eval_monotone => /(_ A). case.
    by lia.
  done.
Qed.

Lemma eval_map {p A} : eval p (map S A) = p * eval p A.
Proof.
  elim: A.
    done.
  move=> a A IH. rewrite /map -/(map _ _) ? eval_consP IH.
  rewrite /Nat.pow -/Nat.pow.
  by nia.
Qed.

Lemma eval_eq {p A B} : A ≡ B -> eval p A = eval p B.
Proof.
  elim: A B.
    by move=> B /eq_nilE ->.
  move => a A IH B /copy [/eq_in_iff /(_ a) /iffLR]. apply: unnest.
    by left.
  move /(@in_split _ _) => [B1 [B2 ->]].
  under (eq_lr eq_refl (B' := a :: (B1 ++ B2))).
    by eq_trivial.
  move /eq_cons_iff /IH. rewrite ? eval_norm.
  move=> ->. by lia.
Qed.

End EvalPolynomial.

(* 
  auxiliary soundness and completeness lemmas 
  for the reduction from H10UC to FMsetC
*)

(* nat constraints are only satisfied by multisets containing only zeroes *)
Lemma nat_spec {n A B C} : 
  (map S B) ++ A ≡ [n] ++ B ++ B ++ B ++ B ->
  (map S (map S C)) ++ A ≡ [2*n] ++ C ++ C ++ C ++ C ->
  Forall (fun a => 0 = a) A.
Proof.
  move=> /(eval_eq (p := 4)) + /(eval_eq (p := 2)).
  rewrite ? eval_norm ? eval_map Nat.pow_mul_r.
  move=> /= ? ?.
  have : eval 2 A = eval 4 A by lia.
  apply /eval_nat_spec.
  by lia.
Qed.

Fixpoint tower m n :=
  match n with 
  | 0 => []
  | S n => (tower m n) ++ (tower m n) ++ (tower m n) ++ (tower m n) ++ [m*n]
  end.

Lemma nat_sat {m n} :
  (map (fun i => m + i) (tower m n)) ++ (repeat 0 (4^n)) ≡ [m*n] ++ (tower m n) ++ (tower m n) ++ (tower m n) ++ (tower m n).
Proof.
  elim: n.
    by (have -> : m * 0 = 0 by nia).
  move=> n IH /=. rewrite ? map_app ? repeat_add. cbn.
  pose L := (map (fun i => m + i) (tower m n)) ++ (repeat 0 (4^n)).
  pose R := [m*n] ++ (tower m n) ++ (tower m n) ++ (tower m n) ++ (tower m n).
  have -> : m + m * n = m * (S n) by nia.
  under (eq_lr (A' := (m * S n) :: (L ++ L ++ L ++ L)) (B' := (m * S n) :: (R ++ R ++ R ++ R))).
    by eq_trivial.
    by eq_trivial.
  rewrite -/(mset_eq _ _).
  apply /eq_cons_iff.
  do 3 (apply /eq_appI; first done).
  done.
Qed.

(* forces instance to be a sequence *)
(* first constraint of encode bound *)
(* type 1 constraint *)
Lemma seq_spec2 {d A B} : A ++ B ≡ [0] ++ (map (fun i => (S d) + i) A) ->
  exists n, A ≡ map (fun i => (S d) * i) (seq 0 n) /\ B = [(S d) * n].
Proof.
  move /copy => [/eq_length + +].
  rewrite ? app_length map_length => /= H.
  have : length B = 1 by lia. clear H.
  move /singleton_length => [n ? Heq]. subst B. 
  exists (n / (S d)).
  move: n Heq.
  elim /(measure_ind (@length nat)) : A => A.
  case: (nil_or_ex_max A).
    move=> -> _ n /= /eq_singletonE. case=> <-. constructor.
      done.
    cbn. f_equal. by nia.
  move=> [m [+ Hm]].
  move /(in_split _ _) => [A1 [A2 ?]]. subst A.
  move=> IH n.
  move /copy => [H +].
  have: n = (S d)+m.
    move : H.
    move /eq_in_iff /(_ ((S d)+m)) /iffRL.
    apply: unnest. 
      rewrite ? (in_app_iff, in_cons_iff, map_app, map_cons). by lia.
    rewrite in_app_iff. case.
      move: Hm => /Forall_forall. move=> + H. move /(_ _ H). by lia.
    rewrite /In /plus. by case.
  move=> ?. subst n.
  under (eq_lr (A' := ((S d) + m) :: (A1 ++ A2) ++ [m]) (B' := ((S d) + m) :: 0 :: map (fun i : nat => S (d + i)) (A1 ++ A2))).
  all: rewrite -/(mset_eq _ _).
    by eq_trivial.
    rewrite ? map_app map_cons /plus. by eq_trivial.
  move /eq_cons_iff /IH.
  apply: unnest.
    rewrite ? app_length => /=. by lia.
  move=> [IHA1A2].
  case. rewrite  -/(Nat.div m (S d)) - ? /(mult (S d) _).
  have -> : S d + m = 1 * S d + m by lia.
  rewrite Nat.div_add_l.
    by lia.
  rewrite seq_last map_app map_cons.
  have -> : S d * (1 + m / S d) = S d + S d * (m / S d) by lia.
  move=> IHm. rewrite  -/(Nat.div m (S d)) - ? /(mult (S d) _).
  rewrite /plus -/plus.  
  rewrite - ? IHm.
  constructor; first last.
    f_equal. by lia.
  under (eq_lr (A' := m :: (A1 ++ A2)) (B' := m :: map (fun i : nat => i + d * i) (seq 0 (m / S d)))).
  all: rewrite -/(mset_eq _ _).
    by eq_trivial.
    by eq_trivial.
  by apply /eq_cons_iff.
Qed.

(* type 1 constraint satisfied by any sequence *)
Lemma seq_sat2 {d n} : 
  let A n := map (fun i => (S d) * i) (seq 0 n) in
  (A n) ++ [(S d) * n] ≡ [0] ++ (map (fun i => (S d) + i) (A n)).
Proof.
  move=> A. elim: n.
    apply /eq_eq. cbn. f_equal. by nia.
  move=> n IH.
  rewrite /A seq_last ? map_app -/(A n) /plus -/plus.
  rewrite /(map _ [n]) /(map _ [S d * n]).
  have -> : S (d + S d * n) = S d * S n by lia.
  under map_ext => i. rewrite -/(plus (S d) i). over.
  rewrite -/(mset_eq _ _).
  under (eq_lr 
    (A' := S d * S n :: (A n ++ [S d * n])) 
    (B' := S d * S n :: ([0] ++ map [eta Init.Nat.add (S d)] (A n)))).
    by eq_trivial.
    by eq_trivial.
  rewrite -/(mset_eq _ _).
  by apply /eq_cons_iff.
Qed.

Lemma seq_sat1 {n} : 
  (seq 0 n) ++ [n] ≡ [0] ++ (map S (seq 0 n)).
Proof.
  have -> : S = (fun i => (S 0) + i) by done.
  have -> : seq 0 n = map (fun i => (S 0) * i) (seq 0 n).
    elim: n.
      done.
    move=> n IH. rewrite seq_last map_app - IH => /=.
    by rewrite Nat.add_0_r.
  have -> : [n] = [1*n] by f_equal; lia.
  by apply: seq_sat2.
Qed.

Lemma unify_spec {A m n} : A ++ (map (fun i => 2 * i) (seq 0 m)) ≡ (seq 0 n) ++ map S A ->
  n = m.
Proof.
  move /eq_length.
  rewrite ? app_length ? map_length ? seq_length.
  by lia.
Qed.

Lemma unify_sat_aux {B n} : 
  Forall2 (fun i j => i >= j) B (seq 0 n) -> {A | A ++ B ≡ (seq 0 n) ++ map S A}.
Proof.
  elim /(induction_ltof1 _ (fold_right (fun x y => S (x + y)) 0)) : B n.
  rewrite /ltof.
  move=> B.
  case (list_eq_dec Nat.eq_dec B []).
    move=> -> ? ? /Forall2_nil_lE ->. by exists [].
  move /exists_last=> [C [a HC]]. subst B. move => IH. case.
    move=> /Forall2_nil_rE /app_eq_nil. by case.
  move=> n. rewrite seq_last /plus. move /Forall2_lastP => [HC Ha].
  have := gt_eq_gt_dec n a. case; first case; first last.
    move=> ?. exfalso. by lia.
    move=> ?. subst a. move: (IH C).
    apply: unnest_t.
      clear. elim: C=> /= *; by lia. 
    move /(_ _ ltac:(eassumption)) => [A HA]. exists A.
    under (eq_lr (A' := n :: (A ++ C)) (B' := n :: (seq 0 n ++ map S A))).
      by eq_trivial.
      by eq_trivial.
    rewrite -/(mset_eq _ _). by apply /eq_cons_iff.
  move=> ?.
  have HaSPa : a = S (Nat.pred a) by lia.
  move: (IH (C ++ [Nat.pred a])).
  apply: unnest_t.
    move: HaSPa. clear. elim: C => /= [|? ? IH /IH] ?; by lia.
  move /(_ (S n)). apply: unnest_t.
    rewrite seq_last /plus. apply /Forall2_lastP. constructor; by [|lia].
  move=> [A HA]. exists ((Nat.pred a) :: A).
  rewrite -seq_last /(map) -/(map _ _) - HaSPa.
  under (eq_lr (A' := a :: (A ++ C ++ [Nat.pred a])) (B' := a :: (seq 0 (S n) ++ map S A))).
    by eq_trivial.
    by eq_trivial.
  rewrite -/(mset_eq _ _). by apply /eq_cons_iff.
Qed.

Definition unify_sat n :
  {A | A ++ (map (fun i => 2*i) (seq 0 n)) ≡ (seq 0 n) ++ map S A}.
Proof.
  apply: unify_sat_aux. elim: n.
    by constructor.
  move=> n IH. rewrite ? seq_last map_app. apply: Forall2_app.
    done.
  constructor.
    by lia.
  done.
Qed.

(* embed nat^3 into nat to provide fresh variables *)
Definition embed '(x, y, z) := NatNat.nat2_to_nat (NatNat.nat2_to_nat (x, y), z).
Definition unembed n := let (xy, z) := NatNat.nat_to_nat2 n in
  (NatNat.nat_to_nat2 xy, z).


Lemma embed_unembed {xyz} : unembed (embed xyz) = xyz.
Proof. 
  case: xyz. case. move=> >.
  by rewrite /embed /unembed ? NatNat.nat_nat2_cancel.
Qed.

Opaque embed unembed.

Definition encode_bound (x: nat): FMsetC_PROBLEM :=
  let X n := embed (x, n, 0) in
    [
      ((X 1) ⊍ (X 2), •0 ⊍ (h (X 1))); (* X 1 = [0..n-1], X 2 = [n] *)
      ((X 3) ⊍ (X 4), •0 ⊍ (h (h (X 3)))); (* X 3 = [0,2,..2*(m-1)], X 4 = [2*m] *)
      ((X 5) ⊍ (X 3), (X 1) ⊍ (h (X 5))); (* n = m *)
      ((h (X 6)) ⊍ (X 0), (X 2) ⊍ ((X 6) ⊍ ((X 6) ⊍ ((X 6) ⊍ (X 6)))));
      ((h (h (X 7))) ⊍ (X 0), (X 4) ⊍ ((X 7) ⊍ ((X 7) ⊍ ((X 7) ⊍ (X 7))))) (* X 0 = [0..0] of length 2^n *)
    ].

Definition encode_bound_spec {φ x} : mset_sat φ (encode_bound x) -> 
  Forall (fun a => 0 = a) (φ (embed (x, 0, 0))).
Proof.
  rewrite /encode_bound /mset_sat ? Forall_norm /mset_sem.
  have -> (A) : map S (map S A) = map (fun i => (S 1) + i) A.
    by rewrite map_map.
  have -> : map S = map [eta Nat.add 1] by done.

  move=> [/seq_spec2 [n [/eq_length Hn ->]]].
  move=> [/seq_spec2 [m [/eq_length Hm ->]]].
  move=> [/eq_length]. rewrite ? app_length Hn Hm ? map_length ? seq_length => ?.
  have ? : n = m by lia. subst m. clear.
  have -> : [eta Nat.add 1] = S by done.
  have -> : 1 * n = n by lia.
  move=> [H1 H2]. by apply: nat_spec.
Qed.

(* [0] ++ [0,1] ++ [0,1,2] ++ ...*)
Definition pyramid n := flat_map (seq 0) (seq 0 n).

(* from a H10UC valuation φ construct a valuation for FMsetC *)
Definition construct_valuation (φ: nat -> nat) (n: nat): list nat :=
  match unembed n with
  | (x, 0, 0) => repeat 0 (4^(φ x))
  | (x, 1, 0) => seq 0 (φ x)
  | (x, 2, 0) => [(φ x)]
  | (x, 3, 0) => map (fun i => 2*i) (seq 0 (φ x))
  | (x, 4, 0) => [2*(φ x)]
  | (x, 5, 0) => proj1_sig (unify_sat (φ x))
  | (x, 6, 0) => tower 1 (φ x)
  | (x, 7, 0) => tower 2 (φ x)
  | (x, 0, 1) => repeat 0 (φ x)
  | (x, 1, 1) => repeat 0 (length (pyramid (φ x)))
  | (x, 2, 1) => repeat 0 (4^(φ x) - (φ x))
  | (x, 3, 1) => repeat 0 (4^(φ x) - (length (pyramid (φ x))))
  | (x, 4, 1) => seq 0 (φ x)
  | (x, 5, 1) => [(φ x)]
  | (x, 6, 1) => pyramid (φ x)
  | (x, 7, 1) => flat_map pyramid (seq 0 (φ x))
  | _ => []
  end.


Lemma encode_bound_sat {φ x} : 
  mset_sat (construct_valuation φ) (encode_bound x).
Proof.
  rewrite /encode_bound /mset_sat ? Forall_norm /mset_sem.
  rewrite /construct_valuation ? embed_unembed.
  pose A d n := map (fun i => (S d) * i) (seq 0 n).
  constructor.
    by apply: seq_sat1.
  constructor.
    have -> (X) : map S (map S X) = map (fun i => 2+i) X by rewrite map_map.
    by apply: seq_sat2.
  constructor.
    apply: proj2_sig (unify_sat _).
  constructor.
    have -> (n): [n] = [1*n] by f_equal; lia.
    by apply: nat_sat.
  rewrite map_map.
  by apply: nat_sat.
Qed.

(* each n : nat is represented by a multiset containing n zeroes *)
Definition encode_nat (x: nat) : FMsetC_PROBLEM :=
  let X n := embed (x, n, 1) in
    [
      (X 0 ⊍ X 2, mset_term_var (embed (x, 0, 0))); (* X 0 = [0..0] *)
      (X 1 ⊍ X 3, mset_term_var (embed (x, 0, 0))); (* X 1 = [0..0] *)
      (X 4 ⊍ X 5, •0 ⊍ (h (X 4))); (* X 4 = [0..m-1], X 5 = [m]*)
      (X 4 ⊍ X 6, X 0 ⊍ (h (X 6))); (* m = length (X 0), length (X 6) ~ m * m *)
      (X 6 ⊍ X 7, X 1 ⊍ (h (X 7))) (* length X 1 ~ m * m *)
    ].

(* auxiliary lemma for square_spec *)
Lemma square_spec_aux {n m A C} : C ++ (n :: A) ≡ (repeat 0 (S m)) ++ (map S A) -> 
exists A', A ≡ (seq 0 n) ++ A' /\ C ++ A' ≡ (repeat 0 m) ++ (map S A').
Proof.
elim: n A.
  move=> A. rewrite /repeat -/(repeat _).
  under (eq_lr (A' := 0 :: (C ++ A)) (B' := 0 :: ((repeat 0 m) ++ map S A))).
    by eq_trivial.
    by eq_trivial.
  move /eq_cons_iff=> ?. exists A. by constructor.
move=> n IH A /copy [/eq_in_iff /(_ (S n)) /iffLR].
apply: unnest. 
  apply /in_app_iff. right. by left.
move /in_app_iff. case.
  by move /(@repeat_spec _ _ _ _).
move /in_map_iff=> [n' [+ +]]. case=> ?. subst n'.
move /(@in_split _ _) => [A1 [A2 ?]]. subst A.

under (eq_lr (A' := S n :: (C ++ (n :: (A1 ++ A2)))) (B' := S n :: ((repeat 0 (S m)) ++ map S (A1 ++ A2)))).
  by eq_trivial.
  move=> c. rewrite ? map_app map_cons. move: c. by eq_trivial.
move /eq_cons_iff => /IH [A' [? ?]].
exists A'. constructor.
  rewrite seq_last.
  under (eq_lr (A' := n :: (A1 ++ A2)) (B' := n :: (seq 0 n ++ A'))).
    by eq_trivial.
    rewrite /plus. by eq_trivial.
  rewrite -/(mset_eq _ _). by apply /eq_cons_iff.
done.
Qed.

(* forces B to be a n zeroes and A to be of length in proportion to n squared *)
Lemma square_spec {n A} : (seq 0 n) ++ A ≡ (repeat 0 n) ++ (map S A) -> 
length A + length A + n = n * n.
Proof.
elim: n A.
  move=> A /=. by move=> /eq_symm /eq_mapE ->.
move=> n IH A. rewrite seq_last /plus -/plus.
under (eq_lr _ eq_refl (A' := seq 0 n ++ (n :: A))).
  by eq_trivial.
move /square_spec_aux => [A' [/eq_length + /IH]].
rewrite app_length seq_length. by lia. 
Qed.

(* if encode bound is satisfied, then there is a square relationship on length of solutions *)
Lemma encode_nat_spec {φ x} : mset_sat φ (encode_bound x) -> mset_sat φ (encode_nat x) -> 
  length (φ (embed (x, 1, 1))) + length (φ (embed (x, 1, 1))) + length (φ (embed (x, 0, 1))) = 
    length (φ (embed (x, 0, 1))) * length (φ (embed (x, 0, 1))).
Proof.
  move /encode_bound_spec.
  rewrite /mset_sat /encode_nat.
  rewrite ? Forall_norm /mset_sem.
  pose X n := φ (embed (x, n, 1)). rewrite - ? /(X _).
  move=> H.
  move=> [/eq_Forall_iff /(_ [eta eq 0]) /iffRL /(_ H)].
  rewrite Forall_norm=> [[HX0 _]].
  move=> [/eq_Forall_iff /(_ [eta eq 0]) /iffRL /(_ H)].
  rewrite Forall_norm=> [[? _]].
  have -> : map S (X 4) = map [eta Init.Nat.add 1] (X 4) by done.
  move=> [/seq_spec2 [n]].
  have -> : map [eta Init.Nat.mul 1] (seq 0 n) = map id (seq 0 n).
    under map_ext => i. have -> : 1*i = i by lia. over. done.
  rewrite map_id => [[Hn _]].
  move=> [/eq_symm /eq_trans] => /(_ ((seq 0 n) ++ X 6)). apply: unnest.
    by apply: eq_appI.
  move => HX6. have HlX0 : length (X 0) = n.
    move: HX6 => /eq_length. rewrite ? app_length map_length seq_length. by lia.
  move: HX6 => /eq_symm. have -> := Forall_repeat HX0. rewrite HlX0. 
  move /square_spec => ?.
  move /eq_length. rewrite ? app_length map_length repeat_length.
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
    by eq_trivial.
    by eq_trivial.
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
    by eq_trivial.
    by eq_trivial.
  rewrite -/(mset_eq _ _).
  apply: eq_appI.
    done.
  by apply: pyramid_shuffle.
Qed.

Lemma pyramid_length n : n + length (pyramid n) <= 4 ^ n.
Proof.
  elim: n.
    cbn. by lia.
  move=> n IH. 
  rewrite /pyramid seq_last /plus -/plus flat_map_concat_map map_app concat_app app_length.
  rewrite -flat_map_concat_map -/(pyramid _).
  rewrite /map /concat app_length seq_length. move=> /=.
  case: n IH.
    rewrite /Nat.pow. by lia.
  move=> n. have := Nat.pow_gt_1 4 (S n) ltac:(lia) ltac:(lia).
    by lia.
Qed.

Lemma encode_nat_sat {φ x} : 
  mset_sat (construct_valuation φ) (encode_nat x).
Proof.
  rewrite /encode_nat /mset_sat ? Forall_norm /mset_sem.
  rewrite /construct_valuation ? embed_unembed.
  constructor.
    rewrite - repeat_add. apply: eq_eq. f_equal.
    have := pyramid_length (φ x).
    by lia.
  constructor.
    rewrite - repeat_add. apply: eq_eq. f_equal.
    have := pyramid_length (φ x).
    by lia.
  constructor.
    by apply: seq_sat1.
  constructor.
    by apply: pyramid_shuffle.
  by apply: encode_nat_sat_aux.
Qed.

(* represent constraints of shape 1 + x + y * y = z *)
Definition encode_constraint x y z := 
  encode_bound x ++ encode_bound y ++ encode_bound z ++ 
  encode_nat x ++ encode_nat y ++ encode_nat z ++ 
  let x := embed (x, 0, 1) in
  let yy := embed (y, 1, 1) in
  let y := embed (y, 0, 1) in
  let z := embed (z, 0, 1) in
  [ (•0 ⊍ x ⊍ yy ⊍ yy ⊍ y, mset_term_var z) ].

(* if mset constraint has a solution, then uniform diophantine constraint is satisfied *)
Lemma encode_constraint_spec {φ x y z} :  
  mset_sat φ (encode_constraint x y z) -> 
  1 + length (φ (embed (x, 0, 1))) + length(φ (embed (y, 0, 1))) * length(φ (embed (y, 0, 1))) = length(φ (embed (z, 0, 1))).
Proof.
  rewrite /encode_constraint /mset_sat. rewrite ? (Forall_app_iff). rewrite - ? /(mset_sat _ _).
  move=> [Hx [Hy [Hz]]].
  move=> [/(encode_nat_spec Hx) ? [/(encode_nat_spec Hy) ? [/(encode_nat_spec Hz) ?]]].
  rewrite /mset_sat Forall_norm /mset_sem.
  move /eq_length. rewrite ? app_length.
  have -> : (length [0] = 1) by done.
  by lia.
Qed.

(* if uniform diophantine constraint is satisfied, then mset constraint has a solution *)
Lemma encode_constraint_sat {φ x y z} : 
  1 + (φ x) + (φ y) * (φ y) = (φ z) -> mset_sat (construct_valuation φ) (encode_constraint x y z).
Proof.
  move=> Hxyz.
  rewrite /encode_constraint /mset_sat ? Forall_app_iff Forall_singleton_iff.
  rewrite - ? /(mset_sat _ _).
  do 3 (constructor; first by apply: encode_bound_sat).
  do 3 (constructor; first by apply: encode_nat_sat).
  rewrite /mset_sem /construct_valuation ? embed_unembed.
  have ->: [0] = repeat 0 1 by done.
  rewrite - ? repeat_add. apply: eq_eq.
  f_equal. move: Hxyz=> <-. clear. elim: (φ y); clear.
    cbn. by lia.
  move=> φy IH. rewrite /pyramid seq_last /(plus 0 _) flat_map_concat_map map_app concat_app.
  rewrite -flat_map_concat_map -/(pyramid _).
  cbn. rewrite ? app_length seq_length. cbn. by lia.
Qed.


(* encode a single H10UC constraint as a list of FMsetC constraints *)
Definition encode_h10uc '(x, y, z) := encode_constraint x y z.

(* many-one reduction from H10UC to FMsetC *)
Theorem H10UC_to_FMsetC : H10UC_SAT ⪯ FMsetC_SAT.
Proof.
  exists (fun h10ucs => flat_map encode_h10uc h10ucs).
  move=> h10ucs. constructor.
  - move=> [φ Hφ]. 
    exists (construct_valuation φ).
    elim: h10ucs Hφ.
      done.
    move=> [[x y] z] h10cs IH.
    move /Forall_forall. rewrite Forall_cons_iff. move=> [Hxyz /Forall_forall /IH].
    move=> {}IH A B.
    rewrite /flat_map -/(flat_map _) in_app_iff. case; first last.
      by apply /IH.
    rewrite /encode_h10uc.
    have := @encode_constraint_sat φ x y z ltac:(done).
    rewrite /mset_sat Forall_forall. by apply.
  - move=> [φ]. rewrite - mset_satP /mset_sat. move=> Hφ.
    pose ψ := (fun x => length (φ (embed (x, 0, 1)))).
    exists ψ.
    rewrite - Forall_forall.
    elim: h10ucs Hφ.
      done.
    move=> [[x y] z] h10ucs IH. rewrite /flat_map -/(flat_map _) Forall_app_iff.
    rewrite /(encode_h10uc _).
    move=> [/encode_constraint_spec Hxyz /IH ?].
    by constructor.
Qed.

Check H10UC_to_FMsetC.
(* Print Assumptions H10UC_to_FMsetC. *)

From Undecidability Require Import Problems.TM.
From Undecidability Require Import Reductions.H10C_to_H10UC.

(* undecidability of FMsetC *)
Theorem FMsetC_undec : Halt ⪯ FMsetC_SAT.
Proof.
  apply (reduces_transitive H10UC_undec).
  apply H10UC_to_FMsetC.
Qed.

Check FMsetC_undec.
(* Print Assumptions FMsetC_undec. *)
