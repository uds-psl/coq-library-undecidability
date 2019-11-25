(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland Informatics Campus, Saarland University, Saarbrücken, Germany
*)

Require Import ssreflect ssrbool ssrfun.
Require Import Arith Psatz.
Require Import List.
Import ListNotations.

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

Lemma Forall_flat_mapP {X Y: Type} {P: Y -> Prop} {f: X -> list Y} {A: list X}: 
  Forall P (flat_map f A) <-> Forall (fun a => Forall P (f a)) A.
Proof.
  elim: A.
    move=> /=. by constructor.
  move=> a A IH. by rewrite /flat_map -/(flat_map _ _) ? Forall_norm IH.
Qed.

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

Lemma nat_to_nat2_snd_non_increasing {n} : snd (nat_to_nat2 n) < S n.
Proof.
  elim: n=> [|n] //=.
  move: (nat_to_nat2 n) => [x y]. case: x => [|x] /=; by lia.
Qed.

(* bijection from nat to list nat *)
Definition nat_to_list := Fix lt_wf _ (fun (n: nat) =>
  match n return ((forall y : nat, y < n -> list nat) -> list nat) with
  | 0 => fun _ => []
  | S n => fun f => (fst (nat_to_nat2 n)) :: (f (snd (nat_to_nat2 n)) nat_to_nat2_snd_non_increasing)
  end).

Lemma nat_to_list_S_nP {n} : 
  nat_to_list (S n) = (fst (nat_to_nat2 n)) :: (nat_to_list (snd (nat_to_nat2 n))).
Proof.
  rewrite /nat_to_list Fix_eq=> //. elim=> // *; by f_equal.
Qed.
  
(* bijection from list nat to nat *)
Fixpoint list_to_nat (A: list nat) : nat :=
  if A is a :: A then S (nat2_to_nat (a, list_to_nat A)) else 0.
  
Lemma nat_list_cancel {A} : nat_to_list (list_to_nat A) = A.
Proof.
  elim: A=> // *.
  rewrite /list_to_nat nat_to_list_S_nP nat_nat2_cancel. by f_equal.
Qed.
  
Lemma list_nat_cancel {n} : list_to_nat (nat_to_list n) = n.
Proof.
  elim /lt_wf_ind: n. case=> //.
  move=> ? IH. rewrite nat_to_list_S_nP /list_to_nat -/list_to_nat IH.
    by apply: nat_to_nat2_snd_non_increasing.
  by rewrite - surjective_pairing nat2_nat_cancel.
Qed.

Lemma nat_to_nat2_non_increasing {n} : fst (nat_to_nat2 n) + snd (nat_to_nat2 n) < S n.
Proof.
  elim: n=> [|n] //=.
  move: (nat_to_nat2 n) => [x y].
  case: y => [|y]; case: x => [|x] /=; by lia.
Qed.

Inductive tree : Set :=
  | leaf : tree
  | node : nat -> tree -> tree -> tree.

Fixpoint tree_to_nat (t: tree) : nat :=
  match t with
  | leaf => 0
  | node n t u => S (nat2_to_nat (n, nat2_to_nat ((tree_to_nat t), (tree_to_nat u))))
  end.

Lemma nat_to_tree_fst_lt {n} : (fst (nat_to_nat2 (snd (nat_to_nat2 n)))) < S n.
Proof. 
  have ? := @nat_to_nat2_non_increasing n.
  have ? := @nat_to_nat2_non_increasing (snd (nat_to_nat2 n)).
  by lia.
Qed.

Lemma nat_to_tree_snd_lt {n} : (snd (nat_to_nat2 (snd (nat_to_nat2 n)))) < S n.
Proof. 
  have ? := @nat_to_nat2_non_increasing n.
  have ? := @nat_to_nat2_non_increasing (snd (nat_to_nat2 n)).
  by lia.
Qed.
  
Definition nat_to_tree : nat -> tree.
Proof.
  apply: (Fix lt_wf _). case.
    exact (fun _ => leaf).
  move=> n f.
  pose m := snd (nat_to_nat2 n).
  refine (node (fst (nat_to_nat2 n)) (f (fst (nat_to_nat2 m)) _) (f (snd (nat_to_nat2 m)) _)).
    exact nat_to_tree_fst_lt.
  exact nat_to_tree_snd_lt.
Defined.

Lemma nat_to_tree_S_nP {n} : 
  nat_to_tree (S n) = 
    node (fst (nat_to_nat2 n)) 
      (nat_to_tree (fst (nat_to_nat2 (snd (nat_to_nat2 n)))))
      (nat_to_tree (snd (nat_to_nat2 (snd (nat_to_nat2 n))))).
Proof.
  rewrite /nat_to_tree Fix_eq=> //. elim=> // *. by f_equal.
Qed.
    
Lemma nat_tree_cancel {t} : nat_to_tree (tree_to_nat t) = t.
Proof.
  elim: t=> // *.
  rewrite /tree_to_nat nat_to_tree_S_nP nat_nat2_cancel.
  rewrite -/tree_to_nat /fst /snd -/(fst _) -/(snd _) nat_nat2_cancel. 
  by f_equal.
Qed.
    
Lemma tree_nat_cancel {n} : tree_to_nat (nat_to_tree n) = n.
Proof.
  elim /lt_wf_ind: n. case=> //.
  move=> n IH. rewrite nat_to_tree_S_nP /tree_to_nat -/tree_to_nat ? IH.
    1,2: have ? := @nat_to_nat2_non_increasing n.
    1,2: have ? := @nat_to_nat2_non_increasing (snd (nat_to_nat2 n)).
    1,2: by lia.
  rewrite - surjective_pairing nat2_nat_cancel.
  by rewrite - surjective_pairing nat2_nat_cancel.
Qed.

End NatNat.
