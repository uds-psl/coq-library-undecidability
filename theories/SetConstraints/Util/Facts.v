(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

Require Import ssreflect ssrbool ssrfun.
Require Import Arith Psatz.
Require Import List.
Import ListNotations.

Set Default Proof Using "Type".

(* misc facts *)

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

(* duplicates argument *)
Lemma copy {A: Prop} : A -> A * A.
Proof. done. Qed.

Lemma eta_reduction {X Y: Type} (f: X -> Y) : (fun x => f x) = f.
Proof. done. Qed.

(* list facts *)

Lemma nil_or_ex_max (A : list nat) : A = [] \/ exists a, In a A /\ Forall (fun b => a >= b) A.
Proof.
  elim: A; first by left.
  move=> a A [-> | [b [? Hb]]]; right.
  - exists a. constructor; by [left | constructor].
  - case: (le_lt_dec a b)=> ?.
    + exists b. constructor; by [right | constructor].
    + exists a. constructor; first by left.
      constructor; first done.
      apply: Forall_impl Hb. by lia.
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

(* seq facts *)
Lemma seq_last start length : seq start (S length) = (seq start length) ++ [start + length].
Proof.
  by rewrite (ltac:(lia) : S length = length + 1) seq_app.
Qed.

(* repeat facts *)
Lemma repeat_add {X : Type} {x : X} {m n} : repeat x (m + n) = repeat x m ++ repeat x n.
Proof. elim: m; [done | by move=> ? /= ->]. Qed.

Lemma Forall_repeat {X: Type} {a} {A: list X} : Forall (fun b => a = b) A -> A = repeat a (length A).
Proof.
  elim: A; first done.
  move=> b A IH. rewrite Forall_norm => [[? /IH ->]]. subst b.
  cbn. by rewrite repeat_length.
Qed.

(* bijection between nat and nat * nat *)
Module NatNat.

(* bijection from nat * nat to nat *)
Definition encode '(x, y) : nat := 
  y + (nat_rec _ 0 (fun i m => (S i) + m) (y + x)).

(* bijection from nat to nat * nat *)
Definition decode (n : nat) : nat * nat := 
  nat_rec _ (0, 0) (fun _ '(x, y) => if x is S x then (x, S y) else (S y, 0)) n.

Lemma decode_encode {xy: nat * nat} : decode (encode xy) = xy.
Proof.
  move Hn: (encode xy) => n. elim: n xy Hn.
  { by move=> [[|?] [|?]]. }
  move=> n IH [x [|y [H]]] /=.
  { move: x => [|x [H]] /=; first done.
    by rewrite (IH (0, x)) /= -?H ?PeanoNat.Nat.add_0_r. }
  by rewrite (IH (S x, y)) /= -?H ?PeanoNat.Nat.add_succ_r.
Qed.

Lemma encode_non_decreasing (x y: nat) : x + y <= encode (x, y).
Proof. elim: x=> [| x IH] /=; [| rewrite Nat.add_succ_r /=]; by lia. Qed.

End NatNat.
