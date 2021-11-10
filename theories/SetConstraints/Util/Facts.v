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
Set Default Goal Selector "!".

(* misc facts *)

(* induction/recursion principle wrt. a decreasing measure f *)
(* example: elim /(measure_rect length) : l. *)
Lemma measure_rect {X : Type} (f : X -> nat) (P : X -> Type) : 
  (forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
  exact: (well_founded_induction_type (Wf_nat.well_founded_lt_compat X f _ (fun _ _ => id)) P).
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
Lemma count_occ_cons {X : Type} {D : forall x y : X, {x = y} + {x <> y}} {A a c}:
count_occ D (a :: A) c = count_occ D (locked [a]) c + count_occ D A c.
Proof.
  rewrite /count_occ /is_left -lock. by case: (D a c).
Qed.

(* Forall facts *)
Lemma Forall_singleton_iff {X: Type} {P: X -> Prop} {x} : Forall P [x] <-> P x.
Proof.
  rewrite Forall_cons_iff. by constructor; [case |].
Qed.

(* usage: rewrite ? Forall_norm *)
Definition Forall_norm := (@Forall_app, @Forall_singleton_iff, @Forall_cons_iff, @Forall_nil_iff).

(* seq facts *)
Lemma seq_last start length : seq start (S length) = (seq start length) ++ [start + length].
Proof.
  by rewrite (ltac:(lia) : S length = length + 1) seq_app.
Qed.

(* repeat facts *)
Lemma Forall_repeat {X: Type} {a} {A: list X} : Forall (fun b => a = b) A -> A = repeat a (length A).
Proof.
  elim: A; first done.
  move=> b A IH. rewrite Forall_norm => [[? /IH ->]]. subst b.
  cbn. by rewrite repeat_length.
Qed.
