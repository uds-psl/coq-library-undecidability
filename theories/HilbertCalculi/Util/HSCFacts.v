From Stdlib Require Import List Lia.
Import ListNotations.
From Stdlib Require Import ssreflect ssrbool ssrfun. 

Require Import Undecidability.HilbertCalculi.HSC.

Set Default Goal Selector "!".

(* number of nodes in the syntax tree of a formula *)
Fixpoint size s := 
  match s with
  | var _ => 1
  | arr s t => S (size s + size t)
  end.

(* list of first k arguments *)
Fixpoint arguments (k: nat) (t: formula) :=
  match k with
  | 0 => []
  | S k => 
    match t with
    | var _ => []
    | arr s t => s :: (arguments k t)
    end
  end.

(* target after first k arguments *)
Fixpoint target (k: nat) (t: formula) :=
  match k with
  | 0 => t
  | S k => 
    match t with
    | var _ => t
    | arr _ t => target k t
    end
  end.

(* Hilbert-style calculus with derivation depth *)
Inductive der (Gamma: list formula) : nat -> formula -> Prop :=
  | der_var {ζ: nat -> formula} {s t: formula} {k n: nat} :
      In s Gamma ->
      Forall (der Gamma n) (arguments k (substitute ζ s)) ->
      target k (substitute ζ s) = t ->
      der Gamma (S n) t.

Lemma derE {n Gamma t} : der Gamma n t ->
  match n with
  | 0 => False
  | S m => 
      exists (ζ: nat -> formula) (s: formula) (k: nat),
        In s Gamma /\
        Forall (der Gamma m) (arguments k (substitute ζ s)) /\
        target k (substitute ζ s) = t
  end.
Proof. case=> *. do 3 eexists. by eauto. Qed.

Lemma der_mon {n m t Gamma} : der Gamma n t -> n <= m -> der Gamma m t.
Proof.
  elim: n m Gamma t; first by move=> > /derE.
  move=> n IH m Gamma t.
  move /derE => [ζ [s' [k']]] [? [? ?]] ?.
  have -> : m = S (Nat.pred m) by lia.
  apply: der_var; try eassumption.
  apply: Forall_impl; last by eassumption.
  move=> ? /IH. apply. by lia.
Qed.

Lemma target_S {r s t k} : target k r = arr s t -> target (S k) r = t.
Proof.
  elim: k r s t; first by move=> > /= ->.
  by move=> k IH [> /= |  > /= /IH <-].
Qed.

Lemma arguments_S {r s t k} : target k r = arr s t -> arguments (S k) r = (arguments k r) ++ [s].
Proof.
  elim: k r s t; first by move=> > /= ->.
  by move=> k IH [> /= |  > /= /IH <-].
Qed.

(* every hsc derivation has a depth *)
Lemma hsc_der {Gamma t} : hsc Gamma t -> exists n, der Gamma n t.
Proof.
  elim.
  - move=> ζ s /der_var => /(_ ζ (substitute ζ s) 0 0).
    move=> H. exists 1. apply: H; by [|constructor].
  - move=> s' t' _ [[|n1] /derE]; [done|].
    move=> + _ [[|n2] /derE]; [done|].
    move=> [ζ1 [s1 [k1 [Hs1 [? Hk1]]]]].
    move=> [ζ2 [s2 [k2 [? [? ?]]]]].
    exists (S (S (n1+n2))). apply: (der_var _ (ζ := ζ1) (s := s1) (k := S k1)).
    + done.
    + rewrite (arguments_S Hk1). apply /Forall_app. constructor.
      * apply: Forall_impl; last eassumption.
        move=> ? /der_mon. apply. by lia.
      * constructor; last done. 
        apply: der_var; last eassumption; first done.
        apply: Forall_impl; last eassumption.
        move=> ? /der_mon. apply. by lia.
    + apply: target_S. by eassumption.
Qed.
