(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland Informatics Campus, Saarland University, Saarbrücken, Germany
*)

(* 
  Reduction from:
    Simple Semi-unification (SSemiU)
  to:
    Semi-unification (SemiU)
*)

Require Import List.
Import ListNotations.

Require Import Undecidability.SemiUnification.SemiU.
From Undecidability.SemiUnification.Util Require Import Facts Enumerable.

Require Import ssreflect ssrfun ssrbool.

Module Argument.

(* make room for enough fresh variables *)
Definition embed_var (x: nat) := atom (to_nat (x, 2)).
Definition embed_lr (x: nat) (b: bool) := atom (to_nat (x, if b then 1 else 0)).

(* simple constraints to inequalities *)
Definition SSU_to_SU0 (p: list constraint) : inequality := 
  fold_right (fun '((a, x), (y, b)) '(s, t) => 
    if a then (s, t) else 
      (arr (arr (if b then (embed_lr y false) else (embed_var x)) (if b then (embed_var x) else (embed_lr y true))) s, 
        arr (embed_var y) t)) (atom (to_nat (0, 3)), atom (to_nat (0, 3))) p.

(* simple constraints to inequalities *)
Definition SSU_to_SU1 (p: list constraint) : inequality := 
  fold_right (fun '((a, x), (y, b)) '(s, t) => 
    if a then  
      (arr (arr (if b then (embed_lr y false) else (embed_var x)) (if b then (embed_var x) else (embed_lr y true))) s, 
        arr (embed_var y) t)
    else (s, t)) (atom (to_nat (0, 3)), atom (to_nat (0, 3))) p.

Definition src (t: term) := if t is arr s t then s else atom 0.

Definition tgt (t: term) := if t is arr s t then t else atom 0.

(* SemiU valuation φ from SSemiU valuation φ' *)
Definition φ (φ' : valuation) : valuation := fun x => 
  match of_nat x with
  | (x, 2) => substitute embed_var (φ' x)
  | _ => atom x
  end.

(* SemiU valuation ψ from SSemiU valuations φ' and ψ' *)
Definition ψ (φ' ψ' : valuation) : valuation := fun x =>
  match of_nat x with
  | (x, 2) => substitute embed_var (ψ' x)
  | (x, 1) => substitute embed_var (tgt (φ' x))
  | (x, 0) => substitute embed_var (src (φ' x))
  | _ => atom x
  end.

Lemma substitute_ψP {φ' ψ': valuation} {t: term} :
  substitute (ψ φ' ψ') (substitute embed_var t) = substitute embed_var (substitute ψ' t).
Proof. elim: t => [x | *] /=; [by rewrite /ψ ?enumP | by f_equal]. Qed.

(* if the given simple semi-unification instance is solvable, 
  then so is the constructed semi-unification instance *)
Lemma soundness {p: list constraint} : SSemiU p -> SemiU [SSU_to_SU0 p; SSU_to_SU1 p].
Proof.
  move=> [φ'] [ψ0'] [ψ1'] /Forall_forall Hp. exists (φ φ').
  move=> ? /=. case; [| case; [| done]]; move=> <-.
  { move Hst: (SSU_to_SU0 p) => [s t]. exists (ψ φ' ψ0').
    elim: p s t Hst Hp.
      move=> > /= [] <- <- _. by rewrite /φ /ψ /= ?enumP /= ?enumP.
    move=> [[a x] [y b]] p IH ? ? /=. move Hst: (SSU_to_SU0 p) => [s t].
    case: a; case=> <- <-; rewrite Forall_norm.
      move=> [_ /IH]. by apply.
    move=> [Hxy /IH {}IH] /=. f_equal; last by apply: IH.
    case: b Hxy; clear; rewrite /φ /= ?enumP.
      move Hy: (φ' y) => r. case: r Hy; first done.
      move=> s t Hy ?. subst t => /=. 
      f_equal; [by rewrite /ψ ?enumP Hy | by apply: substitute_ψP].
    move Hy: (φ' y) => r. case: r Hy; first done.
    move=> s t Hy ?. subst s => /=. 
    f_equal; [by apply: substitute_ψP | by rewrite /ψ ?enumP Hy]. }
  { move Hst: (SSU_to_SU1 p) => [s t]. exists (ψ φ' ψ1').
    elim: p s t Hst Hp.
      move=> > /= [] <- <- _. by rewrite /φ /ψ /= ?enumP /= ?enumP.
    move=> [[a x] [y b]] p IH ? ? /=. move Hst: (SSU_to_SU1 p) => [s t].
    case: a; case=> <- <-; rewrite Forall_norm; first last. 
      move=> [_ /IH]. by apply.
    move=> [Hxy /IH {}IH] /=. f_equal; last by apply: IH.
    case: b Hxy; clear; rewrite /φ /= ?enumP.
      move Hy: (φ' y) => r. case: r Hy; first done.
      move=> s t Hy ?. subst t => /=. 
      f_equal; [by rewrite /ψ ?enumP Hy | by apply: substitute_ψP].
    move Hy: (φ' y) => r. case: r Hy; first done.
    move=> s t Hy ?. subst s => /=. 
    f_equal; [by apply: substitute_ψP | by rewrite /ψ ?enumP Hy]. }
Qed.

(* if the the constructed semi-unification instance is solvable, 
  then so is given simple semi-unification instance *)
Lemma completeness {p: list constraint} : SemiU [SSU_to_SU0 p; SSU_to_SU1 p] -> SSemiU p.
Proof.
  rewrite /SSemiU /SemiU. move=> [φ]. rewrite -Forall_forall ? Forall_norm /solution.
  move Hst0: (SSU_to_SU0 p) => [s0 t0]. move Hst1: (SSU_to_SU1 p) => [s1 t1].
  move=> [[ψ0 Hψ0] [ψ1 Hψ1]].
  exists (fun x => φ (to_nat (x, 2))), ψ0, ψ1. rewrite -Forall_forall.
  elim: p s0 t0 Hst0 s1 t1 Hst1 Hψ0 Hψ1; first done.
  move=> [[a x] [y b]] p IH s0 t0 + s1 t1 => /=.
  move Hst0': (SSU_to_SU0 p) => [s0' t0']. move Hst1': (SSU_to_SU1 p) => [s1' t1'].
  rewrite Forall_norm. 
  move: a => [|] [] <- <- [] <- <- /=.
  - move: b => [|] ? [] <- ?; (constructor; [done | apply: IH; by eassumption]).
  - move: b => [|] [] <- ? ?; (constructor; [done | apply: IH; by eassumption]).
Qed.

End Argument.

Require Import Undecidability.Synthetic.Definitions.

(* many-one reduction from simple semi-unification to semi-unification *)
Theorem reduction : SSemiU ⪯ SemiU.
Proof.
  exists (fun p => [Argument.SSU_to_SU0 p; Argument.SSU_to_SU1 p]).
  intro p. constructor.
  - exact Argument.soundness.
  - exact Argument.completeness.
Qed.
