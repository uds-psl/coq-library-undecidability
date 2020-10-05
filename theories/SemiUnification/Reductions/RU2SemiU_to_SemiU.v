(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Reduction from:
    Uniform Two-inequality Semi-unification (RU2SemiU)
  to:
    Semi-unification (SemiU)
*)

Require Import List.
Import ListNotations.

Require Import Undecidability.SemiUnification.SemiU.
From Undecidability.SemiUnification.Util Require Import Facts.

Require Import ssreflect ssrfun ssrbool.

Require Import Undecidability.Synthetic.Definitions.

(* many-one reduction from right-uniform two-inequality semi-unification to semi-unification *)
Theorem reduction : RU2SemiU ⪯ SemiU.
Proof.
  exists (fun '(s0, s1, t) => [(s0, t); (s1, t)]).
  move=> [[s0 s1] t]. constructor.
  - move=> [φ] [ψ0] [ψ1] [Hψ0 Hψ1]. exists φ.
    rewrite -Forall_forall ?Forall_norm. 
    constructor; [by exists ψ0 | by exists ψ1].
  - move=> [φ]. rewrite -Forall_forall ?Forall_norm.
    move=> [[ψ0 Hψ0] [ψ1 Hψ1]]. by exists φ, ψ0, ψ1.
Qed.
