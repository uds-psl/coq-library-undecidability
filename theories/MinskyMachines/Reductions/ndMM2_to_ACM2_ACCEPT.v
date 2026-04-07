(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Utf8.

From Undecidability.MinskyMachines 
  Require Import ndMM2 ACM2 ACM2.acm2_utils.

From Undecidability.Synthetic
  Require Import Definitions ReducibilityFacts.

#[local] Set Implicit Arguments.

#[local] Theorem relative_reduction loc : @ndMM2_ACCEPT loc ⪯ @ACM2_ACCEPT (loc + bool).
Proof.
  apply reduces_dependent; exists.
  intros (Σ & p & (x,y)).
  exists (list_ndmm2_to_acm2 _ Σ,inl p,(x,y)).
  apply ndmm2_to_acm2_correctness.
Qed.

#[local] Theorem embed_reduction : @ACM2_ACCEPT (nat + bool) ⪯ @ACM2_ACCEPT nat.
Proof.
  apply reduces_dependent; exists.
  intros ((Σ,p),(x,y)).
  (* We define an embedding nat + bool → nat *)
  set (φ (p : nat + bool) :=
    match p with
    | inl n => 2+n
    | inr true => 0
    | inr false => 1
    end).
  set (ψ p :=
    match p with
    | 0 => inr true
    | 1 => inr false
    | S (S n) => inl n
    end).
  exists (map (acm2_instr_map φ) Σ, φ p,(x,y)).
  apply acm2_embed_correctness with (ψ := ψ).
  (* We prove the embedding property *)
  now intros [ | []].
Qed.

#[local] Hint Resolve reduces_transitive embed_reduction relative_reduction : core.

Theorem reduction : @ndMM2_ACCEPT nat ⪯ @ACM2_ACCEPT nat.
Proof. eauto. Qed.


