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
  Require Import ACM2.

From Undecidability.BI
  Require Import BI Utils.bi_utils.

From Undecidability.Synthetic
  Require Import Definitions ReducibilityFacts.

Set Implicit Arguments.

#[local] Theorem relative_reduction loc : @ACM2_ACCEPT loc ⪯ @BI_SEQ_PROVABLE_cut_free (loc + bool)%type.
Proof.
  apply reduces_dependent; exists.
  intros (Σ & p & (x,y)).
  exists (BI_list_mult (acm2_ctx_to_BI Σ (map (@acm2_instr_src _) Σ) x y),BI_form_var (inl p)).
  apply acm2_to_BI_correctness.
Qed.

#[local] Theorem embed_reduction : @BI_SEQ_PROVABLE_cut_free (nat + bool)%type ⪯ @BI_SEQ_PROVABLE_cut_free nat.
Proof.
  apply reduces_dependent; exists.
  intros (Σ & A).
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
  exists (BI_bunch_map φ Σ, BI_form_map φ A).
  apply BI_embed_correctness with (ψ := ψ).
  (* We prove the embedding property *)
  now intros [ | []].
Qed.

#[local] Hint Resolve reduces_transitive embed_reduction relative_reduction : core.

Theorem reduction : @ACM2_ACCEPT nat ⪯ @BI_SEQ_PROVABLE_cut_free nat.
Proof. eauto. Qed.
