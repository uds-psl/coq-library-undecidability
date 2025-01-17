(* 
  Author(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Reduction from:
    Right-uniform Two-inequality Semi-unification (RU2SemiU)
  to:
    Left-uniform Two-inequality Semi-unification (LU2SemiU)
*)

From Stdlib Require Import List.

Require Import Undecidability.SemiUnification.SemiU.
From Undecidability.SemiUnification.Util Require Import Enumerable.

From Stdlib Require Import ssreflect ssrfun ssrbool.

Set Default Goal Selector "!".

Module Argument.
Definition embed_var (x: nat) := atom (to_nat (x, 0)).
  
(* two fresh variables *)
Definition z (b: bool) := atom (to_nat (0, if b then 2 else 1)).

Section RU2SemiU_LU2SemiU.
  Variables s0 s1 t: term. (* RU2SemiU instance *)

  (* LU2SemiU instance *)
  Definition s' := substitute embed_var (arr s0 s1).
  Definition t0' := arr (substitute embed_var t) (z false).
  Definition t1' := arr (z true) (substitute embed_var t).

  Section Transport.
    Variables φ ψ0 ψ1 : valuation.
    Variable Hψ0 : substitute ψ0 (substitute φ s0) = substitute φ t.
    Variable Hψ1 : substitute ψ1 (substitute φ s1) = substitute φ t.

    (* LU2SemiU valuation φ from RU2SemiU valuation φ' *)
    Definition φ' : valuation := fun x => 
      match of_nat x with
      | (x, 0) => substitute embed_var (φ x)
      | (0, 1) => substitute embed_var (substitute ψ0 (substitute φ s1))
      | (0, 2) => substitute embed_var (substitute ψ1 (substitute φ s0))
      | _ => atom x
      end.

    (* LU2SemiU valuations ψ from RU2SemiU valuations *)
    Definition ψ0' : valuation := fun x =>
      match of_nat x with
      | (x, 0) => substitute embed_var (ψ0 x)
      | _ => atom x
      end.
    
    Definition ψ1' : valuation := fun x =>
      match of_nat x with
      | (x, 0) => substitute embed_var (ψ1 x)
      | _ => atom x
      end.
    
    Lemma substitute_φ'P {r: term} :
      substitute φ' (substitute embed_var r) = substitute embed_var (substitute φ r).
    Proof. elim: r => [[| ?] | *] /=; [by rewrite /φ' ?enumP | by rewrite /φ' ?enumP | by f_equal]. Qed.

    Lemma substitute_ψ0'P {r: term} :
      substitute ψ0' (substitute embed_var r) = substitute embed_var (substitute ψ0 r).
    Proof. elim: r => [[| ?] | *] /=; [by rewrite /ψ0' ?enumP | by rewrite /ψ0' ?enumP | by f_equal]. Qed.

    Lemma substitute_ψ1'P {r: term} :
      substitute ψ1' (substitute embed_var r) = substitute embed_var (substitute ψ1 r).
    Proof. elim: r => [[| ?] | *] /=; [by rewrite /ψ1' ?enumP | by rewrite /ψ1' ?enumP | by f_equal]. Qed.

    (* if the given right-uniform semi-unification instance is solvable, 
      then so is the constructed left-uniform semi-unification instance *)
    Lemma transport : LU2SemiU (s', t0', t1').
    Proof using φ ψ0 ψ1 Hψ0 Hψ1.
      exists φ', ψ0', ψ1'. constructor.
      - rewrite /s' /t0' /=. congr arr; rewrite ?substitute_φ'P substitute_ψ0'P ?/φ' ?enumP; by congruence.
      - rewrite /s' /t1' /=. congr arr; rewrite ?substitute_φ'P substitute_ψ1'P ?/φ' ?enumP; by congruence.
    Qed.
  End Transport.

  Section Reflection.
    Variables φ' ψ0' ψ1' : valuation.
    Variable Hψ0' : substitute ψ0' (substitute φ' s') = substitute φ' t0'.
    Variable Hψ1' : substitute ψ1' (substitute φ' s') = substitute φ' t1'.

    Lemma substitute_embed_var {ξ r} : 
      substitute (fun x => ξ (to_nat (x, 0))) r = substitute ξ (substitute embed_var r).
    Proof.
      elim: r; [done | by move=> /=; congruence].
    Qed.
      
    (* if the constructed left-uniform semi-unification instance is solvable, 
      then so is given right-uniform semi-unification instance *)
    Lemma reflection : RU2SemiU (s0, s1, t).
    Proof using φ' ψ0' ψ1' Hψ0' Hψ1'.
      exists (fun x => φ' (to_nat (x, 0))), ψ0', ψ1'. move: Hψ0' Hψ1'.
      rewrite ?(substitute_embed_var (ξ := φ')) /s' /t0' /t1' /=.
      move=> ? ?. constructor; by congruence. 
    Qed.

  End Reflection.
End RU2SemiU_LU2SemiU.
End Argument.

Require Import Undecidability.Synthetic.Definitions.

(* many-one reduction from right-uniform two-inequality semi-unification 
  to left-uniform two-inequality semi-unification *)
Theorem reduction : RU2SemiU ⪯ LU2SemiU.
Proof.
  exists (fun '(s0, s1, t) => (Argument.s' s0 s1, Argument.t0' t, Argument.t1' t)).
  move=> [[? ?] ?]. constructor.
  - move=> [?] [?] [?] [? ?]. apply: Argument.transport; by eassumption.
  - move=> [?] [?] [?] [? ?]. apply: Argument.reflection; by eassumption.
Qed.
