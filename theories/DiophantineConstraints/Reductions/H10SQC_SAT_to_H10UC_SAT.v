(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Reduction from:
    Square Diophantine Constraint Solvability (H10SQC_SAT)
  to:
    Uniform Diophantine Constraint Solvability (H10UC_SAT)
*)

Require Import List Lia.
Require Cantor.
Import ListNotations.

Require Import Undecidability.DiophantineConstraints.H10C.

Require Import ssreflect ssrbool ssrfun.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

Module Argument.

Notation encode := Cantor.to_nat.
Notation decode := Cantor.of_nat.
Opaque Cantor.to_nat Cantor.of_nat.

Section Reduction.
(* given instance of square Diophantine constraint solvability *)
Context (sqcs: list h10sqc).

(* fresh variables
  ζ x 0 ~ x
  ζ x 1 ~ 1 + x
  ζ x 2 ~ 1 + (1 + x)^2
  ζ x 3 ~ 1 + 2x *)
Definition ζ (x t: nat) := encode (1 + x, encode (0, t)).

(* fresh variables
  θ x y 0 ~ 2 + 2x + (1 + y)^2
  θ x y 1 ~ 2 + 2x + 2y
  θ x y 2 ~ 2 + (1 + x + y)^2 *)
Definition θ (x y t: nat) := encode (1 + x, encode (1 + y, t)).

(* values 0, 1, 2 *)
Definition v (t: nat) := encode (0, t).

(* v 0 ~ 0, v 1 ~ 1, v 2 ~ 2 via
  1 + (v 0) + (v 1) * (v 1) = (v 2),
  1 + (v 1) + (v 0) * (v 0) = (v 2),  
  1 + (v 0) + (v 0) * (v 0) = (v 1) *)
Definition v012 := [(v 0, v 1, v 2); (v 1, v 0, v 2); (v 0, v 0, v 1)].

(* x^2 = y ~ 1 + 0 + x^2 = 1 + y + 0^2
   x + y = z ~
   1 + 0 + (1 + x)^2 = 1 + u + x^2
   1 + u + (1 + y)^2 = 1 + v + y^2
   1 + 1 + (1 + z)^2 = 1 + v + z^2 *)
Definition h10sqc_to_h10ucs (c : h10sqc) : list h10uc :=
  match c with
  | h10sqc_one x => [(v 0, v 0, ζ x 0)]
  | h10sqc_sq x y => [(v 0, ζ x 0, ζ y 1); (ζ y 0, v 0, ζ y 1)]
  | h10sqc_plus x y z => [
      (ζ x 0, v 0, ζ x 1); (v 0, ζ x 1, ζ x 2); (ζ x 3, ζ x 0, ζ x 2);
      (ζ y 0, v 0, ζ y 1); (ζ x 3, ζ y 1, θ x y 0); (θ x y 1, ζ y 0, θ x y 0);
      (ζ z 0, v 0, ζ z 1); (v 1, ζ z 1, θ x y 2); (θ x y 1, ζ z 0, θ x y 2)]
  end.

(* constructed instance of uniform Diophantine constraint solvability *)
Definition ucs := v012 ++ flat_map h10sqc_to_h10ucs sqcs.

Section Transport.
(* solution of the given instance sqcs *)
Context (φ : nat -> nat) (Hφ: forall c, In c sqcs -> h10sqc_sem φ c).

(* solution of the constructed instance ucs *)
Definition φ' (n: nat) := 
  match decode n with
  | (0, 0) => 0
  | (0, 1) => 1
  | (0, 2) => 2
  | (0, _) => 0
  | (S x, m) => 
    match decode m with
    | (0, 0) => (φ x)
    | (0, 1) => 1 + (φ x)
    | (0, 2) => 1 + (1 + (φ x)) * (1 + (φ x))
    | (0, 3) => 1 + (φ x) + (φ x)
    | (S y, 0) => 2 + (φ x) + (φ x) + (1 + (φ y)) * (1 + (φ y))
    | (S y, 1) => 2 + (φ x) + (φ x) + (φ y) + (φ y)
    | (S y, 2) => 2 + (1 + (φ x) + (φ y)) * (1 + (φ x) + (φ y))
    | (_, _) => 0
    end
  end.

Lemma h10sqc_to_h10ucs_spec {c} : h10sqc_sem φ c -> Forall (h10uc_sem φ') (h10sqc_to_h10ucs c).
Proof.
  case: c => /=.
  - move=> x ?. constructor; last done.
    rewrite /= /ζ /φ' /v ?Cantor.cancel_of_to /=. by lia.
  - move=> x y z ?. (do ? constructor);
      rewrite /= /ζ /φ' /θ ?Cantor.cancel_of_to /=; by nia.
  - move=> x y ?. (do ? constructor);
      rewrite /= /ζ /φ' ?Cantor.cancel_of_to /=; by nia.
Qed.

End Transport.

Lemma transport : H10SQC_SAT sqcs -> H10UC_SAT ucs.
Proof.
  move=> [φ Hφ]. exists (φ' φ).
  move: Hφ. rewrite -?Forall_forall /ucs Forall_app Forall_flat_map.
  move=> H. constructor.
  - by do ? constructor.
  - apply: Forall_impl H => ?. by move /h10sqc_to_h10ucs_spec.
Qed.

Section InverseTransport.
(* solution of the constructed instance ucs *)
Context (φ' : nat -> nat) (Hφ': forall c, In c ucs -> h10uc_sem φ' c).

(* solution of the constructed given sqcs *)
Definition φ (x: nat) := φ' (ζ x 0).

Lemma v_spec : φ' (v 0) = 0 /\ φ' (v 1) = 1.
Proof using Hφ'.
  move: (Hφ'). rewrite -Forall_forall /ucs Forall_app /v012.
  move=> [/Forall_cons_iff [+]] /Forall_cons_iff [+] /Forall_cons_iff [+] _ _ => /=.
  by nia.
Qed.

Lemma h10sqc_of_h10ucs_spec {c} : Forall (h10uc_sem φ') (h10sqc_to_h10ucs c) -> h10sqc_sem φ c.
Proof using Hφ'.
  case: c => /=.
  - move=> x /Forall_cons_iff []. rewrite /= ?(proj1 v_spec) /φ. by lia.
  - move=> x y z. do 9 (move=> /Forall_cons_iff /and_comm []).
    rewrite /= ?(proj1 v_spec) ?(proj2 v_spec) /φ. by lia. 
  - move=> x y /Forall_cons_iff [+] /Forall_cons_iff [+ _]. rewrite /= ?(proj1 v_spec) /φ. by lia.
Qed.

End InverseTransport.

Lemma inverse_transport : H10UC_SAT ucs -> H10SQC_SAT sqcs.
Proof.
  move=> [φ' Hφ']. exists (φ φ').
  move: (Hφ'). rewrite -?Forall_forall /ucs Forall_app Forall_flat_map.
  move=> [?]. apply: Forall_impl => ?. by apply: h10sqc_of_h10ucs_spec.
Qed.

End Reduction.
End Argument.

Require Import Undecidability.Synthetic.Definitions.

(** Square Diophantine Constraint Solvability many-one reduces to Uniform Diophantine Constraint Solvability *)
Theorem reduction : H10SQC_SAT ⪯ H10UC_SAT.
Proof.
  exists (fun sqcs => Argument.ucs sqcs) => sqcs. constructor.
  - exact: Argument.transport.
  - exact: Argument.inverse_transport.
Qed.
