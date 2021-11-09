(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Reduction from:
    Diophantine Constraint Solvability (H10C_SAT)
  to:
    Square Diophantine Constraint Solvability (H10SQC_SAT)
*)

Require Import List Lia.
Import ListNotations.

Require Import Undecidability.DiophantineConstraints.H10C.

Require Import ssreflect ssrbool ssrfun.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

Module Argument.

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

Opaque encode decode.

Lemma ForallE {X : Type} {P : X -> Prop} {l} : 
  Forall P l -> if l is x :: l then P x /\ Forall P l else True.
Proof. by case. Qed.

Section Reduction.
(* given instance of Diophantine constraint solvability *)
Context (cs: list h10c).

(* variable renaming *)
Definition ζ (x: nat) := encode (x, 0).

(*  
  fresh variables
  θ x y 0 ~ x^2
  θ x y 1 ~ y^2
  θ x y 2 ~ x^2 + y^2
  θ x y 3 ~ x + y
  θ x y 4 ~ (x + y)^2
  θ x y 5 ~ 2xy
*)
Definition θ (x y t: nat) := encode (x, 1 + encode (y, t)).

(* x * y = z <-> x^2 + 2z + y^2 = (x + y)^2 *)
Definition h10c_to_h10sqcs (c : h10c) : list h10sqc :=
  match c with
  | h10c_one x      => [h10sqc_one (ζ x)]
  | h10c_plus x y z => [h10sqc_plus (ζ x) (ζ y) (ζ z)]
  | h10c_mult x y z => [
      h10sqc_sq (ζ x) (θ x y 0); h10sqc_sq (ζ y) (θ x y 1); h10sqc_plus (θ x y 0) (θ x y 1) (θ x y 2);
      h10sqc_plus (ζ x) (ζ y) (θ x y 3); h10sqc_sq (θ x y 3) (θ x y 4);
      h10sqc_plus (ζ z) (ζ z) (θ x y 5); h10sqc_plus (θ x y 2) (θ x y 5) (θ x y 4)]
  end.

(* constructed instance of square Diophantine constraint solvability *)
Definition sqcs := flat_map h10c_to_h10sqcs cs.

Section Transport.
(* solution of the given instance cs *)
Context (φ : nat -> nat) (Hφ: forall c, In c cs -> h10c_sem c φ).

(* solution of the constructed instance sqcs *)
Definition φ' (n: nat) := 
  match decode n with
  | (x, 0) => φ x
  | (x, S m) =>
    match decode m with
    | (y, 0) => (φ x) * (φ x)
    | (y, 1) => (φ y) * (φ y)
    | (y, 2) => (φ x) * (φ x) + (φ y) * (φ y)
    | (y, 3) => (φ x) + (φ y)
    | (y, 4) => ((φ x) + (φ y)) * ((φ x) + (φ y))
    | (y, 5) => (φ x) * (φ y) + (φ x) * (φ y)
    | (_, _) => 0
    end
  end.

Lemma h10c_to_h10sqcs_spec {c} : h10c_sem c φ -> Forall (h10sqc_sem φ') (h10c_to_h10sqcs c).
Proof.
  case: c => /=.
  - move=> x ?. constructor; last done.
    by rewrite /= /ζ /φ' decode_encode.
  - move=> x y z ?. constructor; last done.
    by rewrite /= /ζ /φ' ?decode_encode.
  - move=> x y z ?. (do ? constructor);
      rewrite /= /ζ /φ' ?decode_encode /= ?decode_encode; by nia.
Qed.

End Transport.

Lemma transport : H10C_SAT cs -> H10SQC_SAT sqcs.
Proof.
  move=> [φ Hφ]. exists (φ' φ).
  move: Hφ. rewrite -?Forall_forall /sqcs Forall_flat_map.
  apply: Forall_impl => ?. by move /h10c_to_h10sqcs_spec.
Qed.

Section InverseTransport.
(* solution of the constructed instance sqcs *)
Context (φ' : nat -> nat) (Hφ': forall c, In c sqcs -> h10sqc_sem φ' c).

(* solution of the given instance cs *)
Definition φ (x: nat) := φ' (ζ x).

Lemma h10c_of_h10sqcs_spec {c} : Forall (h10sqc_sem φ') (h10c_to_h10sqcs c) -> h10c_sem c φ.
Proof.
  case: c => /=.
  - by move=> x /ForallE [].
  - by move=> x y z /ForallE [].
  - move=> x y z. do 7 (move=> /ForallE /and_comm []).
    rewrite /= /φ. by nia.
Qed.

End InverseTransport.

Lemma inverse_transport : H10SQC_SAT sqcs -> H10C_SAT cs.
Proof.
  move=> [φ' Hφ']. exists (φ φ').
  move: Hφ'. rewrite -?Forall_forall /sqcs Forall_flat_map.
  apply: Forall_impl => ?. by move=> /h10c_of_h10sqcs_spec.
Qed.

End Reduction.
End Argument.

Require Import Undecidability.Synthetic.Definitions.

(** Diophantine Constraint Solvability many-one reduces to Square Diophantine Constraint Solvability *)
Theorem reduction : H10C_SAT ⪯ H10SQC_SAT.
Proof.
  exists (fun cs => Argument.sqcs cs) => cs. constructor.
  - exact: Argument.transport.
  - exact: Argument.inverse_transport.
Qed.
