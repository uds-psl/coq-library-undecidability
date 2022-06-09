
(* 
  Reduction from:
    Uniform Diophantine Constraint Solvability (H10UC_SAT)
  to:
    Uniform Diophantine Pair Constraint Solvability (H10UPC_SAT)
*)

Require Import List Lia Cantor.
Import ListNotations.

Require Import ssreflect ssrbool ssrfun.

Require Import Undecidability.DiophantineConstraints.H10C.

Set Default Goal Selector "!".

(* Uniform Diophantine pairs constraints are of shape:  
    (x, y) # (1 + x + y, (y²+y)/2)
   Uniform Diophantine constraints are of shape:
    1 + x + y * y = z

  Idea: We represent 1+x+y²=z as such: 
  (where a, b, c, t1, t2 are new variables):
  y(y+1)/2 = a
  a+a+1 = b ( = y(y+1) + 1 = y²+y+1)
  c+y+1 = b (-> c = y²)
  x+c+1 = z (-> z = 1+x+y²)

  This yields these constraints 
  (a,a) # (b,t1)
  (c,y) # (b,a)
  (c,x) # (z,t2)

  We use the following renaming scheme:
  <x,0> = x                          (used for x,y,z)
  <x,1> = (x²+x)/2                   (used for a (with y), t2 (with x))
  <x,2> = x²+x+1                     (used for b (with y))
  <x,3> = x²                         (used for c (with y))
  <x,4> = (k²+k)/2 where k=(x²+x)/2  (used for t1 (with y))
*)

Module Argument.

Definition c2_full (x: nat) : { y:nat | y + y = x * S x}.
Proof.
  elim: x; first by exists 0.
  move=> x [y Hy]. exists (y+x+1). nia.
Qed.

#[local] Notation c2 x := (sval (c2_full x)).
#[local] Notation c2_spec x := (svalP (c2_full x)).

(* fresh variable space *)
Notation var x t := (Cantor.to_nat (x, t)).
Opaque Cantor.to_nat Cantor.of_nat.

Section Reduction.
(* The instance of h10uc (which we are reducing from) *)
Context (ucs: list h10uc).

Definition h10uc_to_h10upcs (c : h10uc) : list h10upc := 
  let '(x, y, z) := c in
  let '(a, b, c, t1, t2) := (var y 1, var y 2, var y 3, var y 4, var x 1) in
  let '(x, y, z) := (var x 0, var y 0, var z 0) in
    [((a, a), (b, t1)); ((c, y), (b, a)); ((c, x), (z, t2))].

Definition upcs := flat_map h10uc_to_h10upcs ucs.

Section Transport.
(* The solution to cs *)
Context (φ: nat -> nat).
(* Proof that φ solves ucs *)
Context (Hφ : forall c, In c ucs -> h10uc_sem φ c). 

Definition φ' (xn: nat) : nat :=
  match Cantor.of_nat xn with
  | (x, 0) => φ x
  | (x, 1) => c2 (φ x)
  | (x, 2) => φ x * φ x + φ x + 1
  | (x, 3) => φ x * φ x
  | (x, 4) => c2 (c2 (φ x))
  | _ => 0
  end.

Lemma transport : forall c, In c upcs -> h10upc_sem φ' c.
Proof using Hφ.
  apply /Forall_forall /Forall_flat_map.
  move: Hφ => /Forall_forall.
  apply: Forall_impl => - [[x y] z] /= ?.
  constructor; [|constructor; [|constructor]]; last done.
  all: rewrite /φ' /= ?Cantor.cancel_of_to ?(c2_spec _); lia.
Qed.

End Transport.

Section InverseTransport.
(* The solution to f(cs) (f is the reduction function) *) 
Context (φ': nat -> nat).
(* Proof that φ' solves upcs *)
Context (Hφ' : forall c, In c upcs -> h10upc_sem φ' c). 

Definition φ (n:nat) : nat := φ' (var n 0). 

Lemma inverse_transport : forall c, In c ucs -> h10uc_sem φ c.
Proof using Hφ'.
  apply /Forall_forall.
  move: Hφ' => /Forall_forall /Forall_flat_map.
  apply: Forall_impl => - [[x y] z] /=.
  move=> /Forall_cons_iff [+] /Forall_cons_iff [+] /Forall_cons_iff [+ _].
  rewrite /φ /=. nia.
Qed.

End InverseTransport.
End Reduction.
End Argument.

Require Import Undecidability.Synthetic.Definitions.

(** Square Diophantine Constraint Solvability many-one reduces to Uniform Diophantine Constraint Solvability *)
Theorem reduction : H10UC_SAT ⪯ H10UPC_SAT.
Proof.
  exists Argument.upcs. split.
  - intros [φ Hφ]. exists (Argument.φ' φ). now apply Argument.transport.
  - intros [φ' Hφ']. exists (Argument.φ φ'). now apply Argument.inverse_transport.
Qed.
