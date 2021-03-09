
(* 
  Reduction from:
    Uniform Diophantine Constraint Solvability (H10UC_SAT)
  to:
    Uniform Diophantine Pair Constraint Solvability (H10UPC_SAT)
*)

Require Import List Lia.
Import ListNotations.

Require Import Undecidability.DiophantineConstraints.H10C.
Require Import Undecidability.DiophantineConstraints.H10UPC.

Set Default Proof Using "Type".
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
  (3 suffice (!) since we can merge constraint 1 and 3 
     into the same pair-constraint)
  (a,a) # (b,t1)
  (c,y) # (b,a)
  (c,x) # (z,t2)

  We use the following renaming scheme:
  <x,v0> = x                          (used for x,y,z)
  <x,v1> = (x²+x)/2                   (used for a (with y), t2 (with x))
  <x,v2> = x²+x+1                     (used for b (with y))
  <x,v3> = x²                         (used for c (with y))
  <x,v4> = (k²+k)/2 where k=(x²+x)/2  (used for t1 (with y))

  *)

Module Argument.

Definition c2_full (x:nat) : {y:nat | x * S x = y+y}.
Proof.
  induction x as [|x [y' IH]].
  - exists 0. lia.
  - exists (y'+x+1). nia.
Defined.

Definition c2 (x:nat) := match (c2_full x) with exist _ y _ => y end.

Definition c2_descr (x:nat) : x * S x = c2 x + c2 x.
Proof.
unfold c2. now destruct (c2_full x).
Qed. 

(* We generate 5 new variables for each variable. 
   The following type encodes the choices *)
Inductive fin5 := v0 | v1 | v2 | v3 | v4.
Definition fin2nat y := match y with v0=>0|v1=>1|v2=>2|v3=>3|v4=>4 end.
Definition encode5 '(x,y) := x*5+fin2nat y.
Fixpoint decode5 k := match k with 
          0 => (0,v0) 
        | 1 => (0,v1) 
        | 2 => (0,v2) 
        | 3 => (0,v3) 
        | 4 => (0,v4) 
        | S(S(S(S(S kk)))) => let '(x,y) := decode5 kk in (S x,y) end.

Lemma decode_encode x y : decode5 (encode5 (x,y)) = (x,y).
Proof.
  induction x as [|x IH].
  - now destruct y.
  - cbn. destruct (decode5 (x*5+fin2nat y)) as [x' y'] eqn:Heq. 
    change (x*5+fin2nat y) with (encode5 (x,y)) in Heq. congruence.
Qed.

Opaque decode5 encode5.

Section Reduction.
Definition rename x := encode5 (x,v0).
Definition newvar x t := encode5 (x,t).

Definition h10uc_to_h10upc_single : h10uc -> list h10upc := (fun '(x,y,z) => 
  let '(a,b,c,t1,t2) := 
            (newvar y v1,newvar y v2,newvar y v3,newvar y v4,newvar x v1) in
  let '(x,y,z) := (rename x,rename y,rename z) in
  [((a,a),(b,t1)); ((c,y),(b,a)); ((c,x),(z,t2))]).

Definition h10uc_to_h10upc := flat_map h10uc_to_h10upc_single.

End Reduction.

Section Transport.
(* The instance of h10uc (which we are reducing from) *)
Context (cs: list h10uc).
(* The solution to cs *)
Context (φ: nat -> nat). 
(* Proof that it actually is a solution *)
Context (Hφ : forall c, In c cs -> h10uc_sem φ c). 

Definition φ' (xn:nat) : nat := match decode5 xn with
    (x,v0) => φ x
  | (x,v1) => c2 (φ x)
  | (x,v2) => φ x * φ x + φ x + 1
  | (x,v3) => φ x * φ x
  | (x,v4) => c2 (c2 (φ x)) end.

Lemma transport_single c : h10uc_sem φ c -> 
          forall cc, In cc (h10uc_to_h10upc_single c) -> h10upc_sem φ' cc.
Proof.
  intros H cc. destruct c as [[x y] z]. intros [c'|[c'|[c'|[]]]]; subst. 
  all:unfold rename, newvar, φ'; cbn. all: rewrite !decode_encode. all: split.
  - rewrite <- c2_descr. lia. 
  - apply c2_descr.
  - lia.
  - apply c2_descr. 
  - cbn in H. nia. 
  - apply c2_descr.
Qed.

Lemma transport : forall c, In c (h10uc_to_h10upc cs) -> h10upc_sem φ' c.
Proof using Hφ.
  intros c H%(in_flat_map_Exists h10uc_to_h10upc_single c cs).
  induction cs as [|cc cs' IHcs].
  - now apply Exists_nil in H.
  - apply Exists_cons in H as [Hl|Hr].
    + apply (transport_single cc).
      * apply Hφ. now left.
      * easy.
    + apply IHcs.
      * intros c' Hc'. apply Hφ. now right.
      * easy.
Qed.

End Transport.

Section InverseTransport.
(* The instance of h10uc (which we are reducing from) *)
Context (cs: list h10uc).
 (* The solution to f(cs) (f is the reduction function) *) 
Context (φ': nat -> nat).
(* Proof that it actually is a solution *)
Context (Hφ' : forall c, In c (h10uc_to_h10upc cs) -> h10upc_sem φ' c). 

(* Lookup variables in result env *)
Definition φ (n:nat) : nat := φ' (rename n). 

Lemma inverse_transport_single c : 
      (forall cc, In cc (h10uc_to_h10upc_single c) -> h10upc_sem φ' cc) 
       -> h10uc_sem φ c.
Proof.
  intros H. destruct c as [[x y] z]. cbn.
  cbn in H.
  assert (h10upc_sem φ' ((newvar y v1, newvar y v1), (newvar y v2, newvar y v4))) 
    as [HC1l _] by (apply H; tauto).
  assert (h10upc_sem φ' ((newvar y v3, rename y), (newvar y v2, newvar y v1))) 
    as [HC2l HC2r] by (apply H; tauto).
  assert (h10upc_sem φ' ((newvar y v3, rename x), (rename z, newvar x v1))) 
    as [HC3l _] by (apply H; tauto).
  unfold φ. nia.
Qed.

Lemma inverse_transport : forall c, In c cs -> h10uc_sem φ c.
Proof using Hφ'.
  intros c H.
  apply inverse_transport_single. intros cc Hcc. apply Hφ'.
  unfold h10uc_to_h10upc. apply in_flat_map. exists c. now split.
Qed.

End InverseTransport.
End Argument.
Require Import Undecidability.Synthetic.Definitions.

(** Square Diophantine Constraint Solvability many-one reduces to Uniform Diophantine Constraint Solvability *)
Theorem reduction : H10UC_SAT ⪯ H10UPC_SAT.
Proof. exists Argument.h10uc_to_h10upc. split.
 - intros [φ Hφ]. exists (Argument.φ' φ). now apply Argument.transport.
 - intros [φ' Hφ']. exists (Argument.φ φ'). now apply Argument.inverse_transport.
Qed.
