
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

Require Import ssreflect ssrbool ssrfun.

  (* Uniform Diophantine pairs constraints (h10upc, the target) are of shape:  
      (x, y) # (1 + x + y, y * y)
     Uniform Diophantine constraints are of shape:
      1 + x + y * y = z

  Idea: We represent 1+x+y²=z as such: (where a, b, c, t1, t2 are new variables):
  y(y+1)/2 = a
  a+a+1 = b ( = y(y+1) + 1 = y²+y+1)
  c+y+1 = b (-> c = y²)
  x+c+1 = z (-> z = 1+x+y²)

  This equals the constraints (3 suffice (!) since we can merge constraint 1 and 3 into the same pair-constraint)
  (a,a) # (b,t1)
  (c,y) # (b,a)
  (c,x) # (z,t2)

  *)

(* Shamelessly taken from H10C-SAT_to_H10SQC_SAT.v *)
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

Opaque decode encode.

(* A simple (!) equality decider for natural numbers *)
Definition nat_eq (x y:nat) : {x=y} + {x <> y}. Proof. decide equality. Defined. 

(* A simple (!) division algorithm *)
Fixpoint divmod (x y:nat) : nat*nat := match x with 0 => (0,0)
   | S n => match divmod n y with (a,b) => if nat_eq (S b) y then (S a,0) else (a, S b) end end.

(* Along with its specification *)
Lemma divmod_spec (x y q r: nat) : y <> 0 -> divmod x y = (q,r) <-> x = q*y+r /\ r < y.
Proof.
intros H. induction x as [|x IH] in q,r|-*; split.
  - cbn. intros Heq. enough (q=0 /\ r=0) by nia. split; congruence.
  - cbn. intros Heq. f_equal; nia.
  - unfold divmod. fold divmod. destruct (divmod x y) as [q' r'].
    specialize (IH q' r'). destruct IH as [IHl IHr]. specialize (IHl ltac:(easy)).
    destruct (nat_eq (S r') y) as [Heq|Hneq]; cbn.
    + intros Hp. enough (r=0 /\ S q' = q) by nia; split; congruence.
    + intros Hp. enough (r=S r' /\ q = q') by nia; split; congruence.
  - intros [Heq Hry]. unfold divmod. fold divmod. destruct (divmod x y) as [q' r'] eqn:Hxy.
    specialize (IH q' r'). destruct IH as [IHl IHr]. destruct (IHl ltac:(easy)) as [xq' r'y].
    destruct (nat_eq (S r') y) as [Hl|Hr]; cbn.
    + enough (S q' = q). f_equal. easy. nia. nia.
    + enough (q=q'). f_equal; nia. nia.
Qed.

(* In a constraint of form (x,y)#(z,w), it holds that w=c2(z). This uniquely defines c2. It is total and computable: *)
Definition c2 k : nat := (divmod (k * S k) 2).1.

Lemma c2_descr x : x * S x = c2 x + c2 x.
Proof.
unfold c2. enough ((divmod (x*S x) 2).2=0) as Hr0. 
 - destruct (divmod (x*S x) 2) as [q r] eqn:Hdiv. cbn. destruct (divmod_spec (x*S x) 2 q r ltac:(easy)) as [Hdivl _].
   specialize (Hdivl ltac:(easy)). cbn in Hr0. nia.
 - induction x as [|x IH].
   + easy.
   + rewrite PeanoNat.Nat.mul_comm. 
     change (S (S x) * S x) with (S x + (S x + x * (S x))). 
     rewrite PeanoNat.Nat.add_assoc.
     destruct (divmod (x*S x) 2) as [q r] eqn:Hqr.
     destruct (divmod (S x + S x + x*S x) 2) as [q' r'] eqn:Hqr'.
     cbn. cbn in IH.
     apply divmod_spec in Hqr. 2:easy. apply divmod_spec in Hqr'. 2:easy.
     rewrite IH in Hqr. destruct Hqr as [Hqr _]. rewrite <- (plus_n_O) in Hqr.
     destruct Hqr' as [Hq' Hr']. rewrite Hqr in Hq'. nia.
Qed.

Opaque divmod c2.

Section Reduction.
Definition rename x := encode (x,0).
Definition newvar x y t := encode (x,S (encode (y,t))).

Definition h10uc_to_h10upc_single : h10uc -> list h10upc := (fun '(x,y,z) => 
  let '(a,b,c,t1,t2) := (newvar x y 0,newvar x y 1,newvar x y 2,newvar x y 3,newvar x y 4) in
  let '(x,y,z) := (rename x,rename y,rename z) in
  [((a,a),(b,t1)); ((c,y),(b,a)); ((c,x),(z,t2))]).

Definition h10uc_to_h10upc : list h10uc -> list h10upc := 
flat_map h10uc_to_h10upc_single.

End Reduction.

Section Transport.
Context (cs: list h10uc). (* The instance of h10uc (which we are reducing from) *)
Context (φ: nat -> nat). (* The solution to cs *)
Context (Hφ : forall c, In c cs -> h10uc_sem φ c). (* Proof that it actually is a solution *)

Definition φ' (xn:nat) : nat := match decode xn with
  (x,0) => φ x
| (x,S n) => match decode n with 
    (y,0) => c2 (φ y)
  | (y,1) => (φ y) * (φ y) + (φ y) + 1
  | (y,2) => (φ y) * (φ y)
  | (y,3) => c2 (c2 (φ y))
  | (y,4) => c2 (φ x)
  | (y,_) => 0 end end.

Lemma transport_single c : h10uc_sem φ c -> forall cc, In cc (h10uc_to_h10upc_single c) -> h10upc_sem φ' cc.
intros H cc. destruct c as [[x y] z]. intros [c'|[c'|[c'|fal]]]; try contradiction; 
subst; unfold rename, newvar, φ'; cbn; try rewrite ! decode_encode; split.
* rewrite <- c2_descr. lia. 
* apply c2_descr.
* lia.
* apply c2_descr. 
* cbn in H. nia. 
* apply c2_descr.
Qed.

Lemma transport : forall c, In c (h10uc_to_h10upc cs) -> h10upc_sem φ' c.
intros c H%(in_flat_map_Exists h10uc_to_h10upc_single c cs).
induction cs as [|cc cs' IHcs].
* inversion H.
* inversion H; subst.
  + apply (transport_single cc).
    - apply Hφ. now left.
    - easy.
  + apply IHcs.
    - intros c' Hc'. apply Hφ. now right.
    - apply H1.
Qed.

End Transport.

Section InverseTransport.
Context (cs: list h10uc). (* The instance of h10uc (which we are reducing from) *)
Context (φ': nat -> nat). (* The solution to f(cs) (f is the reduction function) *)
Context (Hφ' : forall c, In c (h10uc_to_h10upc cs) -> h10upc_sem φ' c). (* Proof that it actually is a solution *)

Definition φ (n:nat) : nat := φ' (rename n). (* Lookup variables in result env *)

Lemma inverse_transport_single c : (forall cc, In cc (h10uc_to_h10upc_single c) -> h10upc_sem φ' cc) -> h10uc_sem φ c.
intros H. destruct c as [[x y] z]. cbn.
cbn in H.
assert (h10upc_sem φ' (newvar x y 0, newvar x y 0, (newvar x y 1, newvar x y 3))) as [HC1l _] by (apply H; intuition).
assert (h10upc_sem φ' (newvar x y 2, rename y, (newvar x y 1, newvar x y 0))) as [HC2l HC2r] by (apply H; intuition).
assert (h10upc_sem φ' (newvar x y 2, rename x, (rename z, newvar x y 4))) as [HC3l _] by (apply H; intuition).
unfold φ. nia.
Qed.

Lemma inverse_transport : forall c, In c cs -> h10uc_sem φ c.
intros c H.
apply inverse_transport_single. intros cc Hcc. apply Hφ'. unfold h10uc_to_h10upc. apply in_flat_map. exists c. now split.
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
