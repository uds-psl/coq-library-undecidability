Set Implicit Arguments.

(* many-one reducibility *)
Definition reduces X Y (p : X -> Prop) (q : Y -> Prop) := exists f : X -> Y, forall x, p x <-> q (f x).
Notation "p ⪯ q" := (reduces p q) (at level 50).

Lemma reduces_reflexive X (p : X -> Prop) : p ⪯ p.
Proof. exists (fun x => x); tauto. Qed.

Lemma reduces_transitive X Y Z (p : X -> Prop) (q : Y -> Prop) (r : Z -> Prop) :
  p ⪯ q -> q ⪯ r -> p ⪯ r.
Proof.
  intros [f ?] [g ?]. exists (fun x => g (f x)). firstorder.
Qed.

(* Turing-reducibility *)
Definition reduces_Turing X Y (p : X -> Prop) (q : Y -> Prop) := 
  inhabited ((forall y, {q y} + {not (q y)}) -> (forall x, {p x} + {not (p x)})).
Notation "p ⪯ᵀ q" := (reduces_Turing p q) (at level 50).

Lemma reduces_Turing_reflexive X (p : X -> Prop) : p ⪯ᵀ p.
Proof.
  constructor. intro H. exact H. 
Qed.

Lemma reduces_Turing_transitive X Y Z (p : X -> Prop) (q : Y -> Prop) (r : Z -> Prop) :
  p ⪯ᵀ q -> q ⪯ᵀ r -> p ⪯ᵀ r.
Proof.
  intros [f] [g]. constructor. intro H. exact (f (g H)).
Qed.

Lemma reduces_Turing_of_reduces X Y (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ q -> p ⪯ᵀ q.
Proof.
  intros [f Hf]. constructor. intros G x.
  destruct (G (f x)) as [Gfx | Gfx].
  left. exact ((proj2 (Hf x)) Gfx).
  right. intro A. exact (Gfx ((proj1 (Hf x)) A)).
Qed.
