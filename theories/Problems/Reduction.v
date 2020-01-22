Require Import Setoid.

Set Implicit Arguments.

(** DLW: replace with INFORMATIVE reductions
    We prove informative reductions in here *)

(* Definition reduces X Y (p : X -> Prop) (q : Y -> Prop) := exists f : X -> Y, forall x, p x <-> q (f x).
Notation "p ⪯ q" := (reduces p q) (at level 50). *)

Definition reduces X Y (P : X -> Prop) (Q : Y -> Prop) :=
        { f : X -> Y | forall x, P x <-> Q (f x) }.

Infix "⪯" := reduces (at level 70).

Lemma reduces_reflexive X (P : X -> Prop) : P ⪯ P.
Proof. exists (fun x => x); tauto. Qed.

Fact reduces_transitive X P Y Q Z R :
        @reduces X Y P Q -> @reduces Y Z Q R -> P ⪯ R.
Proof. 
  intros (f & Hf) (g & Hg).
  exists (fun x => g (f x)).
  intro; rewrite Hf, Hg; tauto.
Qed.

(** DLW: Sometimes the dependent statement is more convenient *)

Fact reduction_dependent X Y (P : X -> Prop) (Q : Y -> Prop) :
         (P ⪯ Q -> forall x, { y | P x <-> Q y })
       * ((forall x, { y | P x <-> Q y }) -> P ⪯ Q).
Proof.
  split.
  + intros (f & Hf).
    intros x; exists (f x); auto.
  + intros f.
    exists (fun x => proj1_sig (f x)).
    intros; apply (proj2_sig (f x)).
Qed.

