(** * Reductions *)

Require Import Setoid.

Set Implicit Arguments.

(** ** Definitions *)

Definition reduces X Y (p : X -> Prop) (q : Y -> Prop) := exists f : X -> Y, forall x, p x <-> q (f x).
Definition ireduces X Y (P : X -> Prop) (Q : Y -> Prop) := { f : X -> Y | forall x, P x <-> Q (f x) }.

Infix "⪯" := reduces (at level 70).
Infix "⪯i" := ireduces (at level 70).

(** ** Pre-order properties *)

Section Properties.

  Variables (X : Type) (P : X -> Prop)
            (Y : Type) (Q : Y -> Prop)
            (Z : Type) (R : Z -> Prop).

  Fact reduces_reflexive : P ⪯ P.
  Proof. exists (fun x => x); tauto. Qed.

  Fact ireduces_reflexive : P ⪯i P.
  Proof. exists (fun x => x); tauto. Qed.

  Fact reduces_transitive : P ⪯ Q -> Q ⪯ R -> P ⪯ R.
  Proof. 
    intros (f & Hf) (g & Hg).
    exists (fun x => g (f x)).
    intro; rewrite Hf, Hg; tauto.
  Qed.

  Fact ireduces_transitive : P ⪯i Q -> Q ⪯i R -> P ⪯i R.
  Proof. 
    intros (f & Hf) (g & Hg).
    exists (fun x => g (f x)).
    intro; rewrite Hf, Hg; tauto.
  Qed.

  Fact ireduces_reduces : P ⪯i Q -> P ⪯ Q.
  Proof. intros (f & ?); exists f; auto. Qed.

  Fact reduces_ireduces : P ⪯ Q -> inhabited (P ⪯i Q).
  Proof. intros (f & ?); exists; exists f; auto. Qed.

  Fact reduces_ireduces_iff : P ⪯ Q <-> inhabited (P ⪯i Q).
  Proof.
    split.
    + apply reduces_ireduces.
    + intros []; apply ireduces_reduces; auto.
  Qed.

  (** ** An equivalent dependent definition *)

  Fact ireduces_dependent :
         (P ⪯i Q -> forall x, { y | P x <-> Q y })
       * ((forall x, { y | P x <-> Q y }) -> P ⪯i Q).
  Proof.
    split.
    + intros (f & Hf).
      intros x; exists (f x); auto.
    + intros f.
      exists (fun x => proj1_sig (f x)).
      intros; apply (proj2_sig (f x)).
  Qed.

End Properties.

