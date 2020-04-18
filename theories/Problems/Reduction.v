(** * Reductions *)

Require Import Setoid.
Require Export Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

(* Set Implicit Arguments. *)

(* (** ** Definitions *) *)

(* Definition reduces X Y (p : X -> Prop) (q : Y -> Prop) := exists f : X -> Y, forall x, p x <-> q (f x). *)
(* Definition informatively_reduces X Y (P : X -> Prop) (Q : Y -> Prop) := { f : X -> Y | forall x, P x <-> Q (f x) }. *)

(* Infix "⪯" := reduces (at level 70). *)
(* Infix "⪯ᵢ" := informatively_reduces (at level 70). *)

(* (** ** Pre-order properties *) *)

(* Section Properties. *)

(*   Variables (X : Type) (P : X -> Prop) *)
(*             (Y : Type) (Q : Y -> Prop) *)
(*             (Z : Type) (R : Z -> Prop). *)

(*   Fact reduces_reflexive : P ⪯ P. *)
(*   Proof. exists (fun x => x); red; tauto. Qed. *)

(*   Fact ireduces_reflexive : P ⪯ᵢ P. *)
(*   Proof. exists (fun x => x); tauto. Qed. *)

(*   Fact reduces_transitive : P ⪯ Q -> Q ⪯ R -> P ⪯ R. *)
(*   Proof. *)
(*     unfold reduces, reduction. *)
(*     intros (f & Hf) (g & Hg). *)
(*     exists (fun x => g (f x)). *)
(*     intro; rewrite Hf, Hg; tauto. *)
(*   Qed. *)

(*   Fact ireduces_transitive : P ⪯ᵢ Q -> Q ⪯ᵢ R -> P ⪯ᵢ R. *)
(*   Proof.  *)
(*     intros (f & Hf) (g & Hg). *)
(*     exists (fun x => g (f x)). *)
(*     intro; rewrite Hf, Hg; tauto. *)
(*   Qed. *)

(*   Fact ireduces_reduces : P ⪯ᵢ Q -> P ⪯ Q. *)
(*   Proof. intros (f & ?); exists f; auto. Qed. *)

(*   Fact reduces_ireduces : P ⪯ Q -> inhabited (P ⪯ᵢ Q). *)
(*   Proof. intros (f & ?); exists; exists f; auto. Qed. *)

(*   Fact reduces_ireduces_iff : P ⪯ Q <-> inhabited (P ⪯ᵢ Q). *)
(*   Proof. *)
(*     split. *)
(*     + apply reduces_ireduces. *)
(*     + intros []; apply ireduces_reduces; auto. *)
(*   Qed. *)

(*   (** ** An equivalent dependent definition *) *)

(*   Fact ireduces_dependent : *)
(*          (P ⪯ᵢ Q -> forall x, { y | P x <-> Q y }) *)
(*        * ((forall x, { y | P x <-> Q y }) -> P ⪯ᵢ Q). *)
(*   Proof. *)
(*     split. *)
(*     + intros (f & Hf). *)
(*       intros x; exists (f x); auto. *)
(*     + intros f. *)
(*       exists (fun x => proj1_sig (f x)). *)
(*       intros; apply (proj2_sig (f x)). *)
(*   Qed. *)

(* End Properties. *)

