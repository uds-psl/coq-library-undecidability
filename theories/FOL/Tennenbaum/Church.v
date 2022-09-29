From Undecidability.Synthetic Require Import Definitions.
From Undecidability.FOL Require Import FullSyntax.
From Undecidability.FOL.Arithmetics Require Import Signature PA DeductionFacts.
From Undecidability.FOL.Syntax Require Import Theories.
From Undecidability.FOL.Tennenbaum Require Import Peano Formulas.
From Undecidability.FOL.Tennenbaum.Utils Require Import Synthetic DN.
Require Import Lia.

Import Vector.VectorNotations.

Notation "x 'el' A" := (List.In x A) (at level 70).
Notation "A '<<=' B" := (List.incl A B) (at level 70).

Definition unary α := bounded 1 α.
Definition binary α := bounded 2 α.


Section ChurchThesis.

Context {peirce_ : peirce}.

(** * Church's Thesis *)

(** ** CT_Q  *)

(*  CT_Q internalizes computability, stating that every function
    nat -> nat is computable in a model of computation. In this case,
    the model of computaion is based on arithmetic: It represents
    functions by formulas in the language of PA in such a way that a 
    weak fragment (Q <<= PA) can prove the agreement of the formula
    with the function on every input.
 *)

Definition represents ϕ f := forall x, Qeq ⊢I ∀ ϕ[(num x)..] ↔ num (f x) == $0.

(*  We only assume a weaker Version of CT_Q, where the existence of
    the formula is only given potentially (i.e. behing a double negation). 
 *)
Definition WCT_Q := forall f : nat -> nat, ~ ~ exists ϕ, bounded 2 ϕ /\ Σ1 ϕ /\ represents ϕ f.

(** Strong Representability *)

Definition strong_repr ϕ (p : nat -> Prop) := 
  (forall x,    p x -> Qeq ⊢I ϕ[(num x)..]) /\ 
  (forall x,  ~ p x -> Qeq ⊢I ¬ϕ[(num x)..]).
Definition WRT_strong := forall p : nat -> Prop, Dec p ->  ~ ~ exists ϕ, bounded 1 ϕ /\ Σ1 ϕ /\ strong_repr ϕ p.

(** Weak Representability *)

Definition weak_repr ϕ (p : nat -> Prop) := (forall x, p x <-> Qeq ⊢ ϕ[(num x)..]).
Definition WRT_weak := forall p : nat -> Prop, enumerable p -> ~ ~ exists ϕ, bounded 1 ϕ /\ Σ1 ϕ /\ weak_repr ϕ p.

Definition WRT := WRT_strong /\ WRT_weak.


Lemma prv_split α β Γ {p : peirce} :
  Γ ⊢ α ↔ β <-> Γ ⊢ (α → β) /\ Γ ⊢ (β → α).
Proof.
  split; intros H.
  - split.
    + eapply CE1. apply H.
    + eapply CE2. apply H.
  - now constructor.
Qed.

Lemma up_switch ϕ s t :
  ϕ[up (num s)..][(num t)..] = ϕ[(num t)..][(num s)..].
Proof.
  rewrite !subst_comp. apply subst_ext. 
  intros [|[]]; cbn; now rewrite ?num_subst.
Qed.


Variable num_eq : forall Γ,
  Γ <<= Qeq -> forall x y, x = y -> Γ ⊢I num x == num y.
Variable num_neq : forall Γ,
  Γ <<= Qeq -> forall x y, x <> y -> Γ ⊢I ¬ num x == num y.


(** ** Strong part of the representability theorem.  *)
Lemma WCT_WRTs :
  WCT_Q -> WRT_strong.
Proof.
  intros wct p [f Hf]%Dec_decider_nat.
  apply (DN.bind_ (wct f)).
  intros [ϕ [b1 [s1 H]]]. DN.ret.
  exists (ϕ[up (num 0)..]). repeat split.
  { admit. }
  { admit. }
  all: intros x; specialize (H x).
  all: eapply AllE with (t := num 0) in H; cbn -[Q] in H.
  all: apply prv_split in H; destruct H as [H1 H2].
  - intros px%Hf.
    eapply num_eq with (Γ := Qeq) in px; [|firstorder].
    eapply IE. cbn -[Qeq num]. rewrite up_switch.
    apply H2. rewrite num_subst. apply px.
  - intros npx. assert (f x <> 0) as E by firstorder.
    apply num_neq with (Γ := Qeq) in E; [|firstorder].
    apply II. eapply IE.
    { eapply Weak; [apply E|now right]. }
    eapply IE; [|apply Ctx; now left].
    rewrite num_subst in H1. eapply Weak.
    + cbn -[Q num]. rewrite up_switch. apply H1.
    + now right.
Admitted.

(** ** Weak part of the representability theorem.  *)
Lemma WCT_WRTw :
  WCT_Q -> WRT_weak.
Proof.
  intros wct p [f Hf]%enumerable_nat.
  apply (DN.bind_ (wct f)). 
  intros [ϕ [b1 [s1 H]]]. DN.ret.
  exists (∃ ϕ[up (σ $1)..]); repeat split.
  { admit. }
  { admit. }
  - intros [n Hn]%Hf.
    eapply Σ1_completeness with (ρ:= fun _ => 0).
    { admit. }
    { admit. }
    exists n. specialize (H n).
    apply soundness in H.
    unshelve refine (let H := (H nat interp_nat (fun _ => 0)) _ in _ ).
    { intros ax H'.
      repeat (destruct H' as [<-| H']); cbn ; try congruence.
      - intros []; auto. right. eexists; auto. 
      - destruct H'.
     }
    (* cbn in H. specialize (H (S x)) as [_ H2].
    rewrite eval_num, inu_nat_id in *.
    apply H2 in Hn. destruct Hn as [d Hd].
    exists d.
    unfold Φ. rewrite !sat_comp in *.
    eapply bound_ext with (N:=3).
    apply b2. 2: apply Hd.
    intros [|[|[]]]; cbn; rewrite ?num_subst, ?eval_num, ?inu_nat_id in *.
    all: try lia; reflexivity.
  - intros HQ%soundness. specialize (HQ nat interp_nat (fun _ => 0)).
    destruct HQ as [n [d Hnd]].
    {apply Q_std_axioms. }
    exists n. specialize (H n).
    apply soundness in H.
    unshelve refine (let H := (H nat interp_nat (fun _ => 0)) _ in _ ).
    apply Q_std_axioms.
    cbn in H. specialize (H (S x)) as [H1 _].
    rewrite eval_num, inu_nat_id in *.
    symmetry. apply H1. exists d.
    rewrite !sat_comp in Hnd. 
    unfold Φ in Hnd. rewrite sat_comp in *.
    eapply bound_ext.
    apply b2. 2: apply Hnd.
    intros [|[|[]]]; cbn; rewrite ?num_subst, ?eval_num, ?inu_nat_id in *.
    all: try lia; reflexivity. *)
Admitted.

End ChurchThesis.