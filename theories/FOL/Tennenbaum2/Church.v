From Undecidability.FOL Require Import FullSyntax.
From Undecidability.FOL.Arithmetics Require Import Signature PA DeductionFacts.
From Undecidability.FOL.Syntax Require Import Theories.
From Undecidability.Shared Require Import ListAutomation.
From Undecidability.FOL.Tennenbaum2 Require Import NumberUtils Formulas SyntheticInType Peano.

(* Require Import FOL Tarski Deduction Peano Formulas NumberTheory Synthetic DecidabilityFacts. *)
Require Import Lia.
From Equations Require Import Equations.

Import Vector.VectorNotations.

Notation "x 'el' A" := (List.In x A) (at level 70).
Notation "A '<<=' B" := (List.incl A B) (at level 70).
Notation "x ∣ y" := (exists k, x * k = y) (at level 50).

Definition unary α := bounded 1 α.
Definition binary α := bounded 2 α.



Section ChurchThesis.

Instance ff : falsity_flag := falsity_on.
Context {Δ1 : Delta1}.

(** * Church's Thesis *)

(** ** CT_Q  *)

(*  CT_Q internalizes computability, by claiming that every function
    nat -> nat is computable in a model of computation. In this case,
    the model of computaion is based on arithmetic: It represents
    functions by formulas in the language of PA in such a way that a 
    weak fragment (Q <<= PA) can prove the agreement of the formula
    with the function on every input.  
 *)

Definition represents ϕ f := forall x, Q ⊢I ∀ ϕ[up (num x)..] ↔ $0 == num (f x).
Definition CT_Q := forall f : nat -> nat, exists ϕ, bounded 3 ϕ /\ inhabited(delta1 ϕ) /\ represents (∃ ϕ) f.

(*  Weaker Version of CT_Q, where the existence of the formula 
    is only given potentially (i.e. behing a double negation). 
 *)
Definition WCT_Q := forall f : nat -> nat, ~ ~ exists ϕ, bounded 3 ϕ /\ inhabited(delta1 ϕ) /\ represents (∃ ϕ) f.

(** Strong Representability *)

Definition strong_repr ϕ (p : nat -> Prop) := (forall x, p x -> Q ⊢I ϕ[(num x)..]) /\ (forall x, ~ p x -> Q ⊢I ¬ϕ[(num x)..]).
Definition RT_strong := forall p : nat -> Prop, Dec p -> exists ϕ, bounded 2 ϕ /\ inhabited(delta1 ϕ) /\ strong_repr (∃ ϕ) p.
Definition WRT_strong := forall p : nat -> Prop, Dec p ->  ~ ~ exists ϕ, bounded 2 ϕ /\ inhabited(delta1 ϕ) /\ strong_repr (∃ ϕ) p.

(** Weak Representability *)

Definition weak_repr ϕ (p : nat -> Prop) := (forall x, p x <-> Q ⊢I ϕ[(num x)..]).
Definition RT_weak := forall p : nat -> Prop, enumerable p -> exists ϕ, bounded 3 ϕ /\ inhabited(delta1 ϕ) /\ weak_repr (∃∃ ϕ) p.
Definition WRT_weak := forall p : nat -> Prop, enumerable p -> ~ ~ exists ϕ, bounded 3 ϕ /\ inhabited(delta1 ϕ) /\ weak_repr (∃∃ ϕ) p.

Definition RT := RT_strong /\ RT_weak.

Lemma prv_split {p : peirce} α β Gamma :
  Gamma ⊢ α ↔ β <-> Gamma ⊢ (α → β) /\ Gamma ⊢ (β → α).
Proof.
  split; intros H.
  - split.
    + eapply CE1. apply H.
    + eapply CE2. apply H.
  - now constructor.
Qed.

Lemma up_switch ϕ s t :
  ϕ[up (num s)..][up (num t)..] = ϕ[up (up (num t)..)][up (num s)..].
Proof.
  rewrite !subst_comp. apply subst_ext. 
  intros [|[|[]]]; cbn; now rewrite ?num_subst.
Qed.


(** ** Strong part of the representability theorem.  *)
Lemma CT_RTs :
  CT_Q -> RT_strong.
Proof.
  intros ct p Dec_p.
  destruct (Dec_decider_nat _ Dec_p) as [f Hf].
  destruct (ct f) as [ϕ [b2 [[s1] H]]].
  pose (Φ := ϕ[up (num 0)..]).
  exists Φ. split; unfold Φ.
  { asimpl. eapply subst_bound; eauto.
    intros [|[|[]]] G; cbn; try lia. all: solve_bounds. }
  split.
  { constructor. now apply delta1_subst. }
  repeat split.
  all: intros x; specialize (H x).
  all: eapply AllE with (t := num 0) in H; cbn -[Q] in H.
  all: apply prv_split in H; destruct H as [H1 H2].
  - intros px%Hf. symmetry in px.
    eapply num_eq with (Gamma := Q)(p := intu) in px; [|firstorder].
    eapply IE. cbn -[Q num]. rewrite up_switch.
    apply H2. now rewrite num_subst.
  - intros npx. assert (0 <> f x) as E by firstorder.
    apply num_neq with (Gamma := Q)(p := intu) in E; [|firstorder].
    apply II. eapply IE.
    {eapply Weak; [apply E|now right]. }
    eapply IE; [|apply Ctx; now left].
    rewrite num_subst in H1. eapply Weak.
    + cbn -[Q num]. rewrite up_switch. apply H1.
    + now right.
Qed.


Lemma WCT_WRTs :
  WCT_Q -> WRT_strong.
Proof.
  intros wct p Dec_p.
  destruct (Dec_decider_nat _ Dec_p) as [f Hf]. 
  apply (DN_chaining (wct f)), DN. intros [ϕ [b2 [[s1] H]]].
  pose (Φ := ϕ[up (num 0)..]).
  exists Φ. split; unfold Φ.
  { eapply subst_bound; eauto.
    intros [|[|[]]] ?; cbn; try lia. all: solve_bounds. }
  split.
  { constructor. now apply delta1_subst. }
  repeat split.
  all: intros x; specialize (H x).
  all: eapply AllE with (t := num 0) in H; cbn -[Q] in H.
  all: apply prv_split in H; destruct H as [H1 H2].
  - intros px%Hf. symmetry in px.
    eapply num_eq with (Gamma := Q)(p := intu) in px; [|firstorder].
    eapply IE. cbn -[Q num]. rewrite up_switch.
    apply H2. now rewrite num_subst.
  - intros npx. assert (0 <> f x) as E by firstorder.
    apply num_neq with (Gamma := Q)(p := intu) in E; [|firstorder].
    apply II. eapply IE.
    {eapply Weak; [apply E|now right]. }
    eapply IE; [|apply Ctx; now left].
    rewrite num_subst in H1. eapply Weak.
    + cbn -[Q num]. rewrite up_switch. apply H1.
    + now right.
Qed.

(** ** Weak part of the representability theorem.  *)
Lemma CT_RTw :
  CT_Q -> RT_weak.
Proof.
  intros ct p [f Hf]%enumerable_nat.
  destruct (ct f) as [ϕ [b2 [[s1] H]]].
  pose (Φ := ϕ[up (σ $1)..] ).
  exists Φ; split. 2: split.
  - unfold Φ. eapply subst_bound; eauto.
    intros [|[|[]]] ?; try lia; repeat solve_bounds.
  - constructor. now apply delta1_subst. 
  - intros x. rewrite Hf. split.
    + intros [n Hn]. symmetry in Hn.
      apply sigma1_ternary_complete.
      { unfold Φ. eapply subst_bound; eauto.
      intros [|[|[]]] ?; try lia; repeat solve_bounds. }
      {unfold Φ. now apply delta1_subst. }
      exists n. specialize (H n).
      apply soundness in H.
      unshelve refine (let H := (H nat (extensional_model interp_nat) (fun _ => 0)) _ in _ ).
      {apply Q_std_axioms. }
      cbn in H. specialize (H (S x)) as [_ H2].
      rewrite eval_num, inu_nat_id in *.
      apply H2 in Hn. destruct Hn as [d Hd].
      exists d.
      unfold Φ. rewrite !sat_comp in *.
      eapply bound_ext with (N:=3).
      apply b2. 2: apply Hd.
      intros [|[|[]]]; cbn; rewrite ?num_subst, ?eval_num, ?inu_nat_id in *.
      all: try lia.
    + intros HQ%soundness. specialize (HQ nat (extensional_model interp_nat) (fun _ => 0)). cbn in HQ.
      destruct HQ as [n [d Hnd]].
      {apply Q_std_axioms. }
      exists n. specialize (H n).
      apply soundness in H.
      unshelve refine (let H := (H nat (extensional_model interp_nat) (fun _ => 0)) _ in _ ).
      apply Q_std_axioms.
      cbn in H. specialize (H (S x)) as [H1 _].
      rewrite eval_num, inu_nat_id in *.
      symmetry. apply H1. exists d.
      rewrite !sat_comp in Hnd. 
      unfold Φ in Hnd. rewrite sat_comp in *.
      eapply bound_ext.
      apply b2. 2: apply Hnd.
      intros [|[|[]]]; cbn; rewrite ?num_subst, ?eval_num, ?inu_nat_id in *.
      all: try lia; reflexivity.
Qed.


Lemma WCT_WRTw :
  WCT_Q -> WRT_weak.
Proof.
  intros wct p [f Hf]%enumerable_nat.
  apply (DN_chaining (wct f)), DN.
  intros [ϕ [b2 [[s1] H]]].
  pose (Φ := ϕ[up (σ $1)..] ).
  exists Φ; split. 2: split.
  - unfold Φ. eapply subst_bound; eauto.
    intros [|[|[]]] ?; try lia; repeat solve_bounds.
  - constructor. now apply delta1_subst. 
  - intros x. rewrite Hf. split.
    + intros [n Hn]. symmetry in Hn.
      apply sigma1_ternary_complete.
      { unfold Φ. eapply subst_bound; eauto.
        intros [|[|[]]] ?; try lia; repeat solve_bounds. }
      {unfold Φ. now apply delta1_subst. }
      exists n. specialize (H n).
      apply soundness in H.
      unshelve refine (let H := (H nat (extensional_model interp_nat) (fun _ => 0)) _ in _ ).
      {apply Q_std_axioms. }
      cbn in H. specialize (H (S x)) as [_ H2].
      rewrite eval_num, inu_nat_id in *.
      apply H2 in Hn. destruct Hn as [d Hd].
      exists d.
      unfold Φ. rewrite !sat_comp in *.
      eapply bound_ext with (N:=3).
      apply b2. 2: apply Hd.
      intros [|[|[]]]; cbn; rewrite ?num_subst, ?eval_num, ?inu_nat_id in *.
      all: try lia; reflexivity.
    + intros HQ%soundness. specialize (HQ nat (extensional_model interp_nat) (fun _ => 0)). cbn in HQ.
      destruct HQ as [n [d Hnd]].
      {apply Q_std_axioms. }
      exists n. specialize (H n).
      apply soundness in H.
      unshelve refine (let H := (H nat (extensional_model interp_nat) (fun _ => 0)) _ in _ ).
      apply Q_std_axioms.
      cbn in H. specialize (H (S x)) as [H1 _].
      rewrite eval_num, inu_nat_id in *.
      symmetry. apply H1. exists d.
      rewrite !sat_comp in Hnd. 
      unfold Φ in Hnd. rewrite sat_comp in *.
      eapply bound_ext.
      apply b2. 2: apply Hnd.
      intros [|[|[]]]; cbn; rewrite ?num_subst, ?eval_num, ?inu_nat_id in *.
      all: try lia; reflexivity.
Qed.


End ChurchThesis.