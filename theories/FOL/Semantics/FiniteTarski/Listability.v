From Undecidability.FOL.Semantics Require Import Tarski.FragmentFacts.
From Undecidability.FOL.Syntax Require Import Facts.
Require Import Undecidability.Synthetic.DecidabilityFacts.
Require Import Undecidability.Synthetic.EnumerabilityFacts.
Require Import Undecidability.Shared.Dec.
From Stdlib Require Import List.

(* Definition of finiteness *)

Definition listable X :=
  exists L, forall x : X, In x L.
Definition cListable X :=
  {L | forall x : X, In x L}.


Lemma listable_enumerable X :
  listable X -> enumerable__T X.
Proof.
  intros [L HL]. exists (nth_error L).
  intros x. apply In_nth_error, HL.
Qed.

Section listableFacts.
  Context (D:Type).
  Context {fini : cListable D}.

  (* Finite decidability is decidable *)
  Lemma fin_dec (P:D->Prop) : (forall k, dec (P k)) -> dec (forall k, P k).
  Proof using fini.
  intros HPr. assert (forall (l:list D), dec (forall k0, In k0 l -> P k0)) as H.
  - intros l. induction l as [|lx lr [IHt|IHf]].
    + left. intros v [].
    + destruct (HPr lx) as [Ht|Hf].
      * left. intros h. intros [l|r]. 1:congruence. now apply IHt.
      * right. intros Hc. apply Hf, Hc. now left.
    + right. intros Hc. apply IHf. intros k Hk. apply Hc. now right.
  - destruct fini as [l Hl]. destruct (H l) as [Ht|Hf].
    + left. intros k. apply Ht, Hl.
    + right. intros Hc. apply Hf. intros k Hk. apply Hc.
  Defined.

  Lemma fin_dec_ex (P:D->Prop) : (forall k, dec (P k)) -> dec (exists k, P k).
  Proof using fini.
  intros HPr. assert (forall (l:list D), dec (exists k0, In k0 l /\ P k0)) as H.
  - intros l. induction l as [|lx lr [IHt|IHf]].
    + right. intros [v [[] _]].
    + left. destruct IHt as [d [Hdl Hdr]]. exists d. split; firstorder.
    + destruct (HPr lx) as [Ht|Hf].
      * left. exists lx. split; firstorder.
      * right. intros [v [[->|vlr] Pv]]. 1:easy.
        apply IHf. exists v. now split.
  - destruct fini as [l Hl]. destruct (H l) as [Ht|Hf].
    + left. destruct Ht as [d [_ Pd]]. now exists d.
    + right. intros [d Pd]. apply Hf. exists d. split. 2:easy. apply Hl.
  Defined.
End listableFacts.