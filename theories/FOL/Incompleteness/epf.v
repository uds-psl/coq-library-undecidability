(** * Incompleteness *)
(** ** Church's Thesis *)

From Undecidability.FOL.Incompleteness Require Import utils.

From Undecidability.Synthetic Require Import Definitions EnumerabilityFacts.

Local Set Implicit Arguments.
Local Unset Strict Implicit.



(* ** Church's thesis *)

Definition is_universal {Y : Type} (theta : nat -> nat -\ Y) :=
  forall f : nat -\ Y, exists c, forall x y, f x ▷ y <-> theta c x ▷ y.

Definition EPF_B := exists (theta : nat -> nat -\ bool), is_universal theta.
Definition EPF_N := exists (theta : nat -> nat -\ nat), is_universal theta.

Section epf.
  Variable (theta : nat -> nat -\ bool).
  Hypothesis theta_universal : is_universal theta.

  Definition self_halting : nat -> Prop := fun x => exists y, theta x x ▷ y.

  Theorem self_halting_diverge (f : nat -\ bool) :
    (forall c, f c ▷ true <-> self_halting c) -> 
    exists c, forall y, ~f c ▷ y.
  Proof.
    intros H.
    unshelve evar (g: nat -\ bool).
    { intros n. exists (fun k => match (f n).(core) k with
                                 | Some true => None
                                 | Some false => Some true
                                 | None => None 
                                 end).
      intros y1 y2 k1 k2 Hk1 Hk2.
      destruct (core (f n) k1) as [[]|] eqn:Hf1, (core (f n) k2) as [[]|] eqn:Hf2.
      all: congruence. }
    destruct (theta_universal g) as [c Hc]. exists c.
    intros [] Hf.
    - pose proof (Hf' := Hf).
      apply H in Hf.
      destruct Hf as [b [k Hk]%Hc].
      cbn in Hk. destruct (core (f c) k) as [[]|] eqn:Hf; try discriminate.
      enough (true = false) by discriminate. 
      apply (@part_functional _ (f c)); firstorder.
    - enough (f c ▷ true) as H1.
      { now pose proof (part_functional Hf H1). }
      apply H. exists true. apply Hc.
      destruct Hf as [k Hk]. exists k.
      cbn. now rewrite Hk.
  Qed.

  Lemma self_halting_undec : ~decidable self_halting.
  Proof.
    intros [f Hf].
    unshelve evar (g: nat -\ bool).
    { intros n. exists (fun _ => Some (f n)). congruence. }
    destruct (@self_halting_diverge g).
    { intros c. split.
      - now intros [k [=Hk%Hf]].
      - intros H%Hf. exists 0. cbn. congruence. }
    apply (H (f x)). now exists 0.
  Qed.

  (* A partial function recursively separates two predicates *)
  Definition recursively_separates (P1 P2 : nat -> Prop)  (f : nat -\ bool) :=
    (forall x, P1 x -> f x ▷ true) /\
    (forall x, P2 x -> f x ▷ false).


  Definition theta_self_return (b : bool) : nat -> Prop :=
    fun x => theta x x ▷ b.

  Lemma theta_self_return_semi_decidable b : semi_decidable (theta_self_return b).
  Proof.
    exists (fun c k => match core (theta c c) k, b with
                       | Some true, true => true
                       | Some false, false => true
                       | _, _ => false
                       end).
   intros c. split; intros [k Hk]; exists k.
   - rewrite Hk. destruct b; congruence.
   - destruct (core _ _) as [[]|], b; congruence.
  Qed.
  Lemma theta_self_return_enumerable b : enumerable (theta_self_return b).
  Proof. 
    apply semi_decidable_enumerable.
    { exists (fun n => Some n). intros n. now exists n. }
    apply theta_self_return_semi_decidable.
  Qed. 


  Theorem recursively_separating_diverge (f : nat -\ bool):
    (forall b c, theta_self_return b c -> f c ▷ b) ->
    exists c, forall y, ~f c ▷ y.
  Proof.
    intros H.
    unshelve evar (g : nat -\ bool).
    { intros x. exact (comp_part_total negb (f x)). }
    destruct (theta_universal g) as [c Hc]. exists c. 
    intros y [k Hk].
    assert (g c ▷ (negb y)) as Hg.
    { exists k. cbn. rewrite Hk. reflexivity. }
    apply Hc in Hg. specialize (H _ _ Hg).
    enough (y = negb y) by now destruct y.
    apply (@part_functional _ (f c)).
    - now exists k. 
    - assumption.
  Qed.

  Lemma no_recursively_separating (f : nat -> bool) : 
    (* Looks closer to required condition by destructing b *)
    ~(forall b c, theta_self_return b c -> f c = b).
  Proof.
    intros H.
    unshelve evar (g : nat -\ bool).
    { intros x. exists (fun _ => Some (f x)). congruence. }
    destruct (@recursively_separating_diverge g) as [c Hc].
    { intros b c Hc%H. exists 0. cbn. congruence. }
    apply (Hc (f c)). now exists 0.
  Qed.

End epf.

Section epf_nat_bool.
  Local Definition bool_to_nat (b : bool) := if b then 1 else 0.
  Local Program Definition nat_to_bool : nat -\ bool.
  Proof.
    intros [|[|n]].
    - exists (fun _ => Some false). congruence.
    - exists (fun _ => Some true). congruence.
    - exists (fun _ => None). congruence.
  Defined.
  (* EPF_N implies EPF_B *)
  Lemma epf_nat_bool : EPF_N -> EPF_B.
  Proof.
    intros [theta theta_universal].
    unshelve eexists.
    { intros c x. exact (comp_part_partial nat_to_bool (theta c x)). }
    intros f. 
    unshelve edestruct theta_universal as [c Hc]. 
    { intros x. exact (comp_part_total bool_to_nat (f x)). }
    exists c. intros x y. split; intros [k Hk].
    - assert (theta c x ▷ bool_to_nat y) as [k' Hk'].
      { rewrite <-Hc. exists k. cbn. now rewrite Hk. }
      exists k'. cbn. rewrite Hk'. now destruct y.
    - assert (theta c x ▷ bool_to_nat y) as [k' Hk']%Hc.
      { exists k. cbn in Hk. destruct core; try congruence.
        destruct y, n as [|[|n]]; cbn in *; try congruence. }
      exists k'. cbn in Hk'. destruct (core (f x) k') as [[]|], y as []; cbn in *; congruence.
  Qed.

End epf_nat_bool.

