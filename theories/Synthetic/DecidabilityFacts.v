Require Export Undecidability.Synthetic.Definitions Lia.
Require Import Undecidability.Shared.Dec.
Require Import Setoid Morphisms.

Definition discrete X := decidable (fun '(x,y) => x = y :> X).

(* Facts on reflects *)

Lemma reflects_not b P :
  reflects b P -> reflects (negb b) (~P).
Proof.
  unfold reflects.
  destruct b; cbn; intuition congruence.
Qed.

Lemma reflects_conj {b1 b2 P1 P2} :
  reflects b1 P1  -> reflects b2 P2 -> reflects (b1 && b2) (P1 /\ P2).
Proof.
  unfold reflects.
  destruct b1, b2; cbn; firstorder congruence.
Qed.

Lemma reflects_disj {b1 b2 P1 P2} :
  reflects b1 P1  -> reflects b2 P2 -> reflects (b1 || b2) (P1 \/ P2).
Proof.
  unfold reflects.
  destruct b1, b2; cbn; firstorder congruence.
Qed.

Lemma reflects_prv b (P : Prop) : (b = true -> P) -> (b = false -> ~ P) -> reflects b P.
Proof.
  intros H1 H2.
  destruct b; cbn; firstorder.
Qed.

(* Type-theoretic characterisations *)

Lemma dec_decidable' X p :
  (forall x : X, dec (p x)) -> { f : _ | forall x, p x <-> f x = true}.
Proof.
  intros d. exists (fun x => if d x then true else false). intros x. destruct (d x); firstorder congruence.
Qed.

Lemma decidable_iff X p :
  decidable p <-> inhabited (forall x : X, dec (p x)).
Proof.
  split.
  - intros [f H]. econstructor. intros x. specialize (H x). destruct (f x); firstorder congruence.
  - intros [d]. eapply dec_decidable' in d as [f]. now exists f.
Qed.

Lemma decidable_iff' X p :
  {f | decider f p} -> (forall x : X, dec (p x)).
Proof.
  intros [f H]. intros x. specialize (H x). destruct (f x); firstorder congruence.
Qed.

(* Closure properties of decidability *)

Lemma discrete_iff X :
  discrete X <-> inhabited (eq_dec X).
Proof.
  split.
  - intros [D] % decidable_iff. econstructor. intros x y; destruct (D (x,y)); firstorder.
  - intros [d]. eapply decidable_iff. econstructor. intros (x,y). eapply d.
Qed.

Lemma dec_compl X p :
  decidable p -> decidable (fun x : X => ~ p x).
Proof.
  intros [f H]. exists (fun x => negb (f x)).
  intros x. eapply reflects_not, H.
Qed.

Lemma dec_compl' X p :
  decidable (fun x : X => ~ ~ p x) -> decidable (fun x : X => ~ p x).
Proof.
  intros [f H]. exists (fun x => negb (f x)).
  intros x. specialize (H x). apply reflects_not in H.
  unfold reflects in *. tauto.
Qed.

Lemma dec_conj X p q :
  decidable p -> decidable q -> decidable (fun x : X => p x /\ q x).
Proof.
  intros [f] [g]. exists (fun x => andb (f x) (g x)).
  intros x. eapply reflects_conj; eauto.
Qed.

Lemma dec_disj X p q :
  decidable p -> decidable q -> decidable (fun x : X => p x \/ q x).
Proof.
  intros [f] [g]. exists (fun x => orb (f x) (g x)).
  intros x. eapply reflects_disj; eauto.
Qed.

(* Proper lemmas *)

#[global]
Instance Proper_decides {X} :
  Proper (pointwise_relation X (@eq bool) ==> pointwise_relation X iff ==> iff ) (@decider X).
Proof.
  intros f g H1 p q H2. red in H1, H2.
  unfold decider, reflects. 
  split; intros H x.
  - now rewrite <- H2, H, H1.
  - now rewrite H2, H, H1.
Qed.

#[global]
Instance Proper_decidable {X} :
  Proper (pointwise_relation X iff ==> iff) (@decidable X).
Proof.
  intros p q H2.
  split; intros [f H]; exists f.
  - now rewrite <- H2.
  - now rewrite H2.
Qed.

(* Closure properties of discreteness *)

Lemma discrete_bool : discrete bool.
Proof.
  eapply discrete_iff. econstructor. exact _.
Qed.

Lemma discrete_nat : discrete nat.
Proof.
  eapply discrete_iff. econstructor. exact _.
Qed.

Lemma discrete_nat_nat : discrete (nat * nat).
Proof.
  eapply discrete_iff. econstructor. exact _.
Qed.

Lemma discrete_prod X Y : discrete X -> discrete Y -> discrete (X * Y).
Proof.
  intros [d1] % discrete_iff [d2] % discrete_iff.
  eapply discrete_iff. econstructor. exact _.
Qed.

Lemma discrete_sum X Y : discrete X -> discrete Y -> discrete (X + Y).
Proof.
  intros [d1] % discrete_iff [d2] % discrete_iff.
  eapply discrete_iff. econstructor. exact _.
Qed.

Lemma discrete_option X : discrete X -> discrete (option X).
Proof.
  intros [d1] % discrete_iff. eapply discrete_iff.
  econstructor. exact _.
Qed.

Lemma discrete_list X : discrete X -> discrete (list X).
Proof.
  intros [d1] % discrete_iff. eapply discrete_iff.
  econstructor. exact _.
Qed.
