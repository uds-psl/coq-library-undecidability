(* * Consistency of ZF-Axiomatisation *)

Require Import Setoid Morphisms.

Local Set Implicit Arguments.
Local Unset Strict Implicit.



(* ** Well-Founded Trees *)

Inductive Acz : Type :=
  Asup : forall A : Type, (A -> Acz) -> Acz.

Arguments Asup _ _ : clear implicits.

Definition pi1 s :=
  match s with
    Asup A f => A
  end.

Definition pi2 s : (pi1 s) -> Acz :=
  match s with
    Asup A f => f
  end.

Arguments pi2 _ : clear implicits.

Fixpoint Aeq s t :=
  match s, t with
    Asup A f, Asup B g => (forall a, exists b, Aeq (f a) (g b)) /\ (forall b, exists a, Aeq (f a) (g b))
  end.

Lemma Aeq_ref s :
  Aeq s s.
Proof.
  induction s as [A f IH]. simpl. split.
  - intros a. exists a. now apply IH.
  - intros a. exists a. now apply IH.
Qed.

Lemma Aeq_ref' s t :
  s = t -> Aeq s t.
Proof.
  intros ->. apply Aeq_ref.
Qed.

Lemma Aeq_sym s t :
  Aeq s t -> Aeq t s.
Proof.
  revert t. induction s as [A f IH].
  intros [B g]. simpl. intros [H1 H2]. split.
  - intros b. destruct (H2 b) as [a H3]. exists a. now apply IH.
  - intros a. destruct (H1 a) as [b H3]. exists b. now apply IH.
Qed.

Lemma Aeq_tra s t u :
  Aeq s t -> Aeq t u -> Aeq s u.
Proof.
  revert t u. induction s as [A f IH].
  intros [B g] [C h]. simpl. intros [H1 H2] [H3 H4]. split.
  - intros a. destruct (H1 a) as [b H5]. destruct (H3 b) as [c H6].
    exists c. now apply IH with (t := (g b)).
  - intros c. destruct (H4 c) as [b H5]. destruct (H2 b) as [a H6].
    exists a. now apply IH with (t := (g b)).
Qed.

Local Hint Resolve Aeq_ref Aeq_sym Aeq_tra : core.

Instance aeq_equiv :
  Equivalence Aeq.
Proof.
  constructor; eauto.
Qed.

Definition Ain s '(Asup A f) :=
  exists a, Aeq s (f a).

Definition ASubq s t :=
  forall u, Ain u s -> Ain u t.

Lemma Ain_Asup A f a :
  Ain (f a) (Asup A f).
Proof.
  simpl. exists a. now apply Aeq_ref.
Qed.

Lemma Ain_pi s t :
  Ain s t -> exists a : (pi1 t), Aeq s (pi2 t a).
Proof.
  destruct t as [A f]. intros [a H]. now exists a.
Qed.

Lemma pi_Ain (s : Acz) (a : pi1 s) :
  Ain (pi2 s a) s.
Proof.
  destruct s as [A f]; simpl in *. now exists a.
Qed.

Lemma Ain_mor s s' t t' :
  Aeq s s' -> Aeq t t' -> Ain s t -> Ain s' t'.
Proof.
  intros H1 H2 H3.
  destruct t as [B1 g1]. simpl in H3. destruct H3 as [b1 H3].
  destruct t' as [B2 g2]. simpl. simpl in H2. destruct H2 as [H2 _].
  destruct (H2 b1) as [b2 H4]. exists b2.
  rewrite <- H4. now rewrite <- H1.
Qed.

Instance Ain_proper :
  Proper (Aeq ==> Aeq ==> iff) Ain.
Proof.
  intros s s' H1 t t' H2. split; intros H.
  - now apply (Ain_mor H1 H2).
  - apply Aeq_sym in H1. apply Aeq_sym in H2.
    now apply (Ain_mor H1 H2).
Qed.

Instance ASubq_proper :
  Proper (Aeq ==> Aeq ==> iff) ASubq.
Proof.
  intros s s' H1 t t' H2. split; intros H.
  - intros u. rewrite <- H1, <- H2. apply H.
  - intros u. rewrite H1, H2. apply H.
Qed.



(* ** Set Operations *)

Definition AEmpty :=
  Asup False (fun a => match a with end).

Definition Aupair X Y := 
  Asup bool (fun a => if a then X else Y).

Definition Aunion '(Asup A f) :=
  Asup (sigT (fun (a : A) => (pi1 (f a)))) (fun p => let (a, b) := p in pi2 (f a) b).

Definition Apower '(Asup A f) :=
  Asup (A -> Prop) (fun P => Asup (sig P) (fun p => let (a, _) := p in f a)).

Definition Asep (P : Acz -> Prop) '(Asup A f) :=
  Asup (sig (fun a => P (f a))) (fun p => let (a, _) := p in f a).

Definition Arepl (F : Acz -> Acz) '(Asup A f) :=
  Asup A (fun a => F (f a)).

Definition Asucc X :=
  Aunion (Aupair X (Aupair X X)).

Fixpoint Anumeral n :=
  match n with
  | 0 => AEmpty
  | S n => Asucc (Anumeral n)
  end.

Definition Aom :=
  Asup nat Anumeral.



(** ** Intensional Axioms *)

(* Extensionality *)

Lemma Aeq_ext s t :
  ASubq s t -> ASubq t s -> Aeq s t.
Proof.
  destruct s as [A f], t as [B g].
  intros H1 H2. simpl. split.
  - intros a. destruct (H1 (f a) (Ain_Asup f a)) as [b H3]. now exists b.
  - intros b. destruct (H2 (g b) (Ain_Asup g b)) as [a H3]. now exists a.
Qed.

Lemma Aeq_ASubq s t :
  Aeq s t -> ASubq s t.
Proof.
  destruct s as [A f], t as [B g]. intros [H _] z [a Z].
  destruct (H a) as [b I]. exists b. eauto.
Qed.

(* Empty *)

Lemma AEmptyAx s :
  ~ Ain s AEmpty.
Proof.
  now intros [t H].
Qed.

(* Unordered Pairs *)

Lemma AupairAx s t u :
  Ain u (Aupair s t) <-> Aeq u s \/ Aeq u t.
Proof.
  split; intros H.
  - destruct H as [[] H]; auto.
  - destruct H as [H|H]; [now exists true | now exists false].
Qed.

Lemma Aupair_mor s s' t t' u :
  Aeq s s' -> Aeq t t' -> Ain u (Aupair s t) -> Ain u (Aupair s' t').
Proof.
  intros H1 H2 H. apply AupairAx.
  rewrite <- H1, <- H2. now apply AupairAx in H.
Qed.

Instance Aupair_proper :
  Proper (Aeq ==> Aeq ==> Aeq) Aupair.
Proof.
  intros s s' H1 t t' H2. apply Aeq_ext; intros z H.
  - now apply (Aupair_mor H1 H2).
  - symmetry in H1, H2. now apply (Aupair_mor H1 H2).
Qed.

(* Union *)

Lemma AunionAx s u :
  Ain u (Aunion s) <-> exists t, Ain t s /\ Ain u t.
Proof.
  split; intros H; destruct s as [A f].
  - destruct  H as [[a b] H]. exists (f a). split.
    + now exists a.
    + destruct (f a) as [C h]; simpl in *. now exists b.
  - destruct H as [[B g][[a Z1][b Z2]]].
    apply Aeq_ASubq in Z1.
    specialize (Z1 (g b) (Ain_Asup g b)).
    apply Ain_pi in Z1 as [c H].
    exists (existT _ a c). eauto.
Qed.

Lemma Aunion_mor s s' u :
  Aeq s s' -> Ain u (Aunion s) -> Ain u (Aunion s').
Proof.
  intros H1 H2. apply AunionAx in H2 as [t H2].
  rewrite H1 in H2. apply AunionAx. now exists t.
Qed.

Instance Aunion_proper :
  Proper (Aeq ==> Aeq) Aunion.
Proof.
  intros s s' H1. apply Aeq_ext; intros z H.
  - now apply (Aunion_mor H1).
  - symmetry in H1. now apply (Aunion_mor H1).
Qed.

(* Power *)

Lemma ApowerAx s t :
  Ain t (Apower s) <-> ASubq t s.
Proof.
  split; intros H; destruct s as [A f].
  - destruct H as [P H].
    intros u Z. apply Aeq_ASubq in H.
    destruct (H u Z) as [[a PA] I]. now exists a. 
  - exists (fun a => Ain (f a) t). apply Aeq_ext; intros z Z.
    + destruct t as [B g], Z as [b H1].
      destruct (H (g b) (Ain_Asup g b)) as [a J].
      assert (H2: Ain (f a) (Asup B g)) by (exists b; auto).
      exists (exist _ a H2). eauto.
    + destruct Z as [[a YA] H1 % Aeq_sym].
      now apply (Ain_mor H1 (t:=t)).
Qed.

Lemma Apower_mor s s' t :
  Aeq s s' -> Ain t (Apower s) -> Ain t (Apower s').
Proof.
  intros H1 H2. apply ApowerAx.
  rewrite <- H1. now apply ApowerAx.
Qed.

Instance Apower_proper :
  Proper (Aeq ==> Aeq) Apower.
Proof.
  intros s s' H1. apply Aeq_ext; intros z H.
  - now apply (Apower_mor H1).
  - symmetry in H1. now apply (Apower_mor H1).
Qed.

(* Separation *)

Definition cres X (R : X -> X -> Prop) (P : X -> Prop) :=
  forall x y, R x y -> P x -> P y.

Lemma AsepAx (P : Acz -> Prop) s t :
  cres Aeq P -> Ain t (Asep P s) <-> Ain t s /\ P t.
Proof.
  intros HP. split; intros H; destruct s as [A f].
  - destruct H as [[a PA]H].
    split; eauto. now exists a.
  - destruct H as [[a H]PY].
    assert (PA : P (f a)) by now apply (HP t).
    now exists (exist _ a PA).
Qed.

Lemma Asep_mor (P P' : Acz -> Prop) s s' t :
  cres Aeq P -> cres Aeq P' -> (forall s, P s <-> P' s)
  -> Aeq s s' -> Ain t (Asep P s) -> Ain t (Asep P' s').
Proof.
  intros H1 H2 H3 H4 H5. apply AsepAx; trivial.
  rewrite <- H3, <- H4. apply AsepAx; trivial.
Qed.

Lemma Asep_proper' (P P' : Acz -> Prop) s s' :
  cres Aeq P -> cres Aeq P' -> (forall s, P s <-> P' s)
  -> Aeq s s' -> Aeq (Asep P s) (Asep P' s').
Proof.
  intros H1 H2 H3 H4. apply Aeq_ext; intros z Z.
  - apply (Asep_mor H1 H2 H3 H4); assumption.
  - apply (@Asep_mor P' P s' s); firstorder.
Qed.

Lemma Asep_proper (P : Acz -> Prop) s s' :
  cres Aeq P -> Aeq s s' -> Aeq (Asep P s) (Asep P s').
Proof.
  intros H1 H2. apply (@Asep_proper' P P); firstorder.
Qed.

(* Functional Replacement *)

Definition fres X (R : X -> X -> Prop) (f : X -> X) :=
  forall x y, R x y -> R (f x) (f y).

Lemma AreplAx F s u :
  fres Aeq F -> Ain u (Arepl F s) <-> exists t, Ain t s /\ Aeq u (F t).
Proof.
  intros HF. split; intros H; destruct s as [A f].
  - destruct H as [a H]. exists (f a).
    split; trivial. apply Ain_Asup.
  - destruct H as [z[[a H] Z]].
    exists a. apply HF in H; try now exists a.
    now rewrite Z, H.
Qed.

Lemma Arepl_mor (F F' : Acz -> Acz) s s' u :
  fres Aeq F -> fres Aeq F' -> (forall s, Aeq (F s) (F' s))
  -> Aeq s s' -> Ain u (Arepl F s) -> Ain u (Arepl F' s').
Proof.
  intros H1 H2 H3 H4 H5. apply AreplAx; trivial.
  apply AreplAx in H5 as [y H]; trivial.
  exists y. now rewrite <- H3, <- H4.
Qed.

Lemma Arepl_proper' (F F' : Acz -> Acz) s s' :
  fres Aeq F -> fres Aeq F' -> (forall s, Aeq (F s) (F' s))
  -> Aeq s s' -> Aeq (Arepl F s) (Arepl F' s').
Proof.
  intros H1 H2 H3 H4. apply Aeq_ext; intros z Z.
  - apply (Arepl_mor H1 H2 H3 H4); assumption.
  - apply (@Arepl_mor F' F s' s); auto.
Qed.

Lemma Arepl_proper (F : Acz -> Acz) s s' :
 fres Aeq F -> Aeq s s' -> Aeq (Arepl F s) (Arepl F s').
Proof.
  intros H1 H2. now apply Arepl_proper'.
Qed.

(* Infinity *)

Instance Asucc_proper :
  Proper (Aeq ==> Aeq) Asucc.
Proof.
  intros s s' H1. unfold Asucc. now rewrite H1.
Qed.

Definition Ainductive X :=
  Ain AEmpty X /\ forall s, Ain s X -> Ain (Asucc s) X.

Lemma AomAx1 :
  Ainductive Aom.
Proof.
  split.
  - exists 0. apply Aeq_ref.
  - intros s [n H]. exists (S n). now rewrite H.
Qed.

Lemma AomAx2 X :
  Ainductive X -> ASubq Aom X.
Proof.
  intros H s [n ->]. induction n; now apply H.
Qed.
