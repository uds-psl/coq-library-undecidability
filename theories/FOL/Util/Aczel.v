(** * Consistency of ZF-Axiomatisation *)

Require Import Setoid Morphisms.

Local Set Implicit Arguments.
Local Unset Strict Implicit.



(** ** Well-Founded Trees *)

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



(** ** Set Operations *)

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



(** ** Quotient Model *)

Class extensional_normaliser :=
  {
    tdelta : (Acz -> Prop) -> Acz;
    TDesc1 : forall P, (exists s, forall t, P t <-> Aeq t s) -> P (tdelta P);
    TDesc2 : forall P P', (forall s, P s <-> P' s) -> tdelta P = tdelta P';
    PI : forall s (H H' : tdelta (Aeq s) = s), H = H';
  }.

Section QM.

  Context { Delta : extensional_normaliser }.

  (* Auxiliary lemmas *)

  Definition N s :=
    tdelta (Aeq s).

  Fact CR1 :
    forall s, Aeq s (N s).
  Proof.
    intros s. pattern (N s). apply TDesc1. now exists s.
  Qed.

  Lemma CR2 :
    forall s t, Aeq s t -> N s = N t.
  Proof.
    intros s t H. apply TDesc2.
    intros u. rewrite H. tauto.
  Qed.

  Lemma N_idem s :
    N (N s) = N s.
  Proof.
    apply CR2. symmetry. apply CR1.
  Qed.

  Lemma N_eq_Aeq s t :
    N s = N t -> Aeq s t.
  Proof.
    intros H. rewrite (CR1 s), (CR1 t). now rewrite H.
  Qed.

  Global Instance N_proper :
    Proper (Aeq ==> Aeq) N.
  Proof.
    intros s t H. now rewrite <- (CR1 s), <- (CR1 t).
  Qed.

  Definition SET :=
    sig (fun s => N s = s).

  Definition NS s : SET :=
    exist (fun s => N s = s) (N s) (N_idem s).

  Definition IN (X Y : SET) :=
    Ain (proj1_sig X) (proj1_sig Y).

  Definition Subq (X Y : SET) :=
    forall Z, IN Z X -> IN Z Y.

  (* Helpful lemmas for automation *)

  Lemma Aeq_p1_NS s :
    Aeq s (proj1_sig (NS s)).
  Proof.
    exact (CR1 s).
  Qed.

  Lemma NS_eq_Aeq_p1 s X :
    NS s = X -> Aeq s (proj1_sig X).
  Proof.
    intros <-. apply Aeq_p1_NS.
  Qed.

  Lemma Ain_IN_p1 X Y :
    Ain (proj1_sig X) (proj1_sig Y) -> IN X Y.
  Proof.
    intros H1. unfold IN. exact H1.
  Qed.

  Lemma Ain_IN_NS s t :
    Ain s t -> IN (NS s) (NS t).
  Proof.
    intros H1. unfold IN. now repeat rewrite <- Aeq_p1_NS.
  Qed.

  Lemma Ain_IN_p1_NS X s :
    Ain (proj1_sig X) s -> IN X (NS s).
  Proof.
    intros H1. unfold IN. now rewrite <- Aeq_p1_NS.
  Qed.

  Lemma Ain_IN_NS_p1 s X :
    Ain s (proj1_sig X) -> IN (NS s) X.
  Proof.
    intros H1. unfold IN. now rewrite <- Aeq_p1_NS.
  Qed.

  Lemma IN_Ain_p1 X Y :
    IN X Y -> Ain (proj1_sig X) (proj1_sig Y).
  Proof.
    tauto.
  Qed.

  Lemma IN_Ain_NS s t :
    IN (NS s) (NS t) -> Ain s t.
  Proof.
    unfold IN. now repeat rewrite <- Aeq_p1_NS.
  Qed.

  Lemma IN_Ain_p1_NS X s :
    IN X (NS s) -> Ain (proj1_sig X) s.
  Proof.
    unfold IN. now rewrite <- Aeq_p1_NS.
  Qed.

  Lemma IN_Ain_NS_p1 s X :
    IN (NS s) X -> Ain s (proj1_sig X).
  Proof.
    unfold IN. now rewrite <- Aeq_p1_NS.
  Qed.

  Local Hint Resolve Ain_IN_p1 Ain_IN_NS Ain_IN_p1_NS Ain_IN_NS_p1 IN_Ain_p1 IN_Ain_NS IN_Ain_p1_NS IN_Ain_NS_p1 : core.

  Lemma ASubq_Subq_p1 X Y :
    ASubq (proj1_sig Y) (proj1_sig X) <-> Subq Y X.
  Proof.
    split; intros H Z H1.
    - apply Ain_IN_p1, H. auto.
    - apply IN_Ain_NS_p1, H. auto.
  Qed.

  Lemma PI_eq s t (H1 : N s = s) (H2 : N t = t) :
    s = t -> exist (fun s => N s = s) s H1 = exist (fun s => N s = s) t H2.
  Proof.
    intros XY. subst t. f_equal. apply PI.
  Qed.

  Lemma NS_p1_eq X :
    NS (proj1_sig X) = X.
  Proof.
    destruct X. simpl. now apply PI_eq.
  Qed.

  Lemma Aeq_p1_NS_eq X s :
    Aeq (proj1_sig X) s -> X = NS s.
  Proof.
    destruct X as [t H1]. simpl. intros H2. unfold NS.
    apply PI_eq. rewrite <- H1. now apply CR2.
  Qed.

  Lemma Aeq_p1_eq (X Y : SET) :
    Aeq (proj1_sig X) (proj1_sig Y) -> X = Y.
  Proof.
    intros H. rewrite <- (NS_p1_eq Y). now apply Aeq_p1_NS_eq.
  Qed.

  Lemma Aeq_NS_eq s t :
    Aeq s t -> NS s = NS t.
  Proof.
    intros H % CR2.
    now apply PI_eq.
  Qed.



  (** ** Extensional Axioms *)

  (* Lifted set operations *)

  Definition Sempty :=
    NS AEmpty.

  Definition Supair (X Y : SET) :=
    NS (Aupair (proj1_sig X) (proj1_sig Y)).

  Definition Sunion (X : SET) :=
    NS (Aunion (proj1_sig X)).

  Definition Spower (X : SET) :=
    NS (Apower (proj1_sig X)).

  Definition empred (P : SET -> Prop) :=
    fun s => P (NS s).

  Definition Ssep (P : SET -> Prop) (X : SET) :=
    NS (Asep (empred P) (proj1_sig X)).

  Definition emfun (F : SET -> SET) :=
    fun s => proj1_sig (F (NS s)).

  Definition Srepl (F : SET -> SET) (X : SET) :=
    NS (Arepl (emfun F) (proj1_sig X)).

  Definition Som :=
    NS Aom.

  (* Extensionality *)

  Lemma set_ext X Y : 
    Subq X Y /\ Subq Y X <-> X = Y.
  Proof.
    split; intros H; try now rewrite H. destruct H as [H1 H2].
    apply Aeq_p1_eq, Aeq_ext; now apply ASubq_Subq_p1.
  Qed.

  (* Empty *)

  Lemma emptyE X :
    ~ IN X Sempty.
  Proof.
    intros H % IN_Ain_p1_NS. now apply AEmptyAx in H.
  Qed.

  (* Unordered Pairs *)

  Lemma upairAx X Y Z :
    IN Z (Supair X Y) <-> Z = X \/ Z = Y.
  Proof.
    split; intros H.
    - apply IN_Ain_p1_NS, AupairAx in H as [H|H].
      + left. now apply Aeq_p1_eq.
      + right. now apply Aeq_p1_eq.
    - apply Ain_IN_p1_NS, AupairAx.
      destruct H as [-> | ->]; auto.
  Qed.

  (* Union *)

  Lemma unionAx X Z :
    IN Z (Sunion X) <-> exists Y, IN Y X /\ IN Z Y.
  Proof.
    split; intros H.
    - apply IN_Ain_p1_NS, AunionAx in H as [y[Y1 Y2]].
      exists (NS y). split; auto.
    - destruct H as [Y[Y1 Y2]].
      apply Ain_IN_p1_NS, AunionAx.
      exists (proj1_sig Y). split; auto.
  Qed.

  (* Power *)

  Lemma powerAx X Y :
    IN Y (Spower X) <-> Subq Y X.
  Proof.
    split; intros H.
    - apply IN_Ain_p1_NS, ApowerAx in H.
      now apply ASubq_Subq_p1.
    - apply Ain_IN_p1_NS, ApowerAx.
      now apply ASubq_Subq_p1.
  Qed.

  (* Separation *)

  Fact empred_Aeq P :
    cres Aeq (empred P).
  Proof.
    intros s s' H % Aeq_NS_eq. unfold empred. now rewrite H.
  Qed.

  Lemma sepAx P X Y :
    IN Y (Ssep P X) <-> IN Y X /\ P Y.
  Proof with try apply empred_Aeq.
    split; intros H.
    - apply IN_Ain_p1_NS, AsepAx in H as [H1 H2]...
      split; auto. unfold empred in H2.
      now rewrite NS_p1_eq in H2.
    - destruct H as [H1 H2]. apply Ain_IN_p1_NS, AsepAx...
      split; trivial. unfold empred. now rewrite NS_p1_eq.
  Qed.

  (* Functional Replacement *)

  Fact emfun_Aeq F :
    fres Aeq (emfun F).
  Proof.
    intros s s' H % Aeq_NS_eq.
    unfold emfun. now rewrite H.
  Qed.

  Lemma replAx F X Y :
    IN Y (Srepl F X) <-> exists Z, IN Z X /\ Y = F Z.
  Proof with try apply emfun_Aeq.
    split; intros H.
    - apply IN_Ain_p1_NS, AreplAx in H as [z[Z1 Z2]]...
      exists (NS z). split; auto. now apply Aeq_p1_eq.
    - destruct H as [Z[Z1 Z2]].
      apply Ain_IN_p1_NS, AreplAx...
      exists (proj1_sig Z). split; auto.
      rewrite Z2. unfold emfun.
      now rewrite NS_p1_eq.
  Qed.

  (* Description Operator *)

  Definition desc (P : SET -> Prop) :=
    NS (tdelta (fun s => empred P s)).

  Lemma descAx (P : SET -> Prop) X :
    P X -> unique P X -> P (desc P).
  Proof.
    intros H1 H2. 
    enough (empred P (tdelta (empred P))) by assumption.
    apply TDesc1. exists (proj1_sig X).
    intros t. split; intros H.
    - apply NS_eq_Aeq_p1. symmetry. now apply H2.
    - symmetry in H. apply (empred_Aeq H).
      hnf. now rewrite NS_p1_eq.
  Qed.

  Lemma descAx2 (P P' : SET -> Prop) :
    (forall x, P x <-> P' x) -> desc P = desc P'.
  Proof.
    intros H. apply Aeq_NS_eq, Aeq_ref', TDesc2.
    intros s. apply H.
  Qed.

  (* Relational Replacement *)
  
  Definition Srep (R : SET -> SET -> Prop) X :=
    Srepl (fun x => desc (R x)) (Ssep (fun x => exists y, R x y) X).

  Definition functional X (R : X -> X -> Prop) :=
    forall x y y', R x y -> R x y' -> y = y'.

  Lemma repAx R X Y :
    functional R -> IN Y (Srep R X) <-> exists Z, IN Z X /\ R Z Y.
  Proof.
    intros H. unfold Srep. rewrite replAx.
    split; intros [Z[H1 H2]]; exists Z; split.
    - now apply sepAx in H1.
    - apply sepAx in H1 as [_ [Y' H']].
      subst. eapply descAx; firstorder eauto.
    - apply sepAx; split; trivial. now exists Y.
    - eapply H; eauto. eapply descAx; firstorder eauto.
  Qed.

  (* Infinity *)

  Definition Ssucc X :=
    Sunion (Supair X (Supair X X)).

  Definition Sinductive X :=
    IN Sempty X /\ forall Y, IN Y X -> IN (Ssucc Y) X.

  Lemma Ainductive_Sinductive X :
    Ainductive (proj1_sig X) <-> Sinductive X.
  Proof.
    split; intros [H1 H2]; split.
    - now apply Ain_IN_NS_p1.
    - intros Y H % IN_Ain_p1. apply H2 in H.
      unfold IN. cbn. now rewrite <- !CR1.
    - now apply IN_Ain_NS_p1.
    - intros s H % Ain_IN_NS_p1. specialize (H2 (NS s) H).
      unfold IN in H2. cbn in H2. now rewrite <- !CR1 in H2.
  Qed.

  Lemma omAx1 :
    Sinductive Som.
  Proof.
    split.
    - apply Ain_IN_NS. apply AomAx1.
    - intros X H. unfold IN in *; cbn in *.
      rewrite <- !CR1 in *. now apply AomAx1.
  Qed.

  Lemma omAx2 :
    forall X, Sinductive X -> Subq Som X.
  Proof.
    intros X H. apply ASubq_Subq_p1. cbn.
    rewrite <- CR1. apply AomAx2.
    now apply Ainductive_Sinductive.
  Qed.

End QM.
