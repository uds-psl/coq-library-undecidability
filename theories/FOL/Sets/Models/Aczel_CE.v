(* * Extensional Model of Z via Class Extensionality *)

From Undecidability.FOL.Sets.Models Require Import Aczel.
Local Set Implicit Arguments.
Local Unset Strict Implicit.

Set Default Proof Using "Type".

(* Quotient construction assuming class extensionality (CE) *)

Definition CE :=
  forall (P Q : Acz -> Prop), (forall s, P s <-> Q s) -> P = Q.

Section Model.

Definition eqclass P :=
  exists s, P = Aeq s.

Hypothesis ce : CE.

Lemma PE (P P' : Prop) :
  (P <-> P') -> P = P'.
Proof using ce.
  intros H.
  change ((fun _ : Acz => P) AEmpty = P').
  now rewrite (@ce (fun _ => P) (fun _ => P')).
Qed.

Lemma PI (P : Prop) (H H' : P) :
  H = H'.
Proof using ce.
  assert (P = True) as ->. apply PE; tauto.
  destruct H, H'. reflexivity.
Qed.

Definition SET' :=
  { P | eqclass P }.

Definition class (X : SET') : Acz -> Prop :=
  proj1_sig X.

Definition ele X Y :=
  forall s t, (class X) s -> (class Y) t -> Ain s t.

Definition sub X Y :=
  forall Z, ele Z X -> ele Z Y.

Lemma Aeq_eqclass s :
  eqclass (Aeq s).
Proof.
  now exists s.
Qed.

Hint Resolve Aeq_eqclass : core.



(* Facts about equivalence classes *)

Definition classof (s : Acz) : SET' :=
  exist _ (Aeq s) (Aeq_eqclass s).

Lemma class_eq X X' s s' :
  Aeq s s' -> class X s -> class X' s' -> X = X'.
Proof using ce.
  destruct X as [P HP], X' as [P' HP']; simpl.
  intros H1 H2 XX. assert (H : P = P').
  - destruct HP as [t ->], HP' as [t' ->].
    apply ce. intros u. rewrite H2, H1, XX. tauto.
  - subst P'. now rewrite (PI HP HP').
Qed.

Lemma classof_ex X :
  exists s, X = classof s.
Proof using ce.
  destruct X as [P[s ->]]; simpl. exists s.
  apply (@class_eq _ _ s s); simpl; auto; reflexivity.
Qed.

Lemma classof_class s :
  class (classof s) s.
Proof.
  simpl. reflexivity.
Qed.

Lemma classof_eq s t :
  classof s = classof t <-> Aeq s t.
Proof using ce.
  split; intros H.
  - specialize (classof_class s).
    intros XX. rewrite H in XX. symmetry. exact XX.
  - apply (class_eq H); simpl; trivial.
Qed.

Lemma classof_ele s t :
  ele (classof s) (classof t) <-> Ain s t.
Proof.
  split; intros H.
  - apply H; simpl; auto.
  - intros s' t' H1 H2. now rewrite <- H1, <- H2.
Qed.

Lemma classof_sub s t :
  sub (classof s) (classof t) <-> ASubq s t.
Proof using ce.
  split; intros H1.
  - intros u H2. now apply classof_ele, H1, classof_ele.
  - intros Z H2. destruct (classof_ex Z) as [u ->].
    now apply classof_ele, H1, classof_ele.
Qed.

Hint Resolve classof_class classof_eq classof_ele classof_sub : core.



(* We define a Z-structure on SET' *)

Definition empty :=
  classof AEmpty.

Definition upair' X Y u :=
  exists s t, (class X) s /\ (class Y) t /\ Aeq u (Aupair s t).

Lemma upair_eqclass X Y :
  eqclass (upair' X Y).
Proof using ce.
  destruct (classof_ex X) as [s ->].
  destruct (classof_ex Y) as [t ->].
  exists (Aupair s t). apply ce. intros z. split; intros H.
  - destruct H as [s'[t'[H1[H2 H3]]]]; simpl in H1, H2.
    now rewrite H1, H2, H3.
  - exists s, t. simpl. repeat split; auto.
Qed.

Definition upair X Y :=
  exist _ (upair' X Y) (upair_eqclass X Y).

Definition union' X t :=
  exists s, (class X) s /\ Aeq t (Aunion s).

Lemma union_eqclass X :
  eqclass (union' X).
Proof using ce.
  destruct (classof_ex X) as [s ->].
  exists (Aunion s). apply ce. intros z. split; intros H.
  - destruct H as [s'[H1 H2]]; simpl in H1.
    now rewrite H1, H2.
  - exists s. auto.
Qed.

Definition union X :=
  exist _ (union' X) (union_eqclass X).

Definition power' X t :=
  exists s, (class X) s /\ Aeq t (Apower s).

Lemma power_eqclass X :
  eqclass (power' X).
Proof using ce.
  destruct (classof_ex X) as [s ->].
  exists (Apower s). apply ce. intros t. split; intros H.
  - destruct H as [s'[H1 H2]]; simpl in H1.
    now rewrite H1, H2.
  - exists s. auto.
Qed.

Definition power X :=
  exist _ (power' X) (power_eqclass X).

Definition empred (P : SET' -> Prop) :=
  fun s => P (classof s).

Fact empred_Aeq P :
  cres Aeq (empred P).
Proof using ce.
  intros s s' H % classof_eq. unfold empred. now rewrite H.
Qed.

Definition sep' P X t :=
  exists s, (class X) s /\ Aeq t (Asep (empred P) s).

Lemma sep_eqclass P X :
  eqclass (sep' P X).
Proof using ce.
  destruct (classof_ex X) as [s ->].
  exists (Asep (empred P) s). apply ce. intros t. split; intros H.
  - destruct H as [s'[H1 H2]]; simpl in H1.
    now rewrite H2, (Asep_proper (@empred_Aeq P) H1).
  - exists s. auto.
Qed.

Definition sep P X :=
  exist _ (sep' P X) (sep_eqclass P X).




(* We prove the extensional axioms of Z for the quotient type *)

(* Extensionality *)

Lemma set_ext X Y : 
  sub X Y /\ sub Y X <-> X = Y.
Proof using ce.
  destruct (classof_ex X) as [s ->].
  destruct (classof_ex Y) as [t ->].
  repeat rewrite classof_sub. rewrite classof_eq.
  split; intros H.
  - now apply Aeq_ext.
  - rewrite H. split; firstorder.
Qed.

(* Empty *)

Lemma emptyE X :
  ~ ele X empty.
Proof using ce.
  destruct (classof_ex X) as [s ->].
  unfold empty. rewrite classof_ele.
  apply AEmptyAx.
Qed.

(* Unordered Pairs *)

Lemma upair_welldef s t :
  upair (classof s) (classof t) = classof (Aupair s t).
Proof.
  pose (u := Aupair s t).
  apply (class_eq (s:=u) (s':=u)); trivial.
  exists s, t. auto.
Qed.

Lemma upairAx X Y Z :
  ele Z (upair X Y) <-> Z = X \/ Z = Y.
Proof.
  destruct (classof_ex Z) as [u ->].
  destruct (classof_ex X) as [s ->].
  destruct (classof_ex Y) as [t ->].
  repeat rewrite classof_eq.
  rewrite upair_welldef, classof_ele.
  apply AupairAx.
Qed.

(* Union *)

Lemma union_welldef s :
  union (classof s) = classof (Aunion s).
Proof.
  pose (t := Aunion s).
  apply (class_eq (s:=t) (s':=t)); trivial.
  exists s. auto.
Qed.

Lemma unionAx X Z :
  ele Z (union X) <-> exists Y, ele Y X /\ ele Z Y.
Proof.
  destruct (classof_ex Z) as [u ->].
  destruct (classof_ex X) as [s ->].
  rewrite union_welldef, classof_ele, AunionAx.
  split; intros [t H].
  - exists (classof t). now repeat rewrite classof_ele.
  - destruct (classof_ex t) as [t' ->].
    exists t'. now repeat rewrite <- classof_ele.
Qed.

(* Power *)

Lemma power_welldef s :
  power (classof s) = classof (Apower s).
Proof.
  pose (t := Apower s).
  apply (class_eq (s:=t) (s':=t)); trivial.
  exists s. auto.
Qed.

Lemma powerAx X Y :
  ele Y (power X) <-> sub Y X.
Proof.
  destruct (classof_ex Y) as [t ->].
  destruct (classof_ex X) as [s ->].
  rewrite power_welldef, classof_ele, classof_sub.
  apply ApowerAx.
Qed.

(* Separation *)

Lemma sep_welldef P s :
  sep P (classof s) = classof (Asep (empred P) s).
Proof.
  pose (t := Asep (empred P) s).
  apply (class_eq (s:=t) (s':=t)); trivial.
  exists s. auto.
Qed.

Lemma sepAx P X Y :
  ele Y (sep P X) <-> ele Y X /\ P Y.
Proof.
  destruct (classof_ex Y) as [s ->].
  destruct (classof_ex X) as [t ->].
  rewrite sep_welldef. repeat rewrite classof_ele.
  apply AsepAx, empred_Aeq.
Qed.

(* Infinity *)

Definition succ X :=
  union (upair X (upair X X)).

Definition inductive X :=
  ele empty X /\ forall Y, ele Y X -> ele (succ Y) X.

Definition om :=
  classof Aom.

Lemma succ_eq s :
  succ (classof s) = classof (Asucc s).
Proof.
  apply set_ext. split; intros X H.
  - apply unionAx in H as [Y[H1 H2]].
    destruct (classof_ex X) as [t ->].
    apply classof_ele. apply AunionAx.
    apply upairAx in H1 as [->| ->].
    + exists s. split; try now apply classof_ele.
      apply AupairAx. now left.
    + exists (Aupair s s). rewrite AupairAx. split; auto.
      apply upairAx in H2. rewrite !classof_eq in H2. now apply AupairAx.
  - destruct (classof_ex X) as [t ->].
    apply classof_ele in H.
    apply AunionAx in H as [u[H1 H2]].
    apply unionAx.
    apply AupairAx in H1 as [H1| H1]; subst.
    + exists (classof u). split; try now apply classof_ele.
      apply upairAx. left. now apply classof_eq.
    + exists (upair (classof s) (classof s)). rewrite upairAx. split; auto.
      rewrite H1 in H2. apply AupairAx in H2. rewrite <- !classof_eq in H2. now apply upairAx.
Qed.

Lemma Ainductive_inductive s :
  Ainductive s <-> inductive (classof s).
Proof.
  split; intros H.
  - split.
    + apply classof_ele. apply H.
    + intros X H'. destruct (classof_ex X) as [t ->].
      rewrite succ_eq. apply classof_ele, H.
      now apply classof_ele.
  - split.
    + apply classof_ele. apply H.
    + intros t Ht. apply classof_ele.
      rewrite <- succ_eq. apply H.
      now apply classof_ele.
Qed.

Lemma om_Ax1 :
  inductive om.
Proof.
  split.
  - apply classof_ele. apply AomAx1.
  - intros X H. destruct (classof_ex X) as [s ->].
    rewrite succ_eq. apply classof_ele, AomAx1.
    now apply classof_ele.
Qed.

Lemma om_Ax2 :
  forall X, inductive X -> sub om X.
Proof.
  intros X H. destruct (classof_ex X) as [s ->].
  apply classof_sub. now apply AomAx2, Ainductive_inductive.
Qed.

End Model.
