(** ** MacNeille Completion *)

Set Implicit Arguments.
Unset Strict Implicit.
Require Export Setoid Morphisms.
Require Export Coq.Program.Basics.
From FOL Require Import FullSyntax.
From FOL Require Import Heyting.Heyting.


Structure HeytingMorphism (HA1 HA2 : HeytingAlgebra) (F : HA1 -> HA2) : Type :=
  {
    F_inj : forall u v, F u = F v -> u = v ;
    F_mono : forall u v, u <= v -> F u <= F v ;
      
    F_bot : F Bot = Bot ;
    F_meet : forall u v, F (Meet u v) = Meet (F u) (F v) ;
    F_join : forall u v, F (Join u v) = Join (F u) (F v) ;
    F_impl : forall u v, F (Impl u v) = Impl (F u) (F v) ;

    F_inf : forall P u, is_inf P u -> is_inf (fun v => forall z, v = F z -> P z) (F u) ;
    F_sup : forall P u, is_sup P u -> is_sup (fun v => forall z, v = F z -> P z) (F u) ;
  }.


Section MacNeille.

  Context { HA : HeytingAlgebra }.

  (* Definitions *)

  Definition hset := HA -> Prop.
  Implicit Type X Y : hset.

  Definition hset_elem x X :=
    X x.

  Notation "x ∈ X" := (hset_elem x X) (at level 70).

  Definition hset_sub X Y :=
    forall x, x ∈ X -> x ∈ Y.

  Notation "X ⊆ Y" := (hset_sub X Y) (at level 70).

  Definition hset_equiv X Y :=
    X ⊆ Y /\ Y ⊆ X.
  
  Notation "X ≡ Y" := (hset_equiv X Y) (at level 70).

  Global Instance hset_equiv_equiv :
    Equivalence hset_equiv.
  Proof.
    firstorder.
  Qed.

  Global Instance hset_elem_proper x :
    Proper (hset_equiv ==> iff) (hset_elem x).
  Proof.
    firstorder.
  Qed.

  Global Instance hset_sub_proper :
    Proper (hset_equiv ==> hset_equiv ==> iff) hset_sub.
  Proof.
    firstorder.
  Qed.
  
  Definition lb X :=
    fun y => forall x, x ∈ X -> y <= x.

  Global Instance lb_proper :
    Proper (hset_equiv ==> hset_equiv) lb.
  Proof.
    firstorder.
  Qed.

  Definition ub X :=
    fun y => forall x, x ∈ X -> x <= y.

  Global Instance ub_proper :
    Proper (hset_equiv ==> hset_equiv) ub.
  Proof.
    firstorder.
  Qed.

  Lemma lu_sub X :
    X ⊆ lb (ub X).
  Proof.
    firstorder.
  Qed.

  Lemma lu_idem X :
    lb (ub (lb (ub X))) ≡ lb (ub X).
  Proof.
    split.
    - firstorder.
    - apply lu_sub.
  Qed.

  Definition normal X :=
    lb (ub X) ⊆ X.

  Global Instance normal_proper :
    Proper (hset_equiv ==> iff) normal.
  Proof.
    intros X Y H. unfold normal. now rewrite H.
  Qed.

  Lemma lb_normal X :
    normal (lb X).
  Proof.
    firstorder.
  Qed.

  Definition dclosed X :=
    forall x y, x ∈ X -> y <= x -> X y.

  Lemma normal_dclosed X :
    normal X -> dclosed X.
  Proof.
    intros H x y H1 H2. apply H.
    intros z H3. rewrite H2. now apply H3.
  Qed.

  Lemma normal_bot X :
    normal X -> X Bot.
  Proof.
    intros H. apply H. intros x _. apply Bot1.
  Qed.


  
  (* Operations *)

  Definition hset_bot : hset :=
    fun x => x <= Bot.

  Lemma hset_bot_normal :
    normal hset_bot.
  Proof.
    intros x H. apply H. intros y H'. apply H'.
  Qed.

  Definition hset_meet X Y : hset :=
    fun x => x ∈ X /\ x ∈ Y.

  Global Instance hset_meet_proper :
    Proper (hset_equiv ==> hset_equiv ==> hset_equiv) hset_meet.
  Proof.
    firstorder.
  Qed.

  Lemma hset_meet_normal X Y :
    normal X -> normal Y -> normal (hset_meet X Y).
  Proof.
    intros H1 H2 x H. split.
    - apply H1. firstorder.
    - apply H2. firstorder.
  Qed.

  Definition hset_join X Y : hset :=
    lb (ub (fun x => x ∈ X \/ x ∈ Y)).

  Global Instance hset_join_proper :
    Proper (hset_equiv ==> hset_equiv ==> hset_equiv) hset_join.
  Proof.
    firstorder.
  Qed.

  Lemma hset_join_normal X Y :
    normal (hset_join X Y).
  Proof.
    firstorder.
  Qed.

  Lemma ub_join X Y :
    ub (hset_join X Y) ≡ hset_meet (ub X) (ub Y).
  Proof.
    firstorder.
  Qed.

  Definition hset_inf P : hset :=
    fun x => forall X, P X -> x ∈ X.

  Lemma hset_inf_normal P :
    (forall X, P X -> normal X) -> normal (hset_inf P).
  Proof.
    intros H x Hx X HX. apply H; firstorder.
  Qed.

  Definition hset_impl X Y : hset :=
    fun x => forall y, y ∈ X -> Meet x y ∈ Y.

  Global Instance hset_impl_proper :
    Proper (hset_equiv ==> hset_equiv ==> hset_equiv) hset_impl.
  Proof.
    firstorder.
  Qed.

  Lemma hset_impl_equiv X Y :
    hset_impl X Y ≡ hset_inf (fun Z => exists x, x ∈ X /\ Z ≡ (fun y => Meet y x ∈ Y)).
  Proof.
    split.
    - intros z Hz Z [x[Hx ->] ]. now apply Hz.
    - intros z H y Hy. apply H.
      exists y. split; trivial. reflexivity.
  Qed.

  Lemma hset_impl_normal X Y :
    normal Y -> normal (hset_impl X Y).
  Proof.
    intros HY. rewrite hset_impl_equiv. apply hset_inf_normal.
    intros Z [x[Hx ->] ]. intros z Hz. unfold hset_elem at 1.
    apply HY. intros y Hy. apply Impl1.
    assert (H : Impl x y ∈ ub (fun y : HA => Meet y x ∈ Y)).
    - intros a. unfold hset_elem at 1. intros H.
      apply Impl1. now apply Hy.
    - firstorder.
  Qed.
  


  (* Axioms *)

  Lemma hset_bot1 X :
    normal X -> hset_bot ⊆ X.
  Proof.
    intros H x Hx. apply H. intros y Hy.
    unfold hset_bot in Hx. rewrite Hx.
    apply Bot1.
  Qed.

  Lemma hset_meet1 X Y Z :
    Z ⊆ X /\ Z ⊆ Y <-> Z ⊆ (hset_meet X Y).
  Proof.
    firstorder.
  Qed.

  Lemma hset_join1 X Y Z :
    normal Z -> X ⊆ Z /\ Y ⊆ Z <-> (hset_join X Y) ⊆ Z.
  Proof.
    intros HZ. split.
    - intros [H1 H2] x Hx. apply HZ. firstorder.
    - firstorder.
  Qed.

  Lemma hset_impl1 X Y Z :
    normal X -> normal Y -> normal Z -> hset_meet Z X ⊆ Y <-> Z ⊆ hset_impl X Y.
  Proof.
    intros HX HY HZ. split.
    - intros H x Hx y Hy. apply H. split.
      + eapply (normal_dclosed HZ); eauto. 
      + eapply (normal_dclosed HX); eauto.
    - intros H x [H1 H2]. specialize (H x H1 x H2).
      eapply (normal_dclosed HY); eauto. now apply Meet1.
  Qed.

  Lemma hset_inf1 (P : hset -> Prop) X :
    (forall Y, P Y -> X ⊆ Y) <-> X ⊆ (hset_inf P).
  Proof.
    firstorder.
  Qed.



  (* Algebra constructions *)

  Definition completion_algebra : HeytingAlgebra.
  Proof.
    unshelve eapply (@Build_HeytingAlgebra (sig normal)).
    - intros X Y. exact (proj1_sig X ⊆ proj1_sig Y).
    - exists hset_bot. apply hset_bot_normal.
    - intros [X HX] [Y HY]. exists (hset_meet X Y).
      now apply hset_meet_normal.
    - intros [X HX] [Y HY]. exists (hset_join X Y).
      now apply hset_join_normal.
    - intros [X HX] [Y HY]. exists (hset_impl X Y).
      now apply hset_impl_normal.
    - intros [X HX]. firstorder.
    - intros [X HX] [Y HY] [Z HZ]. firstorder.
    - intros [X HX]. now apply hset_bot1.
    - intros [X HX] [Y HY] [Z HZ]. now apply hset_meet1.
    - intros [X HX] [Y HY] [Z HZ]. now apply hset_join1.
    - intros [X HX] [Y HY] [Z HZ]. now apply hset_impl1.
  Defined.

  Definition completion_calgebra : CompleteHeytingAlgebra.
  Proof.
    unshelve eapply (@Build_CompleteHeytingAlgebra completion_algebra).
    - intros P. exists (hset_inf (fun X => exists H : normal X, P (exist _ X H))).
      apply hset_inf_normal. intros X [HX _]. assumption.
    - intros P [X HX]. cbn. rewrite <- hset_inf1. split.
      + intros H Y [HY HP]. now apply H in HP.
      + intros H [Y HY] HP. apply H. now exists HY.
  Defined.



  (* Embedding *)

  Definition down x :=
    fun y => y <= x.

  Lemma down_normal x :
    normal (down x).
  Proof.
    intros y H. apply H.
    intros z H'. apply H'.
  Qed.
  #[local]
  Hint Resolve down_normal : core.

  Definition embed x : completion_algebra :=
    exist normal (down x) (@down_normal x).

  Lemma down_inj x y :
    down x ⊆ down y -> x <= y.
  Proof.
    intros H. apply H. unfold down, hset_elem. reflexivity.
  Qed.

  Lemma down_mono x y :
    x <= y -> down x ⊆ down y.
  Proof.
    intros H z Hz. unfold down, hset_elem in *. now rewrite Hz.
  Qed.

  Lemma down_bot :
    down Bot ≡ hset_bot.
  Proof.
    firstorder.
  Qed.

  Lemma down_top :
    down Top ≡ hset_impl hset_bot hset_bot.
  Proof.
    split.
    - apply hset_impl1; eauto using down_normal. firstorder.
    - intros x _. apply Impl1. apply Meet3.
  Qed.

  Lemma down_meet x y :
    down (Meet x y) ≡ hset_meet (down x) (down y).
  Proof.
    split.
    - intros z H. apply Meet1, H.
    - intros z H. apply Meet1, H.
  Qed.

  Lemma down_join x y :
    down (Join x y) ≡ hset_join (down x) (down y).
  Proof.
    split.
    - intros z H. apply hset_join_normal; eauto.
      intros u Hu. apply ub_join in Hu as [H1 H2].
      rewrite H. apply Join1. split.
      + apply H1. apply Rref.
      + apply H2. apply Rref.
    - intros z H. apply H. intros u [Hu|Hu].
      + rewrite Hu. apply Join2.
      + rewrite Hu. apply Join3.
  Qed.
  
  Lemma down_impl x y :
    down (Impl x y) ≡ hset_impl (down x) (down y).
  Proof.
    split.
    - intros z Hz u Hu. apply Impl1 in Hz.
      unfold down, hset_elem. now rewrite (Meet_left z Hu).
    - intros z Hz. apply Impl1. apply Hz. apply Rref.
  Qed.

  Lemma down_inf (P : HA -> Prop) x x0 :
    is_inf P x -> P x0 -> down x ≡ hset_inf (fun X => exists x, X = down x /\ P x).
  Proof.
    intros H. split.
    - intros y Hy X [z [-> Hz] ]. now apply (H y).
    - intros y Hy. unfold hset_elem, down. rewrite <- (H y).
      intros z Hz. apply Hy. now exists z.
  Qed.

End MacNeille.

Notation "x ∈ X" := (hset_elem x X) (at level 70).
Notation "X ⊆ Y" := (hset_sub X Y) (at level 20).
Notation "X ≡ Y" := (hset_equiv X Y) (at level 70).

