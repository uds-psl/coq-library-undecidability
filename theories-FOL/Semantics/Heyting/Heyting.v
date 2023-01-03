Set Implicit Arguments.
Unset Strict Implicit.
Require Export Setoid Morphisms.
Require Export Coq.Program.Basics.
From FOL Require Import FullSyntax.
From Equations Require Import Equations.
From Coq Require Import Arith Lia List Program.Equality.

Class HeytingAlgebra : Type :=
  {
    H : Type ;
    
    R : H -> H -> Prop ;
    Rref : Reflexive R ;
    Rtra : Transitive R ;
    
    Bot : H ;
    Meet : H -> H -> H ;
    Join : H -> H -> H ;
    Impl : H -> H -> H ;
    
    Bot1 : forall u, R Bot u ;
    (*Bot2 : ~ R (Imp Bot Bot) Bot ;*)
    Meet1 : forall u v w, R w u /\ R w v <-> R w (Meet u v) ;
    Join1 : forall u v w, R u w /\ R v w <-> R (Join u v) w ;
    Impl1 : forall u v w, R (Meet w u) v <-> R w (Impl u v) ;
  }.

Coercion H : HeytingAlgebra >-> Sortclass.
Notation "s '<=' t" := (R s t) (at level 70).



(* Registering the relation R of Heyting algebras as preorder for rewriting *)
#[global]
Instance preorder_HA (HA : HeytingAlgebra) :
  PreOrder (@R HA).
Proof.
  split. apply Rref. apply Rtra.
Qed.



(* Simple properties of Heyting algebras *)

Section HAProperty.

  Context { HA : HeytingAlgebra }.
  Implicit Type u v w : HA.

  Definition eqH u v := u <= v /\ v <= u.

  Lemma Meet2 u v :
    Meet u v <= u.
  Proof.
    now apply (Meet1 u v).
  Qed.

  Lemma Meet3 u v :
    Meet u v <= v.
  Proof.
    now apply (Meet1 u v).
  Qed.

  Lemma Meet_com u v :
    Meet u v <= Meet v u.
  Proof.
    apply Meet1; split; auto using Meet2, Meet3.
  Qed.

  Lemma Meet_left x y z :
    x <= y -> Meet z x <= Meet z y.
  Proof.
    intros H. apply Meet1. split.
    - apply Meet2.
    - rewrite <- H. apply Meet3.
  Qed.

  Definition Top := Impl Bot Bot.

  Lemma Top1 u :
    u <= Top.
  Proof.
    apply Impl1, Meet3.
  Qed.

  Lemma Join2 u v :
    u <= Join u v.
  Proof.
    now apply (Join1 u v).
  Qed.

  Lemma Join3 u v :
    v <= Join u v.
  Proof.
    now apply (Join1 u v).
  Qed.

  Lemma Join_com u v :
    eqH (Join u v) (Join v u).
  Proof.
    split; apply Join1; split; auto using Join2, Join3.
  Qed.

  Lemma Imp2 u v :
    Meet (Impl u v) u <= v.
  Proof. 
    apply Impl1, Rref.
  Qed.

  Lemma Meet_assoc u v w :
    Meet u (Meet v w) <= Meet (Meet u v) w.
  Proof.
    simpl. apply Meet1. split.
    - apply Meet1. split.
      + apply Meet2.
      + now rewrite Meet3, Meet2.
    - now rewrite Meet3, Meet3.
  Qed.

  Lemma Meet_extend x y :
    x <= y -> x <= Meet x y.
  Proof.
    intros H. apply Meet1. now split.
  Qed.

  Lemma Imp_bot x y :
    y <= Impl Bot x.
  Proof.
    apply Impl1. rewrite Meet3. apply Bot1.
  Qed.

  Lemma meet_join_distr x y z :
    Meet x (Join y z) <= Join (Meet x y) (Meet x z).
  Proof.
    rewrite Meet_com, Impl1, <- Join1. split.
    - rewrite <- Impl1, Meet_com. apply Join2.
    - rewrite <- Impl1, Meet_com. apply Join3.
  Qed.

  Lemma meet_join_expansion x y z :
    x <= Join y z -> x <= Join (Meet x y) (Meet x z).
  Proof.
    intros H. rewrite <- meet_join_distr.
    apply Meet1. split; trivial. reflexivity.
  Qed.
  
  Definition equiv_HA x y := x <= y /\ y <= x.
  Notation "x ≡ y" := (equiv_HA x y) (at level 40).

  Global Instance subrelation_HA : subrelation equiv_HA R.
  Proof.
    firstorder.
  Qed.

  
  Global Instance subrelation_HA_flip : subrelation equiv_HA (flip R).
  Proof.
    firstorder.
  Qed.
  
  Global Instance equiv_HA_refl : Equivalence equiv_HA.
  Proof.
    split.
    - split; reflexivity.
    - split; eapply H0.
    - split. now rewrite H0, H1. now rewrite <- H1, <- H0.
  Qed.

  Hint Resolve Meet2 Meet3 Join2 Join3 Impl1 Imp2 : core.
      
  Global Instance proper_HA_Meet : Proper (equiv_HA ==> equiv_HA ==> equiv_HA) Meet.
  Proof.
    intros ? ? ? ? ? ?.
    split.
    - rewrite <- Meet1, <- H0, <- H1; eauto.
    - rewrite <- Meet1, H0, H1; eauto.
  Qed.
  
  Global Instance proper_HA_Join : Proper (equiv_HA ==> equiv_HA ==> equiv_HA) Join.
  Proof.
    intros ? ? ? ? ? ?.
    split.
    - rewrite <- Join1, H0, H1; eauto.
    - rewrite <- Join1, <- H0, <- H1; eauto.
  Qed.

  Global Instance proper_HA_Impl : Proper (equiv_HA ==> equiv_HA ==> equiv_HA) Impl.
  Proof.
    intros ? ? ? ? ? ?.
    split.
    - rewrite <- Impl1. rewrite <- H1, <- H0. eauto.
    - rewrite <- Impl1. rewrite H1, H0. eauto.
  Qed.
  
End HAProperty.

Notation is_inf P inf :=
  (forall u, (forall v, P v -> u <= v) <-> u <= inf).

Notation is_sup P sup :=
  (forall u, (forall v, P v -> v <= u) <-> sup <= u).
#[global]
Hint Resolve Meet2 Meet3 : core.

(* ** Complete Heyting Algebras *)

Class CompleteHeytingAlgebra : Type :=
  {
    HA : HeytingAlgebra ;
    Inf : (HA -> Prop) -> HA ;
    Inf1 : forall (P : HA -> Prop), is_inf P (Inf P) ;
  }.

Coercion HA : CompleteHeytingAlgebra >-> HeytingAlgebra.

Section CHAProperty.

  Context { HA : CompleteHeytingAlgebra }.
  Implicit Type u v w : HA.
  Implicit Type P : HA -> Prop.

  Lemma Inf2 P u :
    P u -> Inf P <= u.
  Proof.
    now apply Inf1.
  Qed.

  Definition Inf_indexed I (F : I -> HA) :=
    Inf (fun u => exists i, equiv_HA u (F i)).

  Lemma Inf_indexed1 I (F : I -> HA) u :
    (forall i, u <= F i) <-> u <= Inf_indexed F.
  Proof.
    unfold Inf_indexed. rewrite <- Inf1. split; intros H.
    - intros v [i ->]. now apply H.
    - intros i. apply H. now exists i.
  Qed.

  Definition Sup P :=
    Inf (fun u => forall v, P v -> v <= u).

  Lemma Sup2 P u :
    P u -> u <= Sup P.
  Proof.
    intros H. apply Inf1. firstorder.
  Qed.

  Lemma Sup1 P :
    is_sup P (Sup P).
  Proof.
    split; intros H.
    - now apply Inf2.
    - intros v H' % Sup2. now rewrite H'.
  Qed.

  Definition Sup_indexed I (F : I -> HA) :=
    Sup (fun u => exists i, equiv_HA u (F i)).

  Lemma Sup_indexed1 I (F : I -> HA) u :
    (forall i, F i <= u) <-> Sup_indexed F <= u.
  Proof.
    unfold Sup_indexed. rewrite <- (Sup1 _ u). split; intros H.
    - intros v [i ->]. now apply H.
    - intros i. apply H. now exists i.
  Qed.

  Lemma meet_sup_distr x I (F : I -> HA) :
    Meet x (Sup_indexed F) <= Sup_indexed (fun i => Meet x (F i)).
  Proof.
    rewrite Meet_com, Impl1, <- Sup_indexed1.
    intros i. rewrite <- Impl1, Meet_com.
    apply Sup2. now exists i.
  Qed.

  Lemma meet_sup_expansion x I (F : I -> HA) :
    x <= Sup_indexed F -> x <= Sup_indexed (fun i => Meet x (F i)).
  Proof.
    intros H. rewrite <- meet_sup_distr.
    apply Meet1. split; trivial. reflexivity.
  Qed.

  Instance proper_HA_Inf : Proper (pointwise_relation _ iff ==> equiv_HA) Inf.
  Proof.
    intros ? ? ?.
    split.
    - rewrite <- Inf1. intros. eapply H0 in H1.
      now eapply Inf2.
    - rewrite <- Inf1. intros. eapply H0 in H1.
      now eapply Inf2.
  Qed.      

  Instance proper_HA_Sup : Proper (pointwise_relation _ iff ==> equiv_HA) Sup.
  Proof.
    intros ? ? ?. unfold Sup. eapply proper_HA_Inf.
    intros ?.
    split; firstorder.
  Qed.      

  Instance proper_HA_Sup_indexed I : Proper (pointwise_relation _ equiv_HA ==> equiv_HA) (@Sup_indexed I).
  Proof.
    intros ? ? ?. unfold Sup_indexed. eapply proper_HA_Sup.
    split.
    - firstorder subst. exists x0. split. rewrite H1. eapply H0. rewrite <- H2. eapply H0.
    - firstorder subst. exists x0. split. rewrite H1. eapply H0. rewrite <- H2. eapply H0.
  Qed.      
  
  Instance proper_HA_Inf_indexed I : Proper (pointwise_relation _ equiv_HA ==> equiv_HA) (@Inf_indexed I).
  Proof.
    intros ? ? ?. unfold Inf_indexed. eapply proper_HA_Inf.
    split.
    - firstorder subst. exists x0. split. rewrite H1. eapply H0. rewrite <- H2. eapply H0.
    - firstorder subst. exists x0. split. rewrite H1. eapply H0. rewrite <- H2. eapply H0.
  Qed.      

  Notation "A <~> B" := ((A -> B) * (B -> A))%type (at level 85) : type_scope.      
  
End CHAProperty.


(** ** Heyting Semantics **)

Section CHAEval.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Context { HA : CompleteHeytingAlgebra }.

  Variable hinter_Pr : forall (P : Σ_preds), Vector.t term (ar_preds P) -> HA.

  Obligation Tactic := intros; subst; cbn; try lia.

  Derive NoConfusion for falsity_flag.

  Equations hsat (phi : form) : HA by wf (size phi) lt :=
    hsat (atom P v) := hinter_Pr v ;
    hsat ⊥ := Bot ;
    hsat (phi → psi) := Impl (hsat phi) (hsat psi) ;
    hsat (phi ∧ psi) := Meet (hsat phi) (hsat psi) ;
    hsat (phi ∨ psi) := Join (hsat phi) (hsat psi) ;
    hsat (∀ phi) := Inf_indexed (fun t => hsat (phi [t..])) ;
    hsat (∃ phi) := Sup_indexed (fun t => hsat (phi [t..])).
  Next Obligation.
    rewrite subst_size. econstructor.
  Qed.
  Next Obligation.
    rewrite subst_size. econstructor.
  Qed.

  Definition hsat_L A : HA :=
    Inf (fun x => exists phi, In phi A /\ x = hsat phi).

  Lemma top_hsat_L :
    Top <= hsat_L nil.
  Proof.
    apply Inf1. intros v [phi [[] _]].
  Qed.

End CHAEval.

(* ** Boolean Semantics *)

Definition boolean (HA : HeytingAlgebra) :=
  forall x y : HA, Impl (Impl x y) x <= x.

