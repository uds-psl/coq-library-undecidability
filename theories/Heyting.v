(** * Heyting Semantics *)

Set Implicit Arguments.
Unset Strict Implicit.
Require Export Setoid Morphisms.



(** ** Heyting Algebras *)

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

  Require Export Coq.Program.Basics.
  
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

  Hint Resolve Meet2 Meet3 Join2 Join3 Impl1 Imp2.
      
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

Hint Resolve Meet2 Meet3.

(** ** Complete Heyting Algebras *)

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

(** ** MacNeille Completion *)

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

  Hint Resolve down_normal.

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
