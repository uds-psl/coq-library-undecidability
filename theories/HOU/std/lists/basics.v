Set Implicit Arguments.
Require Import List Arith Lia Morphisms FinFun Init.Wf.
From Undecidability.HOU Require Import std.decidable.
Import ListNotations.

Set Default Proof Using "Type".

Arguments incl {_} _ _.
Definition seteq {X: Type} (A B: list X) := incl A B /\ incl B A.
Definition strict_incl {X: Type} (A B: list X) :=
  incl A B /\ exists x, In x B /\ ~ In x A.
Notation "a ∈ A" := (In a A) (at level 70).
Notation "A ⊆ B" := (incl A B) (at level 70).
Notation "A ⊊ B" := (strict_incl A B) (at level 70).
Notation "A === B" := (seteq A B) (at level 70).
Notation "| A |" := (length A) (at level 65).


Section BasicLemmas.

  Variable X Y: Type.

  Implicit Type f: X -> Y.
  Implicit Type p: X -> bool.
  Implicit Type A B C : list X.
  Implicit Type a b c : X. 


  Lemma incl_refl A: A ⊆ A.
  Proof. firstorder. Qed.

  Lemma incl_trans A B C: A ⊆ B -> B ⊆ C -> A ⊆ C.
  Proof. firstorder. Qed.

  Lemma strict_incl_trans A B C: A ⊊ B -> B ⊊ C -> A ⊊ C.
  Proof. firstorder. Qed.

  Lemma strict_incl_incl_trans A B C: A ⊊ B -> B ⊆ C -> A ⊊ C.
  Proof. firstorder. Qed.

  Lemma incl_strict_incl_trans A B C: A ⊆ B -> B ⊊ C -> A ⊊ C.
  Proof. firstorder. Qed.


  Lemma seteq_refl A: A === A.
  Proof. firstorder. Qed.

  Lemma seteq_trans A B C: A === B -> B === C -> A === C.
  Proof. firstorder. Qed.

  Lemma seteq_sym A B: A === B -> B === A.
  Proof. firstorder. Qed.

  
  Global Instance incl_preorder: PreOrder (@incl X). 
  Proof. firstorder. Qed.

  Global Instance strict_incl_transitive: Transitive (@strict_incl X).
  Proof. firstorder. Qed.

  Global Instance seteq_preorder: PreOrder (@seteq X).
  Proof. firstorder. Qed.

  Global Instance seteq_equivalence: Equivalence (@seteq X).
  Proof. firstorder. Qed.

  Hint Resolve incl_refl seteq_refl : listdb.





 


  (* ∈ *)
  Lemma in_ind e (P: list X -> Prop):
    (forall A, P (e :: A)) -> (forall a A, P A -> P (a :: A)) -> forall A, e ∈ A -> P A.
  Proof.
    intros BH IH; induction A; cbn;
      intuition; subst; intuition.
  Qed.

  Global Instance proper_in_incl: Proper (eq ++> incl ==> Basics.impl) (@In X).
  Proof.
    intros ?? -> ???. firstorder.   
  Qed.

  Global Instance in_seteq_proper: Proper (eq ++> seteq ++> iff) (@In X).
  Proof.
    intros ?? -> ???. firstorder.
  Qed.


  (* ⊆ *)
  Global Instance subrel_incl_seteq: subrelation seteq (@incl X).
  Proof. intros ??; firstorder. Qed.

  Global Instance incl_seteq_proper: Proper (seteq ++> seteq ++> iff) (@incl X).
  Proof. firstorder. Qed.

  
  Lemma incl_app A B C: A ++ B ⊆ C <-> A ⊆ C /\ B ⊆ C.
  Proof. induction A; firstorder. Qed.

  Lemma seteq_incl_left A B: A === B -> A ⊆ B.
  Proof. firstorder. Qed.

  Lemma seteq_incl_right A B: A === B -> B ⊆ A.
  Proof. firstorder. Qed.
  
  Lemma incl_seteq A B: A ⊆ B -> B ⊆ A -> A === B.
  Proof. firstorder. Qed.


  Lemma incl_nil A: nil ⊆ A.
  Proof. intros x []. Qed.

  Lemma incl_cons a A B: a :: A ⊆ B <-> a ∈ B /\ A ⊆ B.
  Proof. split; unfold incl; firstorder; congruence. Qed.

  Lemma incl_cons_build a A B: a ∈ B -> A ⊆ B -> a :: A ⊆ B.
  Proof. intuition. Qed.

  Lemma incl_cons_project_l a A B: a :: A ⊆ B -> a ∈ B.
  Proof. intuition. Qed.

  Lemma incl_cons_project_r a A B: a :: A ⊆ B -> A ⊆ B.
  Proof. firstorder. Qed.


  Lemma incl_cons_drop b A B : A ⊆ B -> A ⊆ b :: B.
  Proof. firstorder. Qed.
  
  Lemma incl_filter p A: filter p A ⊆ A.
  Proof. induction A as [|a A]; cbn; try destruct (p a); firstorder. Qed.


  Lemma incl_distr_left A B C: A ⊆ B -> A ⊆ B ++ C.
  Proof. intuition. Qed.

  Lemma incl_distr_right A B C: A ⊆ C -> A ⊆ B ++ C. 
  Proof. intuition.  Qed.

  Lemma incl_app_project_left A B C: A ++ B ⊆ C -> A ⊆ C.
  Proof. intros H x Hx. eapply H, in_app_iff. eauto. Qed.

  Lemma incl_app_project_right A B C: A ++ B ⊆ C -> B ⊆ C.
  Proof. intros H x Hx. eapply H, in_app_iff. eauto. Qed.

  Lemma incl_app_build A B C: A ⊆ C -> B ⊆ C -> A ++ B ⊆ C.
  Proof. intros; eapply incl_app; intuition. Qed.


  Global Instance incl_cons_proper: Proper (eq ++> incl ++> incl) (@cons X).
  Proof. intros ??-> ???; firstorder. Qed.

  Global Instance seteq_cons_proper: Proper (eq ++> seteq ++> seteq) (@cons X).
  Proof. intros ??-> ???; firstorder. Qed.

 
  
  Hint Resolve incl_seteq seteq_incl_left seteq_incl_right incl_nil
       incl_cons incl_cons_build incl_cons_project_l incl_cons_project_r
       incl_cons_drop incl_filter
       incl_distr_left incl_distr_right incl_app_project_left
       incl_app_project_right incl_app_build : listdb.


  (* ⊊ *)
  Lemma strict_incl_incl A B: A ⊊ B -> A ⊆ B.
  Proof. firstorder. Qed.

  Lemma incl_strict_incl x A B: x ∈ A -> ~ x ∈ B -> A ⊆ B -> A ⊊ B.
  Proof. firstorder. Qed.

  Lemma strict_incl_eq A B: A ⊊ B -> ~ A === B.
  Proof. firstorder. Qed.

  Lemma strict_incl_project A B: A ⊊ B -> exists x, x ∈ B /\ ~ x ∈ A.
  Proof. firstorder. Qed.

  Global Instance strict_incl_incl_subrel:
    subrelation (@strict_incl X) (@incl X).
  Proof. firstorder. Qed.


  Section WellFoundedStrictInclusion.

    Context {D: Dis X}.
    Lemma nodup_seteq A:
      nodup D A === A.
    Proof.
      split; intros ?; eapply nodup_In; eauto.
    Qed.

    Lemma wf_strict_incl: well_founded (@strict_incl X).
    Proof using D.
      eapply well_founded_lt_compat with (f := fun A => length (nodup eq_dec A)). 
      intros A B [H [x [H1 H2]]].
      assert (nodup eq_dec A ⊆ nodup eq_dec B) as H3 by now rewrite !nodup_seteq.
      eapply NoDup_incl_length in H3 as H4; [| eapply NoDup_nodup].
      eapply le_lt_or_eq in H4 as []; eauto; exfalso.
      eapply NoDup_length_incl in H3. 
      rewrite !nodup_seteq in H3; intuition.
      eapply NoDup_nodup. lia.
    Qed.
    
  End WellFoundedStrictInclusion.
    
  (* app *)
  Global Instance proper_app_incl: Proper (incl ++> incl ++> incl) (@app X).
  Proof.
    intros A A' H1 B B' H2; induction A; firstorder auto with *.
  Qed.
  
  Global Instance proper_app_seteq: Proper (seteq ++> seteq ++> seteq) (@app X).
  Proof.
    intros A A' [H1 H2] B B' [H3 H4].
    split; eapply proper_app_incl; firstorder. 
  Qed.

  Hint Rewrite app_nil_l app_nil_r : listdb.
  Hint Rewrite <- app_comm_cons : listdb.
  Hint Rewrite -> in_app_iff : listdb. 

  Lemma app_comm A B: A ++ B === B ++ A.
  Proof.
    split; intros ?; autorewrite with listdb; firstorder.
  Qed.





  (* rev *)
  Lemma rev_seteq A: rev A === A.
  Proof.
    induction A; cbn; autorewrite with listdb; intuition.
  Qed.

  Global Instance proper_incl_seteq: Proper (@seteq X ++> @seteq X ++> iff) incl.
  Proof.
    intros ??????; firstorder.
  Qed.

  Global Instance proper_rev_incl: Proper (incl ++> incl) (@rev X).
  Proof.
    intros A B H. now rewrite rev_seteq, H, rev_seteq. 
  Qed.
  
  
  Global Instance proper_rev_seteq: Proper (seteq ++> seteq) (@rev X).
  Proof.
    intros A B [H1 H2]; split; eapply proper_rev_incl; eauto.  
  Qed.

  Hint Rewrite rev_seteq rev_involutive rev_length rev_app_distr : listdb.  



  (* map *)
  Lemma map_id_list (g: X -> X) A:
    (forall x, x ∈ A -> g x = x) -> map g A = A.
  Proof.
    intros. induction A; cbn in *; eauto.
    rewrite H; intuition.
    rewrite IHA; firstorder.
  Qed.

  Lemma map_id A: map id A = A.
  Proof.
    induction A; unfold id in *; cbn; congruence.
  Qed.

  Lemma map_nil f: map f nil = nil.
  Proof.
    reflexivity.
  Qed.

  Global Instance map_incl_proper : Proper (eq ++> incl ++> incl) (@map Y X).
  Proof.
    intros ?? -> A B H.
    induction A; cbn; eauto with listdb.
    eapply incl_cons_build; firstorder. 
    eapply in_map; firstorder.
  Qed.      

  Global Instance map_seteq_proper : Proper (eq ++> seteq ++> seteq) (@map Y X).
  Proof.
    intros ?? -> A B [H1 H2]; split; apply map_incl_proper; firstorder. 
  Qed.      



  Hint Rewrite map_id map_rev map_nil map_cons map_app map_length : listdb.
  Hint Resolve in_map : listdb.





  (* length *)
  Hint Rewrite app_length map_length rev_length : listdb.



  (* filter *)
  Lemma filter_length p A: length (filter p A) <= length A.
  Proof. induction A; cbn; [ constructor | ]; destruct (p a); cbn; lia. Qed.


  Global Instance filter_incl_proper: Proper (eq ++> incl ++> incl) (@filter X).
  Proof.
    intros ?? ->  A B H2; induction A; cbn; eauto with listdb.
    destruct y eqn: H1; eauto with listdb. 
    eapply incl_cons_build; eauto with listdb.
    eapply filter_In; intuition. 
  Qed.

  Global Instance filter_seqteq_proper: Proper (eq ++> seteq ++> seteq) (@filter X).
  Proof.
    intros f g -> A B [H2 H3]; split; apply filter_incl_proper; firstorder. 
  Qed.
  

   
End BasicLemmas.

#[export] Hint Resolve incl_refl seteq_refl : listdb.
#[export] Hint Resolve incl_seteq seteq_incl_left seteq_incl_right incl_nil
     incl_cons incl_cons_build incl_cons_project_l incl_cons_project_r
     incl_cons_drop incl_filter
     incl_distr_left incl_distr_right incl_app_project_left
     incl_app_project_right incl_app_build : listdb.
Hint Rewrite -> in_app_iff : listdb.
Hint Rewrite <- app_comm_cons : listdb.
Hint Rewrite app_nil_l app_nil_r : listdb.
Hint Rewrite rev_seteq rev_involutive rev_length rev_app_distr : listdb.
Hint Rewrite map_id map_rev map_nil map_cons map_app : listdb.
#[export] Hint Resolve in_map : listdb.
Hint Rewrite app_length map_length rev_length : listdb.

#[export] Hint Extern 4 => 
  match goal with
  |[ H: ?x ∈ nil |- _ ] => destruct H
  end : core.



Ltac lsimpl := autorewrite with listdb. 
Tactic Notation "lsimpl" "in" hyp_list(H) := autorewrite with listdb in H. 
Tactic Notation "lsimpl" "in" "*" := autorewrite with listdb in *. 

Ltac lauto  := eauto with listdb. 
