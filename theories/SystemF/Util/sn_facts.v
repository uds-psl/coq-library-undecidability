Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax Undecidability.SystemF.Autosubst.unscoped.
Import UnscopedNotations.
From Undecidability.SystemF.Util Require Import typing_facts term_facts step.
Require Import Setoid Morphisms.

Definition pw_iff {X} p q := (forall x : X, p x <-> q x).
Notation "p == q" := (pw_iff p q) (at level 70).

Instance Equiv_pw_iff {X} : Equivalence (@pw_iff X).
Proof.
  firstorder.
Qed.

Lemma pw {X : Type} P Q :
  (forall x : X, P x <-> Q x) ->
  (forall x, P x) <-> (forall x, Q x).
Proof.
  firstorder.
Qed.
Ltac pw := repeat (apply pw; intros).

(* * Strong Normalisation  *)

(* ** Logical Relation  *)

Definition active P :=
  match P with
  | abs _ _ | ty_abs _ => true
  | _ => false
  end.

Definition tpred := term -> Prop.

Definition M (p : tpred) : tpred :=
  fun P => forall ξ1 ξ2, p (ren_term ξ1 ξ2 P).

Inductive R (p : tpred) P : Prop :=
| RI : (active P = true -> M p P) ->
       (forall Q, step P Q -> R p Q) ->
       R p P.

Instance R_ext :
  Proper (pw_iff ==> eq ==> iff) R.
Proof.
  intros p1 p2 Heq P ? ->. split; induction 1 as [P H H1 H2].
  - econstructor. intros H3 ξ1 ξ2. eapply Heq. now eapply H. eauto.
  - econstructor. intros H3 ξ1 ξ2. eapply Heq. now eapply H. eauto.
Qed.

Record model := mk_model
  {
    Var : tpred -> tpred ;
    Arr : tpred -> tpred -> tpred ;
    All : (tpred -> tpred) -> tpred ;
    Var_ext : Proper (pw_iff ==> pw_iff) Var ;
    Arr_ext : Proper (pw_iff ==> pw_iff ==> pw_iff) Arr ;
    All_ext : Proper (pointwise_relation _ pw_iff ==> pw_iff) All
  }.
Existing Instances Var_ext Arr_ext All_ext.

Section Evaluation.
  Variable (M : model).

  Fixpoint eval (ρ : nat -> tpred) (s : poly_type) : tpred :=
    match s with
    | poly_var n => Var M (ρ n)
    | poly_arr s t => Arr M (eval ρ s) (eval ρ t)
    | poly_abs s => All M (fun d => eval (d .: ρ) s)
    end.

  Instance eval_ext :
    Proper (pointwise_relation _ pw_iff ==> eq ==> pw_iff) eval.
  Proof.
    intros ρ1 ρ2 Heq s ? <-. induction s in ρ1, ρ2, Heq |- *; cbn.
    - now rewrite (Heq n).
    - now rewrite IHs1, IHs2.
    - eapply All_ext. intros d. eapply IHs. intros []; cbn; intuition.
  Qed.

  Lemma eval_ren ξ s ρ :
    eval ρ (ren_poly_type ξ s) == eval (ξ >> ρ) s.
  Proof.
    induction s in ξ, ρ |- *; cbn.
    - reflexivity.
    - now rewrite IHs1, IHs2.
    - eapply All_ext. intros d. rewrite IHs.
      eapply eval_ext. now intros []. reflexivity.
  Qed.

  Lemma eval_weaken s ρ d :
    eval (d .: ρ) (ren_poly_type shift s) == eval ρ s.
  Proof. now rewrite eval_ren. Qed.

  Definition lift : model.
    refine (mk_model id (Arr M) (fun F => All M (Var M >> F)) _ _ _).
    abstract firstorder.
    abstract (intros p1 p2 H; eapply All_ext; intros P; eapply H).
  Defined.

End Evaluation.

Lemma eval_subst (M : model) σ s ρ :
  eval M ρ (subst_poly_type σ s) == eval (lift M) (σ >> eval M ρ) s.
Proof.
  induction s in σ, ρ |- *; cbn.
  - reflexivity.
  - now rewrite IHs1, IHs2.
  - eapply All_ext. intros d. rewrite IHs. asimpl.
    eapply eval_ext; try reflexivity. intros []. reflexivity. eapply eval_weaken.
Qed.

Lemma eval_beta (M : model) s t ρ :
  eval M ρ (subst_poly_type (t .: poly_var) s) == eval (lift M) (eval M ρ t .: ρ >> Var M) s.
Proof.
  rewrite eval_subst.
  eapply eval_ext. now intros []. reflexivity.
Qed.

Definition D : model.
Proof.
  refine {| Var :=  id ;
            Arr := fun p q P => match P with abs s P => forall Q, R p Q -> R q (subst_term poly_var (Q .: var) P) | _ => False end ;
            All := fun F P => match P with ty_abs P => forall p s, R (F p) (subst_term (s .: poly_var) var P) | _ => False end |}.
  - abstract firstorder.
  - abstract (intros p1 p2 Heq1 p1' p2' Heq2 []; cbn; try tauto; pw; now rewrite Heq1, Heq2).
  - abstract (intros F1 F2 Heq []; cbn; try tauto; pw; now rewrite (Heq x)).
Defined.

(* Instance equiv_D : equiv D. *)

Notation V s ρ := (eval D ρ s).
Notation K s ρ := (M (V s ρ)).
Notation E s ρ := (R (V s ρ)).

(* ** Reducibility Candidates  *)

Lemma R_sn p P :
  R p P -> sn P.
Proof.
  induction 1. eauto using sn.
Qed.

Lemma R_step p P Q :
  step P Q -> R p P -> R p Q.
Proof.
  intros ? []. eauto.
Qed.

Lemma R_var p n :
  R p (var n).
Proof.
  econstructor. intros [=].
  intros Q H. inversion H.
Qed.

Lemma R_ren ξ1 ξ2 p P :
  R p P -> R p (ren_term ξ1 ξ2 P).
Proof.
  induction 1 as [P H H0 H1]. econstructor.
  - intros HnP ξ'1 ξ'2. asimpl. eapply H. now destruct P.
  - intros Q.  erewrite rinst_inst_term; try reflexivity.
    intros (P' & H2 & <-) % step_subst_inv.
    erewrite <- rinst_inst_term; try reflexivity. eauto.
Qed.

(* ** Logical Relation  *)

Lemma K_var n ρ P :
  K (poly_var n) ρ P = forall ξ1 ξ2, ρ n (ren_term ξ1 ξ2 P).
Proof.
  reflexivity.
Qed.

Lemma K_arr s t ρ u P :
  K (poly_arr s t) ρ (abs u P) <->
  forall ξ1 ξ2 Q, E s ρ Q -> E t ρ (subst_term (ξ1 >> poly_var) (Q .: ξ2 >> var) P).
Proof.
  unfold M. cbn. pw. asimpl. eapply R_ext. reflexivity.
  now_asimpl.
Qed.

Lemma K_all s ρ P :
  K (poly_abs s) ρ (ty_abs P) <->
  forall ξ p t, E s (p .: ρ) (subst_term (t .: ξ >> poly_var) var P).
Proof.
  unfold M. split.
  - intros H ξ p t. specialize (H ξ id p t). fold ren_term in H.
    eapply R_ext. 3:eapply H. reflexivity. now_asimpl.
  - intros H ξ1 ξ2 p t. specialize (H ξ1 p t).
    pose proof (Hren := R_ren id ξ2 _ _ H). asimpl in Hren.
    eapply R_ext. 3:eapply Hren. reflexivity. now_asimpl.
Qed.

Lemma V_weaken s ρ p :
  V (ren_poly_type shift s) (p .: ρ) == V s ρ.
Proof.
  now rewrite eval_weaken.
Qed.

Lemma K_weaken s ρ p :
  K (ren_poly_type shift s) (p .: ρ) == K s ρ.
Proof.
  intros P. pw. eapply V_weaken.
Qed.

Lemma E_weaken s ρ p :
  E (ren_poly_type shift s) (p .: ρ) == E s ρ.
Proof.
  intros P. eapply R_ext. eapply V_weaken. reflexivity.
Qed.

Lemma V_beta s t ρ :
  V (subst_poly_type (t .: poly_var) s) ρ == V s (V t ρ .: ρ).
Proof.
  now rewrite eval_beta. 
Qed.

Lemma E_beta  s t ρ :
  E (subst_poly_type (t .: poly_var) s) ρ == E s (V t ρ .: ρ).
Proof.
  intros P. now rewrite eval_beta. 
Qed.

(* ** Logical relation on contexts  *)

Definition C (Γ : nat -> poly_type) (ρ : nat -> tpred) : (nat -> term) -> Prop :=
  fun σ => forall n, E (Γ n) ρ (σ n).

Lemma C_ext :
  Proper (pointwise_relation _ eq ==> eq ==> eq ==> iff) C.
Proof.
  split; repeat intros ?; subst. now rewrite <- H. now rewrite H.
Qed.

Lemma C_scons s Γ ρ σ P :
  E s ρ P -> C Γ ρ σ -> C (s .: Γ) ρ (P .: σ).
Proof.
  intros HE HC. hnf. intros []. eassumption. eapply HC.
Qed.

Lemma C_rename Γ ρ σ ξ1 ξ2 :
  C Γ ρ σ -> C Γ ρ (σ >> ren_term ξ1 ξ2).
Proof.
  intros H ?. eapply R_ren, H.
Qed.

Lemma C_up s Γ ρ σ :
  C Γ ρ σ -> C (s .: Γ) ρ (up_term_term σ).
Proof.
  intros H. eapply C_scons. eapply R_var. now eapply C_rename.
Qed.

(* ** Fundamental theorem & Strong Normalisation  *)
Lemma E2_ind s t ρ1 ρ2 p :
  (forall P Q, E s ρ1 P -> E t ρ2 Q -> (forall P', step P P' -> p P' Q) -> (forall Q', step Q Q' -> p P Q') -> p P Q) ->
  forall P Q, E s ρ1 P -> E t ρ2 Q -> p P Q.
Proof.
  intros H P Q. 
  induction 1 in Q |- *. induction 1. 
  eapply H; eauto using R.
Qed.

Lemma E_app s t P Q ρ :
  E (poly_arr s t) ρ P -> E s ρ Q -> E t ρ (app P Q).
Proof.
  revert P Q. eapply E2_ind.
  intros P Q nP nQ IHP IHQ. econstructor.
  inversion 1. intros R Hst. inv Hst; eauto.
  destruct nP. rewrite K_arr in H; eauto.
Qed.

Lemma E_lam s t s' ρ P :
  sn P ->
  (forall ξ1 ξ2 Q, E s ρ Q -> E t ρ (subst_term (ξ1 >> poly_var) (Q .: ξ2 >> var) P)) ->
  E (poly_arr s t) ρ (abs s' P).
Proof.
    induction 1 as [P _ IH]. intros H.
    econstructor.
    - intros _. rewrite K_arr. eauto.
    - intros Q Hst. inv Hst. eapply IH; eauto.
      intros. eapply R_step; eauto using step_subst.
Qed.

Lemma E_tapp s t ρ P r :
  E (poly_abs s) ρ P -> E (subst_poly_type (t .: poly_var) s) ρ (ty_app P r).
Proof.
  induction 1 as [P H IH H2]. eapply E_beta.
  econstructor. inversion 1. intros Q Hst. inv Hst.
  - specialize (H eq_refl). rewrite K_all in H. eauto.
  - eapply H2 in H4. now eapply E_beta in H4.
Qed.

Lemma E_tlam s ρ P :
  sn P ->
  (forall ξ p t, E s (p .: ρ) (subst_term (t .: ξ >> poly_var) var P)) ->
  E (poly_abs s) ρ (ty_abs P).
Proof.
  induction 1 as [P _ IH]. intros H. econstructor.
  - rewrite K_all. intros _. eapply H.
  - intros Q Hst. inv Hst. eapply IH. eauto.
    intros ξ p t.
    eapply R_step; eauto using step_subst.
Qed.

Lemma fundamental {Γ s P} :
  typing Γ P s ->
  forall σ τ ρ, 
  C (fun n => match List.nth_error Γ n with Some x => x | _ => poly_abs (poly_var 0) end) ρ τ -> 
  E s ρ (subst_term σ τ P).
Proof.
  induction 1 as [Γ n s H | | Γ | | ]; intros σ τ ρ HC.
  - specialize (HC n). cbn in HC. rewrite H in HC. eapply HC.
  - cbn. eapply E_app; eauto.
  -  eapply E_lam; fold subst_term.
     + eapply R_sn. eapply IHtyping.
       eapply C_ext. 4:{ eapply C_up, HC. }
       all: try reflexivity.
       now intros []. 
     + intros ξ1 ξ2 Q HQ.
       match goal with [ |- E _ _ ?R] => 
                       replace R with (subst_term (σ >> ren_poly_type ξ1) (Q .: τ >> ren_term ξ1 ξ2) P)
       end.
       * eapply IHtyping. eapply C_ext.
         4:{ eapply C_scons. eauto. eapply C_rename, HC. }
         all: try reflexivity.
         intros []; cbn; try reflexivity.
       * asimpl. eapply ext_term. intros. asimpl.
         -- erewrite rinst_inst_poly_type; reflexivity.
         -- intros []. reflexivity. asimpl.
            erewrite rinst_inst_term; try reflexivity. now asimpl.
  - cbn. eapply E_tapp; eauto.
  - cbn. eapply E_tlam.
    + specialize (IHtyping (up_poly_type_poly_type σ) (τ >> ren_term shift id) ((fun _ => False) .: ρ)).
      eapply R_sn. refine (IHtyping _).
      intros n.
      rewrite Facts.nth_error_map.
      destruct List.nth_error eqn:Eq.
      * cbn. asimpl. eapply E_weaken.
        specialize (HC n). cbn in HC. rewrite Eq in HC.
        eapply R_ren, HC.
      * unfold ssrfun.Option.map, ssrfun.Option.bind, ssrfun.Option.apply.
        eapply R_ren. specialize (HC n). cbn in HC.
        rewrite Eq in HC. eapply HC.
    + intros ξ p t. asimpl. eapply IHtyping.
      intros n. asimpl. eapply R_ext. 2:reflexivity.
      2:{ eapply E_weaken.
          erewrite <- rinst_inst_term; try reflexivity.
          eapply R_ren. eapply HC. }
      * f_equal. rewrite Facts.nth_error_map.
        now destruct List.nth_error eqn:Eq.
Qed.

Lemma SN {Gamma P t} : typing Gamma P t -> sn P.
Proof.
  intros Htp. pose proof (fundamental Htp poly_var var (fun _ _ => False)).
  asimpl in H.
  eapply R_sn, H.
  intros n. eapply R_var.
Qed.

Lemma typing_normal_form {Gamma P t} : typing Gamma P t -> exists Q, normal_form Q /\ typing Gamma Q t.
Proof.
  intros H.
  destruct (sn_normal _ _ _ H (SN H)) as (Q & H1 & H2).
  exists Q. split. eassumption. eapply preservation_star; eauto.
Qed.
