(** ** Signature Extension  *)

From Undecidability.FOLC Require Import Kripke KripkeCompleteness.

From Equations Require Import Equations.
From Undecidability.FOLC Require Export Gentzen.

Arguments Funcs {_}, _.
Arguments Preds {_}, _.

Record Signature_inj (Σ Σ' : Signature ) :=
  {
    I_Funcs : Funcs Σ -> Funcs Σ' ;
    R_Funcs : Funcs Σ' -> option (Funcs Σ) ; 
    is_inj_Funcs : forall x, R_Funcs (I_Funcs x) = Some x ;
    ar_inj_Funcs : forall x, fun_ar x = fun_ar (I_Funcs x);
    I_Preds : Preds Σ -> Preds Σ' ;
    R_Preds : Preds Σ' -> option (Preds Σ) ;
    is_inj_Preds : forall x, R_Preds (I_Preds x) = Some x ;
    ar_inj_Preds : forall x, pred_ar x = pred_ar (I_Preds x) ;
  }.

Fixpoint embed_term Σ Σ' (inj : Signature_inj Σ Σ') (t : @term Σ) : @term Σ' :=
  match t with
  | var_term n => var_term n
  | Func f v =>
      Func (I_Funcs inj f)
        (cast (Vector.map (embed_term inj) v) (ar_inj_Funcs inj f))
  end.

Fixpoint embed Σ Σ' (inj : Signature_inj Σ Σ') (phi : @form Σ) : @form Σ' :=
  match phi with
    Fal => Fal
  | Pred P v => Pred (I_Preds inj P) (cast (Vector.map (embed_term inj) v) (ar_inj_Preds inj P))
  | Impl φ1 φ2 => Impl (embed inj φ1) (embed inj φ2)
  | All phi => All (embed inj phi)
  end.

Notation make_subst rho := (fun n => var_term (rho n)).

Definition vec_comp {A B C n} {f: A -> B} {g: B -> C} {h} (xs : Vector.t _ n) :
  (forall x, vec_in x xs -> (funcomp  g f) x = h x) -> Vector.map g (Vector.map f xs) = Vector.map h xs.
Proof.
  induction xs. reflexivity.
  cbn. intros. rewrite <- H. f_equal. apply IHxs.
  - intros. eapply H. now right.
  - now left.
Defined.

Lemma cast_eq A n v e : 
  @cast A n v n e = v.
Proof.
  induction v.
  - cbn. reflexivity.
  - cbn. f_equal. now rewrite IHv.
Qed.

Lemma cast_trans A m n l (e1 : m = n) (e2 : n = l) (v : Vector.t A _) :
  cast (cast v e1) e2 = cast v (eq_trans e1 e2) .
Proof.
  subst. rewrite !cast_eq. reflexivity.
Qed.

Lemma embed_subst_term Σ Σ' (inj : Signature_inj Σ Σ') t sigma :
  embed_term inj (subst_term sigma t) = subst_term (sigma >> embed_term inj) (embed_term inj t) .
Proof.
  revert sigma.
  induction t using strong_term_ind.
  - now destruct x.
  - cbn. intros. eapply f_equal. destruct (ar_inj_Funcs inj F).
    rewrite !cast_eq. setoid_rewrite vec_comp; try reflexivity.
    intros. unfold funcomp. now rewrite H. 
Qed.    
    
Lemma embed_subst Σ Σ' (inj : Signature_inj Σ Σ') phi sigma :
  embed inj (subst_form sigma phi) = subst_form (sigma >> embed_term inj) (embed inj phi) .
Proof.
  revert sigma; induction phi; cbn; intros; try congruence.
  - f_equal. destruct (ar_inj_Preds).
    rewrite !cast_eq.
    setoid_rewrite vec_comp; try reflexivity.
    intros. unfold funcomp. now rewrite embed_subst_term.
  - f_equal. rewrite IHphi.
    eapply ext_form. 
    intros. unfold funcomp.
    destruct x; now try setoid_rewrite embed_subst_term. 
Qed.

Lemma prv_embed Σ Σ' (inj : Signature_inj Σ Σ') A phi :
  A ⊢IE phi -> map (embed inj) A ⊢IE embed inj phi.
Proof.
  Hint Constructors prv.
  induction 1; cbn in *; eauto 2.
  - eapply AllI. rewrite map_map in *.
    erewrite map_ext. eassumption.
    intros. unfold form_shift.
    now rewrite embed_subst.
  - eapply AllE with (t0 := embed_term inj t) in IHprv.
    rewrite embed_subst.
    erewrite ext_form. eassumption.
    now destruct x.
  - eapply Ctx. eapply in_map_iff; eauto.
Qed.

Section Tarski.

  Variables Σ Σ' : Signature.
  Variable inj : Signature_inj Σ Σ'.
  Variable D : Type.
  Variable I : @interp Σ D.
  Variable d : D.  

  Instance RI : @interp Σ' D :=
    {|
      i_F := @i_F _ _ I ;
      i_P P v := False ;
      i_f f v := match R_Funcs inj f with Some f' =>
                                         match Nat.eq_dec (fun_ar f) (fun_ar f') with left E =>
                                         @i_f _ _ I f' (cast v E) | right _ => d end | None => d end;

    |}.

  Lemma eval_retract :
    forall (rho : fin -> D) (x : term), eval rho x = (embed_term inj >> eval rho) x.
  Proof.
    intros rho t. induction t using strong_term_ind; cbn.
    - reflexivity.
    - rewrite is_inj_Funcs.
      destruct _.
      + destruct ar_inj_Funcs. rewrite !cast_eq.
        erewrite vec_comp. reflexivity.
        firstorder.        
      + rewrite <- ar_inj_Funcs in n. congruence.
  Qed.
  
End Tarski.    

Section Kripke.

  Variables Σ Σ' : Signature.
  Variable inj : Signature_inj Σ Σ'.
  Variable D : Type.
  Variable M : @kmodel Σ D.
  Variable d : D.

  Program Instance RM : @kmodel Σ' D :=
    {|
      nodes := @nodes _ _ M ;
      reachable := @reachable _ _ M;
      k_interp := RI inj (@k_interp _ _ M) d ;
      k_P u P v := match R_Preds inj P with Some P' =>
                                         match Nat.eq_dec (pred_ar P) (pred_ar P') with left E =>
                                         @k_P _ _ M u P' (cast v E) | right _ => True end | None => True end;
      k_Bot u := @k_Bot _ _ M u
    |}.
  Next Obligation.
    eapply reach_refl.
  Qed.
  Next Obligation.
    eapply reach_tran; eauto.
  Qed.
  Next Obligation.
    intros.
    destruct (R_Preds inj P); try tauto.
    destruct Nat.eq_dec; try tauto.
    eapply mon_P; eauto.
  Qed.
  Next Obligation.
    intros. eapply mon_Bot; eauto.
  Qed.

      
  Lemma ksat_retract phi u rho :
    ksat M u rho phi <-> ksat RM u rho (embed inj phi).
  Proof.
    induction phi in u, rho |- *; cbn.
    - reflexivity.
    - rewrite is_inj_Preds.
      destruct _.
      + destruct (ar_inj_Preds).
        rewrite !cast_eq. erewrite vec_comp. 2:reflexivity.
        erewrite vec_ext. reflexivity.
        eapply eval_retract.
      + rewrite <- ar_inj_Preds in n. congruence.
    - setoid_rewrite IHphi1. setoid_rewrite IHphi2. reflexivity.
    - setoid_rewrite IHphi. reflexivity.
  Qed.

  Fixpoint vec2vars n (v : Vector.t D n) : Vector.t (@term Σ) n :=
    match v in (Vector.t _ n) return Vector.t term n with
    | Vector.nil => Vector.nil
    | @Vector.cons _ a n v => Vector.cons (var_term 0) (Vector.map (fun t => t[↑]) (vec2vars v))
    end.

  Fixpoint vec2env n (v : Vector.t D n) rho : nat -> D :=
    match v in (Vector.t _ n) return nat -> D with
    | Vector.nil => rho
    | @Vector.cons _ a n v => a .: vec2env v rho
    end.
  
  Lemma vec_map_map A B C n (f : A -> B) (g : B -> C) (xs : vector A n) :
    Vector.map g (Vector.map f xs) = Vector.map (fun a => g (f a)) xs.
  Proof.
    induction xs; cbn; congruence.
  Qed.

  Lemma vec2env_map {I : @interp Σ D} n (ds : Vector.t D n) (rho : nat -> D) :
    Vector.map (eval (vec2env ds rho)) (vec2vars ds) = ds.
  Proof.
    induction ds; cbn; trivial.
    f_equal. rewrite <- IHds at 3. rewrite vec_map_map.
    apply vec_ext. intros t. apply eval_comp.
  Qed.

  Lemma vec2env_correct (P : @Preds Σ) (ds : Vector.t D (pred_ar P)) rho u :
    vec2env ds rho ⊨(u, M) Pred P (vec2vars ds) <-> k_P u ds.
  Proof.
    cbn. now rewrite vec2env_map.
  Qed.

  Lemma kexploding_preds (P : @Preds Σ) (ds : Vector.t D (pred_ar P)) (rho : nat -> D) u :
    kexploding M -> k_Bot u -> k_P u ds.
  Proof.
    intros H1 H2. rewrite <- vec2env_correct with (rho:=rho).
    apply (H1 u (vec2env ds rho) (Pred P (vec2vars ds)) u); intuition.
  Qed.

  Lemma kexploding_retract :
    kexploding M -> kexploding RM.
  Proof.
    intros H. apply ksemantic_explosion.
    intros ? ? ? ? ? ? ?.
    change (rho ⊨( v0, M) ⊥) in H1.
    cbn. destruct R_Preds eqn : Peq; trivial. destruct _; trivial.
    apply kexploding_preds; eauto.
  Qed.
  
End Kripke.

Lemma sprv_prv_iff `{Sigma : Signature} {EP : eq_dec Preds} {EF : eq_dec Funcs} A phi :
  A ⊢IE phi <-> A ⊢SE phi.
Proof.
  split; intros.
  - eapply ksoundness in H.
    eapply K_exp_completeness. eapply H. firstorder.
  - now eapply seq_ND with (phi0 := None).
Qed.
  
Lemma prv_back Σ {EP : eq_dec Preds} {EF : eq_dec Funcs} Σ' (inj : Signature_inj Σ Σ') Gamma phi :
  (map (embed inj) Gamma) ⊢IE embed inj phi -> Gamma ⊢IE phi.
Proof.
  intros.
  eapply ksoundness with (C := kexploding) in H. 2:firstorder.
  eapply seq_ND with (phi0 := None).
  eapply K_exp_completeness. 
  intros ? ? ? ? ? ?.
  eapply ksat_retract. eapply H. 2:firstorder.
  now eapply kexploding_retract.
  Unshelve. 2:exact (rho 0). cbn.
  apply in_map_iff in H2 as [psi' [<- HP]].
  apply ksat_retract, H1, HP.
Qed.
