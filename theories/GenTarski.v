(** ** Constructive Analysis of Completeness Theorems *)

(** *** Tarki Models **)

From Undecidability.FOLC Require Export ND.
From Undecidability.FOLC Require Export Enumeration.

Section Tarski.
  Context {Sigma : Signature}.

  (** **** Semantic notions *)

  Section Semantics.
    Variable domain : Type.

    Class interp := B_I
      {
        i_f : forall f : Funcs, Vector.t domain (fun_ar f) -> domain ;
        i_P : forall P : Preds, Vector.t domain (pred_ar P) -> Prop ;
        i_F : Prop
      }.

    Definition env := fin -> domain.

    Context {I : interp }.
    Fixpoint eval (rho : env) (t : term) : domain :=
      match t with
      | var_term s => rho s
      | Func f v => i_f (Vector.map (eval rho) v)
      end.

    Fixpoint sat (rho : env) (phi : form) : Prop :=
      match phi with
      | Pred P v => i_P (Vector.map (eval rho) v)
      | Fal => i_F
      | Impl phi psi => sat rho phi -> sat rho psi
      | All phi => forall d : domain, sat (d .: rho) phi
      end.
  End Semantics.

  Arguments sat  {_ _} _ _, _ _ _ _.

  Notation "rho ⊨ phi" := (sat rho phi) (at level 20).

  Definition constraint := forall D, interp D -> Prop.
  Definition con_subs (C C' : constraint) := (forall D (I : interp D), C' D I -> C D I).
  Definition classical D (I : interp D) :=
    forall rho phi psi, rho ⊨ (((phi --> psi) --> phi) --> phi).
  Definition standard_bot D (I : interp D) := @i_F D I -> False.
  Definition exploding_bot D (I : interp D) := forall rho phi, rho ⊨ (⊥ --> phi).

  Definition SM D (I : interp D) := classical I /\ standard_bot I.
  Definition EM D (I : interp D) := classical I /\ exploding_bot I.
  Definition BLM D (I : interp D) := classical I.

  Definition has_model (C : constraint) (T : theory) :=
    exists D (I : interp D) rho, (forall phi, phi ∈ T -> rho ⊨ phi) /\ C D I.
  Definition valid_T (C : constraint) (T : theory) (phi : form) :=
    forall D (I : interp D), C D I -> forall rho, (forall psi, psi ∈ T -> rho ⊨ psi) -> rho ⊨ phi.
  Definition valid_L (C : constraint) A phi :=
    forall D (I : interp D), C D I -> forall rho, (forall psi, psi el A -> rho ⊨ psi) -> rho ⊨ phi.

  Notation "T '⊫<' C '>' phi" := (valid_T C T phi) (at level 50).
  Notation "T ⊫S phi" := (valid_T SM T phi) (at level 50).
  Notation "T ⊫E phi" := (valid_T EM T phi) (at level 50).
  Notation "T ⊫M phi" := (valid_T BLM T phi) (at level 50).

  (** **** Model relationships **)

  Lemma valid_T_subsumption (C C' : constraint) T phi :
    con_subs C C' -> valid_T C T phi -> valid_T C' T phi.
  Proof.
    firstorder.
  Qed.

  Lemma E_S_subsumption :
    con_subs EM SM.
  Proof.
    firstorder.
  Qed.

  Lemma BL_E_subsumption :
    con_subs BLM EM.
  Proof.
    firstorder.
  Qed.

  (** **** Substitution properties **)

  Section Substs.
    Variable D : Type.
    Variable I : interp D.

    Hint Unfold funcomp.

    Lemma eval_ext rho xi t :
      (forall x, rho x = xi x) -> eval rho t = eval xi t.
    Proof.
      intros H; induction t using strong_term_ind; comp; try congruence.
      f_equal. now apply vec_map_ext. 
    Qed.

    Lemma eval_comp rho xi t :
      eval rho (subst_term xi t) = eval (xi >> eval rho) t.
    Proof.
      induction t using strong_term_ind; comp; try congruence.
      f_equal. erewrite vec_comp. 2: reflexivity. now apply vec_map_ext.
    Qed.

    Lemma sat_ext rho xi phi :
      (forall x, rho x = xi x) -> rho ⊨ phi <-> xi ⊨ phi.
    Proof.
      induction phi in rho, xi |-*; intros Hext; comp.
      - tauto.
      - now rewrite (vec_ext (fun x => eval_ext x Hext)).
      - now erewrite IHphi1, IHphi2.
      - split; intros H' d; eapply (IHphi (d .: rho) (d .: xi) _), H'.
        Unshelve. all: (intros []; cbn; congruence).
    Qed.

    Lemma sat_comp rho xi phi :
      rho ⊨ (subst_form xi phi) <-> (xi >> eval rho) ⊨ phi.
    Proof.
      induction phi in rho, xi |-*; comp.
      - tauto.
      - erewrite vec_comp. 2: reflexivity. now rewrite (vec_ext (fun x => eval_comp rho xi x)).
      - now rewrite IHphi1, IHphi2.
      - setoid_rewrite IHphi. split; intros H d; eapply sat_ext. 2, 4: apply (H d).
        all: intros []; comp; rewrite? eval_comp; now comp.
    Qed.

    Lemma sat_subst rho sigma phi :
      (forall x, eval rho (sigma x) = rho x) -> rho ⊨ phi <-> rho ⊨ (subst_form sigma phi).
    Proof.
      intros Hsigma. rewrite sat_comp. apply sat_ext. now comp.
    Qed.
  End Substs.

  (** **** Soundness **)

  Lemma semantic_dm D {I : interp D} rho phi :
    EM I -> (rho ⊨ ¬ ¬ phi) -> rho ⊨ phi.
  Proof.
    intros [Hclass Hb] Hdn. apply (Hclass rho phi Fal).
    intros H % Hdn. apply Hb, H.
  Qed.

  Section Soundness.
    Context {p : peirce} {b : bottom}.

    Hint Unfold valid_L.

    Lemma Soundness C A phi :
      A ⊢ phi -> (p = class -> con_subs classical C) -> (b = expl -> con_subs exploding_bot C) -> valid_L C A phi.
    Proof.
      induction 1; intros Hclass Hexpl D I HC rho HA; (eauto || (comp; eauto)).
      - intros Hphi. capply IHprv. intros ? []; subst. assumption. now apply HA.
      - intros d. capply IHprv. apply switch_map. intros psi Hphi % HA.
        eapply sat_comp. now comp.
      - eapply sat_comp, sat_ext. 2: apply (IHprv Hclass Hexpl D I HC rho HA (eval rho t)).
        now intros []; asimpl.
      - apply (Hexpl eq_refl _ _ HC); firstorder.
      - apply (Hclass eq_refl D I HC).
    Qed.

    Lemma StrongSoundness C T phi :
      T ⊩ phi -> (p = class -> con_subs classical C) -> (b = expl -> con_subs exploding_bot C) -> valid_T C T phi.
    Proof.
      intros (A & HA1 & HA2) Hclass Hexpl D I HC rho HT. eapply Soundness in HA2; eauto.
    Qed.

    Definition dummy_interp : interp True :=
      {| i_f := fun _ _ => I; i_P := fun _ _ => False; i_F := False |}.

    Lemma dummy_xm rho phi :
      sat True dummy_interp rho phi \/ ~ sat True dummy_interp rho phi.
    Proof.
      induction phi in rho |-*. 1, 2: now right.
      - destruct (IHphi1 rho), (IHphi2 rho); firstorder.
      - destruct (IHphi (I .: rho)).
        + left. now intros [].
        + right. firstorder.
    Qed.

    Lemma dummy_SM :
      SM dummy_interp.
    Proof.
      split.
      - intros rho psi phi. intros Hi. destruct (dummy_xm rho psi). all: firstorder.
      - firstorder.
    Qed.

    Lemma Consistency :
      ~ [] ⊢ ⊥.
    Proof.
      intros H. apply (@Soundness SM) in H. 
      - apply (H True dummy_interp dummy_SM (fun _ => I)). intros _ [].
      - now intros _ D I [].
      - now intros _ D I [_ Hb] rho phi Hf % Hb.
    Qed.
  End Soundness.

  (** **** Model properties *)

  Lemma valid_T_standard_dm T phi C :
    con_subs SM C -> ~ (~ valid_T C T phi) -> valid_T C T phi.
  Proof.
    intros Hs Hn D I HC rho HT. destruct (Hs D I HC) as [Hclass ?]. apply semantic_dm; firstorder.
  Qed.
End Tarski.

Arguments sat  {_ _ _} _ _, _ _ _ _ _.
Notation "rho ⊨ phi" := (sat rho phi) (at level 20).

Arguments valid_T {_} _ _ _.
Notation "T '⊫<' C '>' phi" := (valid_T C T phi) (at level 50).
Notation "T ⊫S phi" := (valid_T SM T phi) (at level 50).
Notation "T ⊫E phi" := (valid_T EM T phi) (at level 50).
Notation "T ⊫M phi" := (valid_T BLM T phi) (at level 50).

(** **** Signature Extensions & Closing Validity **)

Section SigExt.
  Variable D : Type.
  Variable F P : Type.
  Variable F_ar : F -> nat.
  Variable P_ar : P -> nat.

  Hint Unfold axioms.funcomp.

  Definition drop_interp' (I : @interp (sig_ext (B_S F F_ar P P_ar)) D) : @interp (B_S F F_ar P P_ar) D :=
    match I with B_I i_f i_P i_F => @B_I (B_S F F_ar P P_ar) _ (fun f v => i_f (inl f) v) i_P i_F end.

  Lemma drop_interp'_eval (I : @interp (sig_ext (B_S F F_ar P P_ar)) D) rho t :
    @eval _ D I rho (sig_lift_term' t) = @eval _ D (drop_interp' I) rho t.
  Proof.
    destruct I; induction t using strong_term_ind.
    - reflexivity.
    - comp. f_equal. erewrite vec_comp. 2: reflexivity. apply vec_map_ext, H. 
  Qed.

  Lemma drop_interp'_sat (I : @interp (sig_ext (B_S F F_ar P P_ar)) D) rho phi :
    @sat _ D I rho (sig_lift' phi) <-> @sat _ D (drop_interp' I) rho phi.
  Proof.
    destruct I. induction phi in rho |-*; comp.
    - tauto.
    - erewrite vec_comp. 2: reflexivity. comp. erewrite vec_ext. 2: apply drop_interp'_eval. reflexivity.
    - intuition.
    - now setoid_rewrite IHphi.
  Qed.

  Definition lift_interp (I : @interp (B_S F F_ar P P_ar) D) (d : D) : @interp (sig_ext (B_S F F_ar P P_ar)) D :=
    match I with B_I i_f i_P i_F => @B_I (sig_ext (B_S F F_ar P P_ar)) _
                                        (fun f => match f with inl f' => i_f f' | inr _ => fun _ => d end)
                                        i_P i_F
    end.

  Lemma lift_interp_eval (I : @interp (B_S F F_ar P P_ar) D) d rho t :
    @eval _ D (lift_interp I d) rho (sig_lift_term' t) = @eval _ D I rho t.
  Proof.
    destruct I; induction t using strong_term_ind.
    - reflexivity.
    - comp. f_equal. erewrite vec_comp. 2: reflexivity. apply vec_map_ext, H. 
  Qed.

  Lemma lift_interp_sat (I : @interp (B_S F F_ar P P_ar) D) d rho phi :
    @sat _ D (lift_interp I d) rho (sig_lift' phi) <-> @sat _ D I rho phi.
  Proof.
    destruct I. induction phi in rho |-*; comp.
    - tauto.
    - erewrite vec_comp. 2: reflexivity. comp. erewrite vec_ext. 1: reflexivity.
      now setoid_rewrite <- lift_interp_eval with (d := d).
    - intuition.
    - now setoid_rewrite IHphi.
  Qed.

  Definition venv (n : nat) (v : Vector.t D n) (rho : nat -> D) (x : nat) : D :=
    match fin_minus x n with
    | inl i => nth_order v i
    | inr (exist _ y _) => rho y
    end.
  Hint Unfold venv.
  Hint Unfold pref.

  Lemma venv_sat {Sigma : Signature} (I : interp D) n (v : Vector.t D n) rho d phi :
    (d .: venv v rho) ⊨ phi <-> venv (Vector.cons d v) rho ⊨ phi.
  Proof.
    apply sat_ext. intros []. 1: reflexivity. comp. destruct (fin_minus n0 n).
    2: now destruct s. now rewrite Fin.of_nat_ext with (h' := l) at 1.
  Qed.

  Lemma venv_empty {Sigma : Signature} (I : interp D) rho phi :
    rho ⊨ phi <-> (venv Vector.nil rho) ⊨ phi.
  Proof.
    apply sat_ext. now intros [].
  Qed.

  Definition subs_interp (I : @interp (sig_ext (B_S F F_ar P P_ar)) D) (rho : nat -> D) : @interp (sig_ext (B_S F F_ar P P_ar)) D :=
    match I with B_I i_f i_P i_F => @B_I (sig_ext (B_S F F_ar P P_ar)) _
                                        (fun f => match f with inl f' => i_f (inl f') | inr n => fun _ => rho n end)
                                        i_P i_F
    end.

  Lemma subs_interp_eval (I : @interp (sig_ext (B_S F F_ar P P_ar)) D) rho xi n (v : Vector.t D n) t :
    @eval _ D I (venv v rho) (sig_lift_term' t) = @eval _ D (subs_interp I rho) (venv v xi) (subst_term (@pref (sig_ext (B_S F F_ar P P_ar)) n ext_c) (sig_lift_term' t)).
  Proof.
    destruct I. induction t using strong_term_ind; comp.
    - destruct (fin_minus x n) eqn:Hf; comp. 1: now rewrite Hf. destruct s. now comp.
    - f_equal. erewrite! vec_comp. 2,3,4: reflexivity. apply vec_map_ext, H.
  Qed.

  Lemma subs_interp_sat (I : @interp (sig_ext (B_S F F_ar P P_ar)) D) rho xi n (v : Vector.t D n) phi :
    @sat _ D I (venv v rho) (sig_lift' phi) <-> @sat _ D (subs_interp I rho) (venv v xi) (subst_form (@pref (sig_ext (B_S F F_ar P P_ar)) n ext_c) (sig_lift' phi)).
  Proof.
    destruct I. induction phi in n, v |-*. 1,2,3: comp.
    - tauto.
    - erewrite! vec_comp. 2,3,4: reflexivity. comp. erewrite vec_ext. 2: apply subs_interp_eval with (xi := xi). reflexivity.
    - intuition.
    - cbn. setoid_rewrite venv_sat. setoid_rewrite ext_form. 2: apply up_term_term_pref_ext_c'. now setoid_rewrite IHphi.
  Qed.

  Lemma subs_interp_sat' (I : @interp (sig_ext (B_S F F_ar P P_ar)) D) rho xi phi :
    @sat _ D I rho (sig_lift' phi) <-> @sat _ D (subs_interp I rho) xi (subst_form (ext_c' F_ar P_ar) (sig_lift' phi)).
  Proof.
    rewrite ext_form with (tauterm := pref 0 (ext_c' F_ar P_ar)). 2: now intros [].
    rewrite venv_empty. rewrite venv_empty with (rho0 := xi). apply subs_interp_sat.
  Qed.

  Lemma subs_eval (I : @interp (sig_ext (B_S F F_ar P P_ar)) D) rho n (v : Vector.t D n) t :
    eval (venv v (fun x => @i_f _ _ I (inr x) Vector.nil)) (sig_lift_term' t) = eval (venv v rho) (subst_term (@pref (sig_ext (B_S F F_ar P P_ar)) n ext_c) (sig_lift_term' t)).
  Proof.
    destruct I. induction t using strong_term_ind; comp.
    - destruct (fin_minus x n) eqn:Hf; comp. 1: now rewrite Hf. destruct s. now comp.
    - f_equal. erewrite! vec_comp. 2,3,4: reflexivity. apply vec_map_ext, H.
  Qed.

  Lemma subs_sat (I : @interp (sig_ext (B_S F F_ar P P_ar)) D) rho n (v : Vector.t D n) phi :
    sat (venv v (fun x => @i_f _ _ I (inr x) Vector.nil)) (sig_lift' phi) <-> sat (venv v rho) (subst_form (@pref (sig_ext (B_S F F_ar P P_ar)) n ext_c) (sig_lift' phi)).
  Proof.
    destruct I. induction phi in n, v |-*. 1,2,3: comp.
    - tauto.
    - erewrite! vec_comp. 2,3,4: reflexivity. comp. erewrite vec_ext. 2: apply subs_eval with (rho := rho). reflexivity.
    - intuition.
    - cbn. setoid_rewrite venv_sat. setoid_rewrite ext_form. 2: apply up_term_term_pref_ext_c'. now setoid_rewrite IHphi.
  Qed.

  Lemma subs_sat' (I : @interp (sig_ext (B_S F F_ar P P_ar)) D) rho phi :
    sat (fun x => @i_f _ _ I (inr x) Vector.nil) (sig_lift' phi) <-> sat rho (subst_form (ext_c' F_ar P_ar) (sig_lift' phi)).
  Proof.
    rewrite ext_form with (tauterm := pref 0 (ext_c' F_ar P_ar)). 2: now intros [].
    rewrite venv_empty. rewrite venv_empty with (rho0 := rho). apply subs_sat.
  Qed.
End SigExt.

Definition drop_interp {Sigma : Signature} D  : @interp (sig_ext Sigma) D -> @interp Sigma D :=
  match Sigma with B_S F F_ar P P_ar => fun I => drop_interp' I end.

Definition droppable (C : forall S D (I : @interp S D), Prop) := forall S D (I : @interp (sig_ext S) D), C _ _ I -> C _ _ (drop_interp I).

Lemma droppable_classical : droppable (@classical).
Proof.
  intros [] D [] Hc rho phi psi. apply drop_interp'_sat. comp. apply Hc.
Qed.

Lemma droppable_standard_bot : droppable (@standard_bot).
Proof.
  intros [] D [] Hs. apply Hs.
Qed.

Lemma droppable_exploding_bot : droppable (@exploding_bot).
Proof.
  intros [] D [] He rho phi Hf. now apply drop_interp'_sat, He.
Qed.

Lemma droppable_S : droppable (@SM).
Proof.
  intros [] D [] [? % droppable_classical ? % droppable_standard_bot]. now split.
Qed.

Lemma droppable_E : droppable (@EM).
Proof.
  intros [] D [] [? % droppable_classical ? % droppable_exploding_bot]. now split.
Qed.

Lemma droppable_BL : droppable (@BLM).
Proof. apply droppable_classical. Qed.

Section ClosingValidity.
  Context {Sigma : Signature}.
  Variable C : forall (S : Signature) D (I : @interp S D), Prop.
  Variable (T : theory) (phi : form).

  Hypothesis HC : droppable C.
  Hypothesis Hprv : valid_T (@C Sigma) T phi.

  Lemma sig_lift_subst_sat D (I : @interp (sig_ext Sigma) D) rho :
    C I -> exists (I' : @interp Sigma D) xi, C I' /\ forall psi, @sat _ _ I rho (subst_form (ext_c) (sig_lift psi)) <-> @sat _ _ I' xi psi.
  Proof.
    intros HI % HC. destruct Sigma. eexists. eexists. split. 1: exact HI.
    intros psi. unfold ext_c, sig_lift. rewrite <- subs_sat', drop_interp'_sat.
    reflexivity.
  Qed.

  Lemma sig_lift_subst_valid : valid_T (@C (sig_ext Sigma)) (tmap (fun psi => (sig_lift psi)[ext_c]) T) ((sig_lift phi)[ext_c]).
  Proof.
    intros D I HI rho HT. destruct (sig_lift_subst_sat rho HI) as (I' & xi & HC' & HI'). apply HI'.
    apply Hprv. 1: exact HC'. intros psi Hpsi. apply HI', HT. now exists psi.
  Qed.
End ClosingValidity.

(** **** Closing and Big Implication **)

Section ClosingBigImp.
  Context {Sigma : Signature}.

  Lemma valid_L_valid_T C A phi :
    valid_L C A phi <-> valid_T C (list_T A) phi.
  Proof.
    firstorder.
  Qed.

  Lemma big_imp_valid_L C A B phi :
    valid_L C (rev A ++ B) phi -> valid_L C B (A ⟹ phi).
  Proof.
    intros HL. induction A in B, HL |-*.
    - apply HL.
    - intros D I HI rho HB Ha. apply IHA with (B := a :: B). 2: assumption.
      2: intros ? []; subst; intuition. comp. now rewrite <- app_assoc in HL.
  Qed.

  Lemma close_valid_L C phi :
    valid_L C nil phi -> valid_L C nil (close phi).
  Proof.
    intros Hval. unfold close. destruct (find_unused phi) as [n Hn]; comp.
    intros D I HI rho _. clear Hn; induction n in rho |-*.
    - apply Hval; intuition.
    - intros d. apply IHn.
  Qed.

  Lemma valid_L_to_single C A phi :
    valid_L C A phi -> valid_L C nil (close (A ⟹ phi)).
  Proof.
    intros H. apply close_valid_L, big_imp_valid_L.
    intros D I HI rho HL. apply H. 1: assumption.
    rewrite app_nil_r in HL. intros ? ? % in_rev. auto.
  Qed.
End ClosingBigImp.
