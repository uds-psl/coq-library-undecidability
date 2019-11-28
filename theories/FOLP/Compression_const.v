(** ** Signature Compression *)

Require Import Equations.Equations Fin.
From Undecidability.FOLP Require Export FullTarski.

Section Compression.

  Context { Sigma : Signature }.

  Notation fin := Fin.t.

  Variable arity : nat.
  Hypothesis arity_const : forall P, pred_ar P = arity.

  Definition compress_sig :=
    {| Funcs := Funcs + Preds;
       fun_ar := fun f => match f with inl f => fun_ar f | _ => 0 end;
       Preds := unit;
       pred_ar := fun _ => S arity |}.

  Fixpoint convert_t (t : @term Sigma) : @term compress_sig :=
    match t with
    | var_term s => var_term s
    | Func f v => @Func compress_sig (inl f) (Vector.map convert_t v)
    end.

  Definition convert_v n (v : vector term n) :=
    Vector.map convert_t v.
  
  Definition encode_v P (v : vector term (pred_ar P)) :=
    Vector.cons (@Func compress_sig (inr P) Vector.nil) (cast (convert_v v) (arity_const P)).

  Fixpoint encode (phi : @form Sigma) : @form compress_sig :=
    match phi with
    | Pred P v => @Pred compress_sig tt (encode_v v)
    | Fal => Fal
    | Impl phi psi => Impl (encode phi) (encode psi)
    | Conj phi psi => Conj (encode phi) (encode psi)
    | Disj phi psi => Disj (encode phi) (encode psi)
    | Ex phi => Ex (encode phi)
    | All phi => All (encode phi)
    end.

  


  Section to_compr.

    Context { D : Type }.
    Context { I : @interp Sigma D }.
    Variable d0 : D.

    Fixpoint vec_fill n (v : vector (D + Preds) n) : vector D n :=
      match v with
      | Vector.nil => Vector.nil
      | Vector.cons (inl x) v => Vector.cons x (vec_fill v)
      | Vector.cons (inr P) v => Vector.cons d0 (vec_fill v)
      end.

    Lemma vec_fill_inl n (v : vector D n) :
      vec_fill (Vector.map inl v) = v.
    Proof.
      induction v; cbn; congruence.
    Qed.

    Local Instance compr_interp :
      @interp compress_sig (D + Preds).
    Proof.
      split.
      - intros [f|P] v.
        + left. exact (@i_f _ _ I f (vec_fill v)).
        + right. exact P.
      - intros [] v; cbn in *.
        destruct (Vector.hd v) as [d|P].
        + exact True.
        + exact (@i_P _ _ I P (cast (vec_fill (Vector.tl v)) (eq_sym (arity_const P)))).
    Defined.

    Definition convert_env (rho : nat -> D) : nat -> D + Preds :=
      fun n => inl (rho n).

    Lemma eval_to_compr (rho : nat -> D) t :
      inl (eval rho t) = eval (convert_env rho) (convert_t t).
    Proof.
      induction t using strong_term_ind; cbn; trivial. repeat f_equal.
      induction v; cbn; trivial. rewrite <- H, IHv; intuition.
    Qed.

    Lemma cast_refl X n (v : vector X n) :
      cast v eq_refl = v.
    Proof.
      induction v; cbn; congruence.
    Qed.

    Definition env_fill (rho : nat -> D + Preds) : nat -> D + Preds :=
      fun n => match (rho n) with inl d => inl d | inr P => inl d0 end.

    Lemma env_fill_eval rho t :
      eval (env_fill rho) (convert_t t) = eval rho (convert_t t).
    Proof.
      induction t using strong_term_ind; cbn; trivial.
    Abort.

    Lemma env_fill_sat rho phi :
      sat (env_fill rho) phi <-> sat rho phi.
    Proof.
      induction phi in rho |- *; try tauto.
      - destruct P. cbn. admit.
      - firstorder.
      - firstorder.
      - firstorder.
      - split; intros H d.
        + apply IHphi. destruct d; eapply sat_ext; try apply H; now destruct x.
        + apply IHphi. destruct d; eapply sat_ext; try apply IHphi, H; destruct x; try reflexivity.
          all: unfold env_fill; cbn; now destruct (rho x).
      - split; intros [d H].
        + exists d. apply IHphi. apply IHphi in H. destruct d; eapply sat_ext; try apply H; destruct x; try reflexivity.
          all: unfold env_fill; cbn; now destruct (rho x).
        + exists d. apply IHphi. apply IHphi in H. destruct d; eapply sat_ext; try apply H; destruct x; try reflexivity.
          all: unfold env_fill; cbn; now destruct (rho x).
    Admitted.

    Lemma env_fill_sat' rho phi :
      sat (env_fill rho) (encode phi) <-> sat rho (encode phi).
    Proof.
      induction phi in rho |- *; try tauto.
      - cbn. rewrite <- (arity_const P), !cast_refl.
        replace (vec_fill (Vector.map (eval (env_fill rho)) (convert_v t)))
                with (vec_fill (Vector.map (eval rho) (convert_v t))); try reflexivity.
        induction t; cbn; trivial. rewrite IHt. destruct h; cbn. 
        + unfold env_fill. now destruct rho.
        
      - firstorder.
      - firstorder.
      - firstorder.
      - split; intros H d.
        + apply IHphi. destruct d; eapply sat_ext; try apply H; now destruct x.
        + apply IHphi. destruct d; eapply sat_ext; try apply IHphi, H; destruct x; try reflexivity.
          all: unfold env_fill; cbn; now destruct (rho x).
      - split; intros [d H].
        + exists d. apply IHphi. apply IHphi in H. destruct d; eapply sat_ext; try apply H; destruct x; try reflexivity.
          all: unfold env_fill; cbn; now destruct (rho x).
        + exists d. apply IHphi. apply IHphi in H. destruct d; eapply sat_ext; try apply H; destruct x; try reflexivity.
          all: unfold env_fill; cbn; now destruct (rho x).
    Admitted.

    Lemma sat_to_compr (rho : nat -> D) phi :
      sat rho phi <-> sat (convert_env rho) (encode phi).
    Proof.
      induction phi in rho |- *; cbn; try firstorder tauto.
      - rewrite <- (arity_const P), !cast_refl.
        unfold convert_v. erewrite vec_comp; try reflexivity.
        rewrite <- (vec_fill_inl (Vector.map (eval rho) t)).
        erewrite vec_comp; try reflexivity. apply eval_to_compr.
      - split; intros H d.
        + destruct d as [d|P].
          * eapply sat_ext; try apply IHphi, (H d). now intros [].
          * specialize (H d0). apply IHphi in H. apply env_fill_sat.
            eapply sat_ext; try apply H. now intros [].
        + apply IHphi. eapply sat_ext; try apply (H (inl d)). now intros [].
      - split; intros [d H].
        + exists (inl d). apply IHphi in H. eapply sat_ext, H. now intros [].
        + destruct d as [d|P].
          * exists d. apply IHphi. eapply sat_ext; try apply H. now intros [].
          * exists d0. apply IHphi. apply env_fill_sat in H.
            eapply sat_ext; try apply H. now intros [].
    Qed.

  End to_compr.

  Section from_compr.

    Context { D : Type }.
    Context { I : @interp compress_sig D }.

    Notation index P := (@i_f _ _ I (inr P) Vector.nil).

    Local Instance uncompr_interp :
      @interp Sigma D.
    Proof.
      split.
      - intros f v. exact (@i_f _ _ I (inl f) v).
      - intros P v. exact (@i_P _ _ I tt (Vector.cons (index P) (cast v (arity_const P)))).
    Defined.

    Lemma eval_from_compr (rho : nat -> D) t :
      eval rho t = eval rho (convert_t t).
    Proof.
      induction t using strong_term_ind; cbn; trivial.
      f_equal. erewrite vec_comp. apply vec_map_ext. apply H. reflexivity.
    Qed.

    Lemma sat_from_compr (rho : nat -> D) phi :
      sat rho phi <-> sat rho (encode phi).
    Proof.
      induction phi in rho |- *; cbn; try firstorder tauto.
      replace (cast (Vector.map (eval rho) t) (arity_const P))
        with (Vector.map (eval rho) (cast (convert_v t) (arity_const P))); try reflexivity.
      rewrite <- (arity_const P) in *. rewrite !cast_refl.
      apply vec_comp. intros t'. now rewrite eval_from_compr.
    Qed.

  End from_compr.

End Compression.
