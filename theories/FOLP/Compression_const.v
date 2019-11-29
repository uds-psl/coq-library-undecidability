(** ** Signature Compression *)

Require Import Equations.Equations Fin.
From Undecidability.FOLP Require Export FullTarski.



(* Prelim (to be moved) *)

Lemma cast_refl X n (v : vector X n) :
  cast v eq_refl = v.
Proof.
  induction v; cbn; congruence.
Qed.

Lemma forall_proper X (p q : X -> Prop) :
  (forall x, p x <-> q x) -> (forall x, p x) <-> (forall x, q x).
Proof.
  firstorder.
Qed.

Lemma exists_proper X (p q : X -> Prop) :
  (forall x, p x <-> q x) -> (exists x, p x) <-> (exists x, q x).
Proof.
  firstorder.
Qed.



(* Satisfiability (not yet classical) *)

Definition SAT Sigma (phi : @form Sigma) :=
  exists D (I : @interp Sigma D) rho, rho ⊨ phi.



(* STEP 1: compression into a single relation symbol *)

Section Compression.

  Context { Sigma : Signature }.

  (* Input: signature only containing relations of a fixed arity *)

  Variable arity : nat.
  Hypothesis arity_const : forall P, pred_ar P = arity.
  Hypothesis funcs_empty : Funcs -> False.

  (* Output: signature with constants for each relation and a single relation *)

  Definition compress_sig :=
    {| Funcs := Preds;
       fun_ar := fun _ => 0;
       Preds := unit;
       pred_ar := fun _ => S arity |}.

  (* Conversion: each atom P_i(x, y, ...) is replaced by P (i, x, y, ...) *)

  Fixpoint convert_t (t : @term Sigma) : @term compress_sig :=
    match t with
    | var_term s => var_term s
    | Func f v => False_rect _ (funcs_empty f)
    end.

  Definition convert_v n (v : vector term n) :=
    Vector.map convert_t v.
  
  Definition encode_v P (v : vector term (pred_ar P)) :=
    Vector.cons (@Func compress_sig P Vector.nil) (cast (convert_v v) (arity_const P)).

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

  (* Direction 1: sat phi -> sat (encode phi) *)

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
      - intros P v. right. exact P.
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
      destruct t as [x | f v]; trivial.
      exfalso. apply (funcs_empty f).
    Qed.

    Definition env_fill (rho : nat -> D + Preds) : nat -> D + Preds :=
      fun n => match (rho n) with inl d => inl d | inr P => inl d0 end.

    Lemma env_fill_sat_help rho phi x :
      env_fill (x .: env_fill rho) ⊨ encode phi <-> env_fill (x .: rho) ⊨ encode phi.
    Proof.
      apply sat_ext. intros []; try reflexivity. unfold env_fill; cbn. now destruct (rho n).
    Qed.

    Lemma env_fill_sat rho phi :
      sat (env_fill rho) (encode phi) <-> sat rho (encode phi).
    Proof.
      induction phi in rho |- *. 1, 3, 4, 5: firstorder.
      - cbn. rewrite <- (arity_const P), !cast_refl.
        replace (vec_fill (Vector.map (eval (env_fill rho)) (convert_v t)))
                with (vec_fill (Vector.map (eval rho) (convert_v t))); try reflexivity.
        induction t; cbn; trivial. rewrite IHt. destruct h as [x | f v]; cbn. 
        + unfold env_fill. now destruct rho.
        + exfalso. apply (funcs_empty f).
      - cbn. apply forall_proper. intros x.
        rewrite <- IHphi, env_fill_sat_help.
        now setoid_rewrite <- IHphi at 2.
      - cbn. apply exists_proper. intros x.
        rewrite <- IHphi, env_fill_sat_help.
        now setoid_rewrite <- IHphi at 2.
    Qed.

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

  (* Direction 2: sat (encode phi) -> sat phi *)

  Section from_compr.

    Context { D : Type }.
    Context { I : @interp compress_sig D }.

    Notation index P := (@i_f _ _ I P Vector.nil).

    Local Instance uncompr_interp :
      @interp Sigma D.
    Proof.
      split.
      - intros f v. exfalso. apply (funcs_empty f).
      - intros P v. exact (@i_P _ _ I tt (Vector.cons (index P) (cast v (arity_const P)))).
    Defined.

    Lemma eval_from_compr (rho : nat -> D) (t : @term Sigma) :
      eval rho t = eval rho (convert_t t).
    Proof.
      destruct t as [x | f v]; trivial.
      exfalso. apply (funcs_empty f).
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

  (* Reduction 1 *)

  Theorem sat_compr (phi : @form Sigma) :
    SAT phi <-> SAT (encode phi).
  Proof.
    split; intros (D & I & rho & H).
    - exists _, (compr_interp (rho 0)), (convert_env rho). now apply sat_to_compr.
    - exists _, uncompr_interp, rho. now apply sat_from_compr.
  Qed.

End Compression.



(* STEP 2: simulation of constants with free variables *)

Section Constants.

  Context { Sigma : Signature } {HdF : eq_dec Funcs}.

  (* Simulation of a single constant *)

  Section Rpl.

    Context { D : Type } { I : @interp Sigma D }.
    Variable c : Funcs.
    Hypothesis Hc : 0 = fun_ar c.

    Fixpoint rpl_const_t n t :=
      match t with 
      | var_term x => var_term x
      | Func f v => if Dec (f = c) then var_term n else Func f (Vector.map (rpl_const_t n) v)
      end.

    Definition update (rho : nat -> D) n d : nat -> D :=
      fun k => if Dec (k = n) then d else rho k.

    Definition i_const rho : D :=
      eval rho (@Func _ c (match Hc with eq_refl => Vector.nil end)).

    Lemma i_const_inv rho rho' :
      i_const rho = i_const rho'.
    Proof.
      cbn. erewrite vec_map_ext; try reflexivity.
      intros t. destruct Hc. inversion 1.
    Qed.

    Lemma i_const_eq rho v :
      i_const rho = eval rho (@Func _ c v).
    Proof.
      cbn. f_equal. destruct Hc. now depelim v.
    Qed.

    Lemma rpl_const_eval t n rho :
      unused_term n t -> eval (update rho n (i_const rho)) (rpl_const_t n t) = eval rho t.
    Proof.
      induction 1; cbn -[i_const].
      - unfold update. decide _; congruence.
      - decide _; cbn -[i_const].
        + subst. unfold update. decide (n = n); try tauto. apply i_const_eq. 
        + f_equal. erewrite vec_comp. apply vec_map_ext, H0. reflexivity.
    Qed.

    Fixpoint rpl_const n phi :=
      match phi with 
      | Pred P v => Pred P (Vector.map (rpl_const_t n) v)
      | Fal => Fal
      | Impl phi psi => Impl (rpl_const n phi) (rpl_const n psi)
      | Conj phi psi => Conj (rpl_const n phi) (rpl_const n psi)
      | Disj phi psi => Disj (rpl_const n phi) (rpl_const n psi)
      | Ex phi => Ex (rpl_const (S n) phi)
      | All phi => All (rpl_const (S n) phi)
      end.

    Lemma update_S phi n rho d d' :
      (d .: update rho n d') ⊨ phi <-> update (d .: rho) (S n) d' ⊨ phi.
    Proof.
      apply sat_ext. intros []; cbn -[i_const]; trivial.
      unfold update. repeat destruct _; try lia; trivial.
    Qed.

    Lemma rpl_const_sat phi n rho :
      unused n phi -> sat (update rho n (i_const rho)) (rpl_const n phi) <-> sat rho phi.
    Proof.
      induction 1 in rho |- *. 1, 3, 4, 5: firstorder.
      - cbn -[i_const]. symmetry. erewrite vec_map_ext. erewrite vec_comp; reflexivity.
        intros x Hx. symmetry. now apply rpl_const_eval, H.
      - cbn -[i_const]. apply forall_proper. intros d.
        erewrite <- IHunused, i_const_inv. apply update_S.
      - cbn -[i_const]. apply exists_proper. intros d.
        erewrite <- IHunused, i_const_inv. apply update_S.
    Qed.

    Definition rpl_const_t' t :=
      rpl_const_t (proj1_sig (find_unused_term t)) t.

    Definition rpl_const' phi :=
      rpl_const (proj1_sig (find_unused phi)) phi.
    
    Definition rpl_const_env rho phi :=
      update rho (proj1_sig (find_unused phi)) (i_const rho).

    Lemma rpl_const_sat' phi rho :
      sat (rpl_const_env rho phi) (rpl_const' phi) <-> sat rho phi.
    Proof.
      apply rpl_const_sat. destruct find_unused; cbn. now apply u.
    Qed.

    Inductive unused_f_term : term -> Prop :=
    | unused_f_var m : unused_f_term (var_term m)
    | unused_f_Func f v : f <> c -> unused_f_term (Func f v).

    Inductive unused_f : form -> Prop :=
    | unused_f_Fal : unused_f Fal
    | unused_f_Pred P v : (forall t, vec_in t v -> unused_f_term t) -> unused_f (Pred P v)
    | unused_f_I phi psi : unused_f phi -> unused_f psi -> unused_f (Impl phi psi)
    | unused_f_A phi psi : unused_f phi -> unused_f psi -> unused_f (Conj phi psi)
    | unused_f_O phi psi : unused_f phi -> unused_f psi -> unused_f (Disj phi psi)
    | unused_f_All phi : unused_f phi -> unused_f (All phi)
    | unused_f_Ex phi : unused_f phi -> unused_f (Ex phi).

    Lemma unused_rpl_t t n :
      unused_f_term (rpl_const_t n t).
    Proof.
      induction t; cbn; try constructor.
      decide _; now constructor.
    Qed.

    Lemma unused_rpl_t' t :
      unused_f_term (rpl_const_t' t).
    Proof.
      apply unused_rpl_t.
    Qed.

    Lemma vec_map_in X Y (f : X -> Y) n (v : vector X n) y :
      vec_in y (Vector.map f v) -> { x & ((vec_in x v) * (y = f x))%type }.
    Proof.
      induction v; cbn; inversion 1; subst.
      
    Admitted.

    Lemma unused_rpl phi n :
      unused_f (rpl_const n phi).
    Proof.
      induction phi in n |- *; cbn; constructor; trivial.
      intros t1 [t' [H ->]] % vec_map_in. apply unused_rpl_t.
    Qed.

    Lemma unused_rpl' phi :
      unused_f (rpl_const' phi).
    Proof.
      apply unused_rpl.
    Qed.

  End Rpl.

  (* Simulation of a list of constants *)

  Section RplList.

    Context { D : Type } { I : @interp Sigma D }.

    Fixpoint rpl_list L phi :=
      match L with
      | nil => phi
      | c::L => rpl_const' c (rpl_list L phi)
      end.

    Lemma unused_rpl_mono phi f g :
      unused_f f phi -> unused_f f (rpl_const' g phi).
    Proof.
    Admitted.

    Lemma unused_rpl_list (L : list Funcs) (HL : forall c, c el L -> 0 = fun_ar c) phi :
      forall f, f el L -> unused_f f (rpl_list L phi).
    Proof.
      induction L; intuition; subst; cbn.
      destruct H as [->|H].
      - apply unused_rpl'. now apply HL.
      - apply unused_rpl_mono. apply IHL; auto.
    Qed.

    Definition rpl_list_all L (HL : forall c, c el L -> 0 = fun_ar c) phi rho :
      { phi' : form & { rho' : nat -> D | rho' ⊨ phi' <-> rho ⊨ phi } }.
    Proof.
      induction L.
      - exists phi, rho. reflexivity.
      - destruct IHL as (phi' & rho' & H); auto.
        assert (Ha : a el a::L) by now left.
        exists (rpl_const' a phi'), (rpl_const_env (HL a Ha) rho' phi').
        rewrite <- H. apply rpl_const_sat'.
    Defined.

    Definition rpl_list' L (HL : forall c, c el L -> 0 = fun_ar c) phi rho :=
      projT1 (rpl_list_all HL phi rho).

    Definition rpl_list_env L (HL : forall c, c el L -> 0 = fun_ar c) phi rho :=
      proj1_sig (projT2 (rpl_list_all HL phi rho)).

  End RplList.

  (* Hence constants can be erased from the signature *)

  Hypothesis HS : forall f, 0 = fun_ar f.

  Definition const_sig :=
    {| Funcs := False;
       fun_ar := fun _ => 0;
       Preds := Preds;
       pred_ar := pred_ar |}.

  Fixpoint collect_funcs_t t : list Funcs :=
    match t with 
    | var_term x => nil
    | Func f v => f :: concat (to_list (Vector.map collect_funcs_t v))
    end.

  Fixpoint collect_funcs phi : list Funcs :=
    match phi with 
      | Pred P v => concat (to_list (Vector.map collect_funcs_t v))
      | Fal => nil
      | Impl phi psi => (collect_funcs phi) ++ (collect_funcs psi)
      | Conj phi psi => (collect_funcs phi) ++ (collect_funcs psi)
      | Disj phi psi => (collect_funcs phi) ++ (collect_funcs psi)
      | Ex phi => collect_funcs phi
      | All phi => collect_funcs phi
      end.
  
  Inductive pure_t : term -> Type :=
  | pure_var n : pure_t (var_term n).

  Inductive pure : form -> Type :=
  | pure_P P v : (forall t, vec_in t v -> pure_t t) -> pure (Pred P v)
  | pure_I phi psi : pure phi -> pure psi -> pure (Impl phi psi)
  | pure_A phi psi : pure phi -> pure psi -> pure (Conj phi psi)
  | pure_O phi psi : pure phi -> pure psi -> pure (Disj phi psi)
  | pure_All phi : pure phi -> pure (All phi)
  | pure_Ex phi : pure phi -> pure (Ex phi).

  Definition erase_funcs_t (t : @term Sigma) :
    pure_t t -> @term const_sig.
  Proof.
    destruct 1. exact (var_term 1).
  Defined.

  Definition erase_funcs_v n (v : vector (@term Sigma) n) :
    (forall t : term, vec_in t v -> pure_t t) -> vector (@term const_sig) n.
  Proof.
    intros H. induction v.
    - exact Vector.nil.
    - apply Vector.cons.
      + apply (@erase_funcs_t h). apply H. now left.
      + apply IHv. auto.
  Defined.

  Definition erase_funcs (phi : @form Sigma) :
    pure phi -> @form const_sig.
  Proof.
    induction 1.
    - exact (@Pred const_sig P (erase_funcs_v p)).
    - exact (Impl IHX1 IHX2).
    - exact (Conj IHX1 IHX2).
    - exact (Disj IHX1 IHX2).
    - exact (All IHX).
    - exact (Ex IHX).
  Defined.

  Lemma pure_repl phi :
    pure (rpl_list (collect_funcs phi) phi).
  Proof.
    
  Admitted.

  Definition encode_const phi :=
    erase_funcs (pure_repl phi).

  Theorem sat_const (phi : @form Sigma) :
    SAT phi <-> SAT (encode_const phi).
  Proof.
    split; intros (D & I & rho & H).
    - exists D, I.

End Constants.
  
