From Undecidability.Shared.Libs.PSL Require Import Vectors VectorForall.
Require Import Undecidability.SOL.SOL.
From Undecidability.SOL.Util Require Import Subst Syntax.
Require Import Arith Lia Vector.

From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
Derive Signature for Vector.t.

Import SubstNotations.
Unset Implicit Arguments.

Set Default Proof Using "Type".

Arguments eval_function {_ _ _ _ _}.
Arguments eval_predicate {_ _ _ _ _}.
Arguments eval {_ _ _ _}.
Arguments sat {_ _ _ _}.
Arguments new_env {_} _ _ _.
Arguments get_indi {_} _ _.
Arguments get_func {_} _ _.
Arguments get_pred {_} _ _.

Notation "⟨ a , b , c ⟩" := (new_env a b c).

(* Type class for ⊨ notations *)
Class Ent X Y `{funcs_signature, preds_signature} := ent : X -> Y -> Prop.
Notation "X ⊨ phi" := (ent X phi) (at level 20).
Class Ent' X `{funcs_signature, preds_signature} := ent' : forall M : Model, env (M_domain M) -> X -> Prop.
Notation "( M , rho ) ⊨ phi" := (ent' M rho phi) (at level 0).

#[global] Instance ent_env `{funcs_signature, preds_signature} domain I : Ent (env domain) form := 
  @sat _ _ domain I.
#[global] Instance ent'_form `{funcs_signature, preds_signature} : Ent' form :=
  fun M rho phi => @sat _ _ (M_domain M) (M_interp M) rho phi.
#[global] Instance ent_model `{funcs_signature, preds_signature} : Ent Model form := 
  fun M phi => forall rho, @sat _ _ (M_domain M) (M_interp M) rho phi.
#[global] Instance ent_model_theory `{funcs_signature, preds_signature} : Ent Model (form -> Prop) := 
  fun M T => forall phi, T phi -> M ⊨ phi.
#[global] Instance ent_theory `{funcs_signature, preds_signature} : Ent (form -> Prop) form := 
  fun T phi => forall (M : Model) rho, (forall psi, T psi -> (M, rho) ⊨ psi) -> (M, rho) ⊨ phi.
#[global] Instance ent'_theory `{funcs_signature, preds_signature} : Ent' (form -> Prop) :=
  fun M rho T => forall phi, T phi -> (M, rho) ⊨ phi.
#[global] Instance ent'_form' `{funcs_signature, preds_signature} : Ent' form :=
  fun M rho phi => @sat _ _ (M_domain M) (M_interp M) rho phi.


Section Environment.

  Variable domain : Type.

  Definition env_equiv (rho1 : env domain) rho2 := forall n,
        get_indi rho1 n = get_indi rho2 n
    /\ forall ar v, get_func rho1 n ar v = get_func rho2 n ar v
                /\ (get_pred rho1 n ar v <-> get_pred rho2 n ar v).
  Notation "rho1 ≡ rho2" := (env_equiv rho1 rho2) (at level 30).

  Lemma env_equiv_symm rho1 rho2 :
    rho1 ≡ rho2 -> rho2 ≡ rho1.
  Proof.
    intros H. intros n. specialize (H n). split. easy. 
    intros ar v. destruct H as [_ H]. specialize (H ar v). easy.
  Qed.

  Lemma env_equiv_cons_i rho1 rho2 x :
  rho1 ≡ rho2 -> ⟨ x .: get_indi rho1, get_func rho1, get_pred rho1 ⟩ ≡ ⟨ x .: get_indi rho2, get_func rho2, get_pred rho2 ⟩.
  Proof.
    intros H n. split. 2:split. destruct n. all: firstorder.
  Qed.

  Lemma env_equiv_cons_f rho1 rho2 ar (f : vec domain ar -> domain) f' :
    rho1 ≡ rho2 -> (forall v, f v = f' v) 
    -> ⟨ get_indi rho1, f .: get_func rho1, get_pred rho1 ⟩ ≡ ⟨ get_indi rho2, f' .: get_func rho2, get_pred rho2 ⟩.
  Proof.
    intros H Hf n. split. 2:split.
    - apply H.
    - destruct n; cbn; destruct (Nat.eq_dec ar ar0) as [->|]; firstorder.
    - apply H.
  Qed.

  Lemma env_equiv_cons_p rho1 rho2 ar (P : vec domain ar -> Prop) :
    rho1 ≡ rho2 -> ⟨ get_indi rho1, get_func rho1, P .: get_pred rho1 ⟩ ≡ ⟨ get_indi rho2, get_func rho2, P .: get_pred rho2 ⟩.
  Proof.
    intros H n. split. 2:split.
    - apply H.
    - apply H.
    - destruct n; cbn; destruct (Nat.eq_dec ar ar0) as [->|]. all: firstorder.
  Qed.

End Environment.

Notation "rho1 ≡ rho2" := (env_equiv _ rho1 rho2) (at level 30).



Section SatExt.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Variable domain : Type.
  Context {I : interp domain}.

  Lemma eval_function_ext rho1 rho2 ar (f : function ar) :
    (forall n ar v, get_func rho1 n ar v = get_func rho2 n ar v)
      -> forall v, eval_function rho1 f v = eval_function rho2 f v.
  Proof.
    intros H v. destruct f; cbn. apply H. reflexivity.
  Qed.

  Lemma eval_predicate_ext rho1 rho2 ar (P : predicate ar) :
    (forall n ar v, get_pred rho1 n ar v <-> get_pred rho2 n ar v)
      -> forall v, eval_predicate rho1 P v <-> eval_predicate rho2 P v.
  Proof.
    intros H v. destruct P; cbn. apply H. reflexivity.
  Qed.

  Lemma eval_ext rho1 rho2 t :
    (forall n, get_indi rho1 n = get_indi rho2 n) 
    -> (forall n ar v, get_func rho1 n ar v = get_func rho2 n ar v)
    -> eval rho1 t = eval rho2 t.
  Proof.
    intros H1 H2. induction t.
    - apply H1.
    - cbn. enough (map (eval rho1) v = map (eval rho2) v) as -> by apply H2.
      now apply map_ext_forall.
    - cbn. f_equal. now apply map_ext_forall.
  Qed.

  Lemma sat_ext rho1 rho2 phi :
    rho1 ≡ rho2 -> sat rho1 phi <-> sat rho2 phi.
  Proof.
    revert rho1 rho2. induction phi; cbn; intros rho1 rho2 H.
    - easy.
    - destruct p. 
      + rename t into v. enough (map (eval rho1) v = map (eval rho2) v) as <- by apply H.
        apply map_ext. induction v; firstorder. apply eval_ext; apply H.
      + rename t into v. enough (map (eval rho1) v = map (eval rho2) v) as <- by easy.
        apply map_ext. induction v; firstorder. apply eval_ext; apply H.
    - specialize (IHphi1 rho1 rho2); specialize (IHphi2 rho1 rho2).
      destruct b; cbn; firstorder.
    - destruct q; split; cbn.
      + intros H1 x. eapply IHphi. 2: apply H1. now apply env_equiv_symm, env_equiv_cons_i.
      + intros H1 x. eapply IHphi. 2: apply H1. now apply env_equiv_cons_i.
      + intros [d H1]. exists d. eapply IHphi. 2: apply H1. now apply env_equiv_symm, env_equiv_cons_i.
      + intros [d H1]. exists d. eapply IHphi. 2: apply H1. now apply env_equiv_cons_i.
    - destruct q; split; cbn.
      + intros H1 f. eapply IHphi. 2: apply H1. now apply env_equiv_symm, env_equiv_cons_f.
      + intros H1 f. eapply IHphi. 2: apply H1. now apply env_equiv_cons_f.
      + intros [f H1]. exists f. eapply IHphi. 2: apply H1. now apply env_equiv_symm, env_equiv_cons_f.
      + intros [f H1]. exists f. eapply IHphi. 2: apply H1. now apply env_equiv_cons_f.
    - destruct q; split; cbn.
      + intros H1 P. eapply IHphi. 2: apply H1. now apply env_equiv_symm, env_equiv_cons_p.
      + intros H1 P. eapply IHphi. 2: apply H1. now apply env_equiv_cons_p.
      + intros [P H1]. exists P. eapply IHphi. 2: apply H1. now apply env_equiv_symm, env_equiv_cons_p.
      + intros [P H1]. exists P. eapply IHphi. 2: apply H1. now apply env_equiv_cons_p.
  Qed.

End SatExt.



Section BoundedSat.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Variable domain : Type.
  Context {I : interp domain}.

  Lemma sat_ext_bounded_term t rho sigma :
    (forall x, ~ bounded_indi_term x t -> get_indi rho x = get_indi sigma x)
    -> (forall x ar, ~ bounded_func_term ar x t -> get_func rho x ar = get_func sigma x ar)
    -> eval rho t = eval sigma t.
  Proof.
    intros H1 H2. induction t; cbn.
    - apply H1. cbn. lia.
    - rewrite H2. f_equal. apply map_ext_in. intros t H. eapply Forall_in in IH.
      apply IH. intros x H3. apply H1. cbn. intros H4. apply H3. eapply Forall_in in H4. 
      apply H4. trivial. intros x ar' H3. apply H2. cbn. intros [H4 H5]. apply H3. eapply Forall_in in H5.
      apply H5. easy. easy. cbn. lia.
    - f_equal. apply map_ext_in. intros t H. eapply Forall_in in IH.
      apply IH. intros x H3. apply H1. cbn. intros H4. apply H3. eapply Forall_in in H4. 
      apply H4. trivial. intros x ar' H3. apply H2. cbn. intros H4. apply H3. eapply Forall_in in H4.
      apply H4. easy. easy.
  Qed.

  Lemma sat_ext_bounded phi rho sigma :
    (forall x, ~ bounded_indi x phi -> get_indi rho x = get_indi sigma x)
    -> (forall x ar, ~ bounded_func ar x phi -> get_func rho x ar = get_func sigma x ar)
    -> (forall x ar, ~ bounded_pred ar x phi -> get_pred rho x ar = get_pred sigma x ar)
    -> sat rho phi <-> sat sigma phi.
  Proof.
    revert rho sigma. induction phi; cbn; intros rho sigma H1 H2 H3.
    - reflexivity.
    - erewrite map_ext_in with (g := eval sigma); revgoals.
      intros ? H. apply sat_ext_bounded_term. intros x H4. apply H1. intros H5. apply H4.
      eapply Forall_in in H5. apply H5. easy. intros x ar' H4. apply H2. intros H5. apply H4.
      eapply Forall_in in H5. apply H5. easy. destruct p; cbn.
      + rewrite H3. reflexivity. cbn. lia.
      + reflexivity.
    - specialize (IHphi1 rho sigma). specialize (IHphi2 rho sigma).
      destruct b; cbn; setoid_rewrite IHphi1; try setoid_rewrite IHphi2; try reflexivity; clear IHphi1 IHphi2; firstorder.
    - destruct q; split.
      + intros H d. eapply IHphi. 4: apply (H d). intros []. all: firstorder.
      + intros H d. eapply IHphi. 4: apply (H d). intros []. all: firstorder.
      + intros [d H]. exists d. eapply IHphi. 4: apply H. intros []. all: firstorder.
      + intros [d H]. exists d. eapply IHphi. 4: apply H. intros []. all: firstorder.
    - destruct q; split.
      + intros H f. eapply IHphi. 4: eapply (H f); trivial. 2: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
      + intros H f. eapply IHphi. 4: eapply (H f); trivial. 2: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
      + intros [f H]. exists f. eapply IHphi. 4: eapply H; trivial. 2: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
      + intros [f H]. exists f. eapply IHphi. 4: eapply H; trivial. 2: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
    - destruct q; split.
      + intros H P. eapply IHphi. 4: eapply (H P); trivial. 3: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
      + intros H P. eapply IHphi. 4: eapply (H P); trivial. 3: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
      + intros [P H]. exists P. eapply IHphi. 4: eapply H; trivial. 3: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
      + intros [P H]. exists P. eapply IHphi. 4: eapply H; trivial. 3: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
  Qed.

  Lemma sat_ext_closed phi rho sigma :
    bounded_indi 0 phi -> (forall ar, bounded_func ar 0 phi) -> (forall ar, bounded_pred ar 0 phi) 
    -> (sat rho phi <-> sat sigma phi).
  Proof.
    intros Bi Bf Bp. apply sat_ext_bounded.
    - intros x H. exfalso. apply H. eapply bounded_indi_up. 2: apply Bi. lia.
    - intros x ar H. exfalso. apply H. eapply bounded_func_up. 2: apply Bf. lia.
    - intros x ar H. exfalso. apply H. eapply bounded_pred_up. 2: apply Bp. lia.
  Qed.

  Lemma sat_ext_closed_funcfree phi rho sigma :
    funcfree phi -> bounded_indi 0 phi -> (forall ar, bounded_pred ar 0 phi) 
    -> (sat rho phi <-> sat sigma phi).
  Proof.
    intros F Bi Bp. apply sat_ext_bounded.
    - intros x H. exfalso. apply H. eapply bounded_indi_up. 2: apply Bi. lia.
    - intros x ar H. exfalso. apply H. apply funcfree_bounded_func, F.
    - intros x ar H. exfalso. apply H. eapply bounded_pred_up. 2: apply Bp. lia.
  Qed.

  Lemma sat_ext_closed_FO phi rho sigma :
    first_order phi -> bounded_indi 0 phi -> (sat rho phi <-> sat sigma phi).
  Proof.
    intros F B. apply sat_ext_bounded.
    - intros x H. exfalso. apply H. eapply bounded_indi_up. 2: apply B. lia.
    - intros x ar H. exfalso. apply H. apply funcfree_bounded_func, firstorder_funcfree, F.
    - intros x ar H. exfalso. apply H. apply firstorder_bounded_pred, F.
  Qed.

End BoundedSat.




Section Subst.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Variable domain : Type.
  Context {I : interp domain}.

  Lemma eval_function_subst_cons_shift_f (rho : env domain) ar (f : function ar) ar' (g : vec domain ar' -> domain) :
    eval_function rho f = eval_function ⟨ get_indi rho, g .: get_func rho, get_pred rho ⟩ (f[↑ ar']f).
  Proof.
    destruct f.
    - unfold econs, econs_func, econs_ar, shift, shift_f; cbn.
      destruct Nat.eq_dec as [->|]; cbn. now destruct Nat.eq_dec.
      destruct n. destruct Nat.eq_dec; try easy. now destruct Nat.eq_dec.
    - reflexivity.
  Qed.

  Lemma eval_predicate_subst_cons_shift_p (rho : env domain) ar (P : predicate ar) ar' (Q : vec domain ar' -> Prop) :
    eval_predicate rho P = eval_predicate ⟨ get_indi rho, get_func rho, Q .: get_pred rho ⟩ (P[↑ ar']p).
  Proof.
    destruct P.
    - unfold econs, econs_pred, econs_ar, shift, shift_p; cbn.
      destruct Nat.eq_dec as [->|]; cbn. now destruct Nat.eq_dec.
      destruct n. destruct Nat.eq_dec; try easy. now destruct Nat.eq_dec.
    - reflexivity.
  Qed.

  Lemma eval_subst_cons_shift_f (rho : env domain) ar (f : vec domain ar -> domain) t :
    eval rho t = eval ⟨get_indi rho, f .: get_func rho, get_pred rho⟩ t[↑ ar]f.
  Proof.
    induction t; cbn [eval].
    - reflexivity.
    - rewrite eval_function_subst_cons_shift_f with (g := f).
      cbn. f_equal. rewrite map_map. apply map_ext_forall, IH.
    - cbn. f_equal. rewrite map_map. apply map_ext_forall, IH.
  Qed.

  Lemma eval_comp_i (rho : env domain) σ t :
    eval rho (t[σ]i) = eval ⟨σ >> eval rho, get_func rho, get_pred rho⟩ t.
  Proof.
    induction t; cbn. reflexivity. all: f_equal; rewrite map_map; apply map_ext_forall, IH.
  Qed.

  Lemma eval_comp_f (rho : env domain) σ t :
    eval rho (t[σ]f) = eval ⟨get_indi rho, σ >>> eval_function rho, get_pred rho⟩ t.
  Proof.
    induction t; cbn. reflexivity. all: f_equal; rewrite map_map; apply map_ext_forall, IH.
  Qed.

  Lemma sat_comp_i rho σ phi :
    sat rho (phi[σ]i) <-> sat ⟨σ >> eval rho, get_func rho, get_pred rho⟩ phi.
  Proof.
    induction phi in rho, σ |- *; cbn.
    - reflexivity.
    - destruct p; cbn; erewrite map_map, map_ext; try reflexivity;
      induction t; firstorder using eval_comp_i.
    - specialize (IHphi1 rho σ); specialize (IHphi2 rho σ).
      destruct b; cbn; firstorder.
    - destruct q.
      + setoid_rewrite IHphi. split; intros H d; eapply sat_ext.
        2, 4: apply (H d). all: intros []; split; try easy;
        cbn; erewrite eval_comp_i; now destruct rho.
      + setoid_rewrite IHphi. split; intros [d H]; exists d; eapply sat_ext.
        2, 4: apply H. all: intros []; split; try easy;
        cbn; erewrite eval_comp_i; now destruct rho.
    - destruct q.
      + setoid_rewrite IHphi; split; intros H f; eapply sat_ext.
        2, 4: apply (H f). all: split; try easy. 2: symmetry.
        all: apply eval_subst_cons_shift_f.
      + setoid_rewrite IHphi; split; intros [f H]; exists f; eapply sat_ext.
        2, 4: apply H. all: split; try easy. 2: symmetry.
        all: apply eval_subst_cons_shift_f.
    - destruct q.
      + setoid_rewrite IHphi; split; intros H P; eapply sat_ext.
        2, 4: apply (H P). all: split; try easy; now apply eval_ext.
      + setoid_rewrite IHphi; split; intros [P H]; exists P; eapply sat_ext.
        2, 4: apply H. all: split; try easy; now apply eval_ext.
  Qed.

  Lemma sat_comp_f rho σ phi :
    sat rho (phi[σ]f) <-> sat ⟨get_indi rho, σ >>> eval_function rho, get_pred rho⟩ phi.
  Proof.
    induction phi in rho, σ |- *; cbn.
    - reflexivity.
    - destruct p; cbn; erewrite map_map, map_ext; try reflexivity;
      induction t; firstorder using eval_comp_f.
    - specialize (IHphi1 rho σ); specialize (IHphi2 rho σ).
      destruct b; cbn; firstorder.
    - destruct q.
      + setoid_rewrite IHphi. split; intros H d; eapply sat_ext.
        2, 4: apply (H d). all: easy.
      + setoid_rewrite IHphi. split; intros [d H]; exists d; eapply sat_ext.
        2, 4: apply H. all: easy.
    - destruct q.
      + setoid_rewrite IHphi; split; intros H f; eapply sat_ext.
        2, 4: apply (H f). 
        all: intros []; repeat split; try easy; cbn; destruct Nat.eq_dec as [->|]; cbn.
        1, 5: destruct Nat.eq_dec; try easy; rewrite Eqdep_dec.UIP_dec with (p1 := e) (p2 := eq_refl); try easy; decide equality.
        1-3: now rewrite eval_function_subst_cons_shift_f with (g := f).
        all: now rewrite <- eval_function_subst_cons_shift_f with (g := f).
      + setoid_rewrite IHphi; split; intros [f H]; exists f; eapply sat_ext.
        2, 4: apply H.
        all: intros []; repeat split; try easy; cbn; destruct Nat.eq_dec as [->|]; cbn.
        1, 5: destruct Nat.eq_dec; try easy; rewrite Eqdep_dec.UIP_dec with (p1 := e) (p2 := eq_refl); try easy; decide equality.
        1-3: now rewrite eval_function_subst_cons_shift_f with (g := f).
        all: now rewrite <- eval_function_subst_cons_shift_f with (g := f).
    - destruct q.
      + setoid_rewrite IHphi; split; intros H P; eapply sat_ext.
        2, 4: apply (H P). all: intros; split; try easy; now apply eval_ext.
      + setoid_rewrite IHphi; split; intros [P H]; exists P; eapply sat_ext.
        2, 4: apply H. all: intros; split; try easy; now apply eval_ext.
  Qed.

  Lemma sat_comp_p rho σ phi :
    sat rho (phi[σ]p) <-> sat ⟨get_indi rho, get_func rho, σ >>> eval_predicate rho⟩ phi.
  Proof.
    induction phi in rho, σ |- *; cbn.
    - reflexivity.
    - destruct p; cbn; rename t into v;
      enough (map (eval rho) v = map (eval ⟨get_indi rho, get_func rho, σ >>> eval_predicate rho⟩) v) as -> by reflexivity;
      apply map_ext_forall; induction v; firstorder; now apply eval_ext.
    - specialize (IHphi1 rho σ); specialize (IHphi2 rho σ).
      destruct b; cbn; firstorder.
    - destruct q.
      + setoid_rewrite IHphi. split; intros H d; eapply sat_ext.
        2, 4: apply (H d). all: easy.
      + setoid_rewrite IHphi. split; intros [d H]; exists d; eapply sat_ext.
        2, 4: apply H. all: easy.
    - destruct q.
      + setoid_rewrite IHphi. split; intros H f; eapply sat_ext.
        2, 4: apply (H f). all: easy.
      + setoid_rewrite IHphi. split; intros [f H]; exists f; eapply sat_ext.
        2, 4: apply H. all: easy.
    - destruct q.
      + setoid_rewrite IHphi; split; intros H P; eapply sat_ext.
        2, 4: apply (H P). 
        all: intros []; split; try easy; split; try easy; cbn; destruct Nat.eq_dec as [->|]; cbn.
        1, 5: destruct Nat.eq_dec; try easy; rewrite Eqdep_dec.UIP_dec with (p1 := e) (p2 := eq_refl); try easy; decide equality.
        1-3: now rewrite eval_predicate_subst_cons_shift_p with (Q := P).
        all: now rewrite <- eval_predicate_subst_cons_shift_p with (Q := P).
      + setoid_rewrite IHphi; split; intros [P H]; exists P; eapply sat_ext.
        2, 4: apply H. 
        all: intros []; split; try easy; split; try easy; cbn; destruct Nat.eq_dec as [->|]; cbn.
        1, 5: destruct Nat.eq_dec; try easy; rewrite Eqdep_dec.UIP_dec with (p1 := e) (p2 := eq_refl); try easy; decide equality.
        1-3: now rewrite eval_predicate_subst_cons_shift_p with (Q := P).
        all: now rewrite <- eval_predicate_subst_cons_shift_p with (Q := P).
  Qed.

End Subst.
