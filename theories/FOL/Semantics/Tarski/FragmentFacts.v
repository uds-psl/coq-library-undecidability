(* * Tarski Semantics *)

Require Import Undecidability.FOL.Syntax.Facts.
Require Export Undecidability.FOL.Semantics.Tarski.FragmentCore.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Require Import Vector Lia.


Local Set Implicit Arguments.
Local Unset Strict Implicit.

Set Default Proof Using "Type".

Local Notation vec := Vector.t.


(** Tarski Semantics ***)


Section Tarski.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  (* Semantic notions *)
  
  
  Section Substs.
    
    Variable D : Type.
    Variable I : interp D.
        
    Lemma eval_ext rho xi t :
      (forall x, rho x = xi x) -> eval rho t = eval xi t.
    Proof.
      intros H. induction t; cbn.
      - now apply H.
      - f_equal. apply map_ext_in. now apply IH.
    Qed.

    Lemma eval_comp rho xi t :
      eval rho (subst_term xi t) = eval (xi >> eval rho) t.
    Proof.
      induction t; cbn.
      - reflexivity.
      - f_equal. rewrite map_map. apply map_ext_in, IH.
    Qed.

    Lemma sat_ext {ff : falsity_flag} rho xi phi :
      (forall x, rho x = xi x) -> rho ⊨ phi <-> xi ⊨ phi.
    Proof.
      induction phi  as [ | b P v | | ] in rho, xi |- *; cbn; intros H.
      - reflexivity.
      - erewrite map_ext; try reflexivity. intros t. now apply eval_ext.
      - specialize (IHphi1 rho xi). specialize (IHphi2 rho xi). destruct b0; intuition.
      - destruct q.
        + split; intros H' d; eapply IHphi; try apply (H' d). 1,2: intros []; cbn; intuition.
    Qed.

    Lemma sat_ext' {ff : falsity_flag} rho xi phi :
      (forall x, rho x = xi x) -> rho ⊨ phi -> xi ⊨ phi.
    Proof.
      intros Hext H. rewrite sat_ext. exact H.
      intros x. now rewrite (Hext x).
    Qed.

    Lemma sat_comp {ff : falsity_flag} rho xi phi :
      rho ⊨ (subst_form xi phi) <-> (xi >> eval rho) ⊨ phi.
    Proof.
      induction phi as [ | b P v | | ] in rho, xi |- *; cbn.
      - reflexivity.
      - erewrite map_map, map_ext; try reflexivity. intros t. apply eval_comp.
      - specialize (IHphi1 rho xi). specialize (IHphi2 rho xi). destruct b0; intuition.
      - destruct q.
        + setoid_rewrite IHphi. split; intros H d; eapply sat_ext. 2, 4: apply (H d).
          all: intros []; cbn; trivial; now setoid_rewrite eval_comp.
    Qed.

    Lemma sat_subst {ff : falsity_flag} rho sigma phi :
      (forall x, eval rho (sigma x) = rho x) -> rho ⊨ phi <-> rho ⊨ (subst_form sigma phi).
    Proof.
      intros H. rewrite sat_comp. apply sat_ext. intros x. now rewrite <- H.
    Qed.

    Lemma sat_single {ff : falsity_flag} (rho : nat -> D) (Phi : form) (t : term) :
      (eval rho t .: rho) ⊨ Phi <-> rho ⊨ subst_form (t..) Phi.
    Proof.
      rewrite sat_comp. apply sat_ext. now intros [].
    Qed.

    Lemma impl_sat {ff : falsity_flag} A rho phi :
      sat rho (A ==> phi) <-> ((forall psi, psi el A -> sat rho psi) -> sat rho phi).
    Proof.
      induction A; cbn; firstorder congruence.
    Qed.

    Lemma impl_sat' {ff : falsity_flag} A rho phi :
      sat rho (A ==> phi) -> ((forall psi, psi el A -> sat rho psi) -> sat rho phi).
    Proof.
      eapply impl_sat.
    Qed.

    Lemma bounded_eval_t n t sigma tau :
      (forall k, n > k -> sigma k = tau k) -> bounded_t n t -> eval sigma t = eval tau t.
    Proof.
      intros H. induction 1; cbn; auto.
      f_equal. now apply Vector.map_ext_in.
    Qed.
    
    Lemma bound_ext {ff : falsity_flag} N phi rho sigma :
      bounded N phi -> (forall n, n < N -> rho n = sigma n) -> (rho ⊨ phi <-> sigma ⊨ phi).
    Proof.
      induction 1 in sigma, rho |- *; cbn; intros HN; try tauto.
      - enough (map (eval rho) v = map (eval sigma) v) as E. now setoid_rewrite E.
        apply Vector.map_ext_in. intros t Ht.
        eapply bounded_eval_t; try apply HN. now apply H.
      - destruct binop; now rewrite (IHbounded1 rho sigma), (IHbounded2 rho sigma).
      - destruct quantop.
        + split; intros Hd d; eapply IHbounded.
          all : try apply (Hd d); intros [] Hk; cbn; auto.
          symmetry. all: apply HN; lia.
    Qed. 

    Corollary sat_closed {ff : falsity_flag} rho sigma phi :
      bounded 0 phi -> rho ⊨ phi <-> sigma ⊨ phi.
    Proof.
      intros H. eapply bound_ext. apply H. lia.
    Qed.

    Lemma bounded_S_forall {ff : falsity_flag} N phi :
      bounded (S N) phi <-> bounded N (∀ phi).
    Proof.
      split; intros H.
      - now constructor.
      - inversion H. apply Eqdep_dec.inj_pair2_eq_dec in H4 as ->; trivial.
        unfold Dec.dec. decide equality.
    Qed.

    Definition forall_times {ff : falsity_flag} n (phi : form) := iter (fun psi => ∀ psi) n phi.

  End Substs.

End Tarski.



(* Trivial Model *)

Section TM.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Instance TM : interp unit :=
    {| i_func := fun _ _ => tt; i_atom := fun _ _ => True; |}.

  Fact TM_sat (rho : nat -> unit) (phi : form falsity_off) :
    rho ⊨ phi.
  Proof.
    revert rho. remember falsity_off as ff. induction phi; cbn; trivial.
    - discriminate.
    - destruct b0; auto.
    - destruct q; firstorder.
  Qed.

  Fact TM_sat_decidable {ff} (rho : nat -> unit) (phi : form ff) :
    rho ⊨ phi \/ ~(rho ⊨ phi).
  Proof.
    revert rho. induction phi; cbn; intros rho; eauto.
    - destruct b0. destruct (IHphi1 rho), (IHphi2 rho); tauto.
    - destruct q. destruct (IHphi (tt .: rho)).
      + left; now intros [].
      + right; intros Hcc. apply H, Hcc.
  Qed.

End TM.

Section FlagsTransport.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ff1 : falsity_flag}.

  Section Bottom.
    Variable D : Type.
    Variable I : interp D. 
    Context (default : @form _ _ _ ff1).

    Lemma sat_to_falsity_compat {ff2} rho (phi : @form _ _ _ ff2) : 
      (sat rho default -> False)
      -> sat rho phi <-> sat rho (phi[default /⊥]).
    Proof.
      induction phi as [|t1 t2|ff [] phi IHphi psi IHpsi|ff [] phi IHphi] in rho,default|-*; intros Hdefault; split.
      - intros [].
      - apply Hdefault.
      - intros H; apply H.
      - intros H; apply H.
      - intros H H1. cbn in H. apply IHpsi. 1:easy. apply H. now eapply IHphi, H1.
      - intros H H1. cbn in H. apply IHpsi with default. 1:easy. apply H. now apply IHphi.
      - intros H d. apply IHphi. 2: apply H. intros Hd. apply Hdefault.
        eapply sat_comp in Hd. eapply sat_ext in Hd. 1: apply Hd.
        now intros [|x].
      - intros H d. apply IHphi with (default [↑]). 2: apply H. intros Hd. apply Hdefault.
        eapply sat_comp in Hd. eapply sat_ext in Hd. 1: apply Hd.
        now intros [|x].
    Qed.
  End Bottom.
  Section Atoms.

    Context {Σ_preds2 : preds_signature}.
    Context (s : forall (P : Σ_preds), Vector.t (@term Σ_funcs) (ar_preds P) -> (@form Σ_funcs Σ_preds2 _ _)).
    Context (Hresp : atom_subst_respects_strong s).

    Variable D : Type.
    (* Crucially, we need an interpretation for the formulas s maps _to_ *)
    Variable I : @interp Σ_funcs Σ_preds2 D. 

    Definition rho_from_vec {A} n (v : Vector.t A n) d : env A := fun m => match Compare_dec.lt_dec m n with
      left Hl => Vector.nth v (Fin.of_nat_lt Hl)
    | right _ => d end.

    Lemma rho_from_vec_map {A B} {n} (f : B -> A) (t : Vector.t B n) (d2 : A) (d:B):
     f d = d2 ->
     forall k, rho_from_vec (map f t) d2 k = f (rho_from_vec t d k).
    Proof.
      intros H k. unfold rho_from_vec. destruct (Compare_dec.lt_dec k n) as [Hl|Hr].
      - erewrite nth_map. 2:reflexivity. easy.
      - easy.
    Qed.

    Definition tabulate_vars n : Vector.t term n := Vectors.tabulate (fun p => $(proj1_sig (Fin.to_nat p))).

    Lemma semantic_lifting_correct n t tt : 
      map (subst_term (rho_from_vec t tt)) (tabulate_vars n) = t.
    Proof.
      apply Vectors.eq_nth_iff'. intros i.
      erewrite nth_map. 2:reflexivity.
      unfold tabulate_vars. rewrite Vectors.nth_tabulate. cbn.
      unfold rho_from_vec. destruct (Fin.to_nat i) as [k Hk] eqn:Heq. cbn.
      destruct Compare_dec.lt_dec; try lia. f_equal.
      erewrite Fin.of_nat_ext.
      rewrite <- Fin.to_nat_of_nat in Heq.
      apply Fin.to_nat_inj. rewrite <- Heq. easy.
    Qed.

    Definition lift_s_semantically (d:D) (P : Σ_preds) (v : Vector.t D (ar_preds P)) : Prop
      := sat (rho_from_vec v d) (s (tabulate_vars (ar_preds P))).

    (* To construct an interpretation for the formulas we are mapping _from_ *)
    Definition interp_s (d:D) : @interp Σ_funcs Σ_preds D := {|
      i_func := @i_func _ _ D I;
      i_atom := lift_s_semantically d
    |}.

    Lemma sat_atom_subst_compat rho phi n :
      sat rho (phi [s/atom]) <-> @sat _ _ _ (interp_s (rho n)) _ rho phi.
    Proof using Hresp.
      unfold interp_s, lift_s_semantically. revert rho n.
      induction phi as [|t1 t2|ff [] phi IHphi psi IHpsi|ff [] phi IHphi]; split.
      - intros H; apply H.
      - intros H; apply H.
      - cbn; intros H.
        eapply sat_ext with (((rho_from_vec t $n) >> eval rho)).
        1: intros x; unfold funcomp. now apply rho_from_vec_map.
        rewrite <- sat_comp. rewrite Hresp. now rewrite semantic_lifting_correct.
      - cbn; intros H. 
        eapply (@sat_ext _ _ _ _ _ (((rho_from_vec t $n) >> eval rho))) in H.
        2: intros x; unfold funcomp; symmetry; now apply rho_from_vec_map.
        rewrite <- sat_comp in H. rewrite Hresp in H. now rewrite semantic_lifting_correct in H.
      - cbn; intros H1 Hphi. apply IHpsi. 1:easy. apply H1. apply IHphi with n. 1:easy. apply Hphi.
      - cbn; intros H1 Hphi. apply IHpsi with n. 1:easy. apply H1, IHphi. 1:easy. apply Hphi.
      - cbn; intros H1 d. apply (IHphi s Hresp (d.:rho) (S n)). apply H1.
      - cbn; intros H1 d. apply (IHphi s Hresp (d.:rho) (S n)). apply H1.
    Qed.

  End Atoms.

End FlagsTransport.

Section Bottom.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Variable D : Type.
  Variable I : interp D.

  Definition interp_bot (F_P : Prop) (i : @interp Σ_funcs Σ_preds D) : @interp Σ_funcs (@Σ_preds_bot Σ_preds) D := {|
    i_func := @i_func _ _ D i;
    i_atom := fun (P : (@preds (@Σ_preds_bot Σ_preds))) => match P with inl _ => fun v => F_P | inr P => fun v => @i_atom _ _ D i P v end
  |}.

  Definition sat_bot {ff : falsity_flag} (F_P : Prop) (rho : env D) (phi : form) : Prop 
    := @sat _ Σ_preds_bot D (interp_bot F_P I) falsity_off rho (falsity_to_pred phi).

  Lemma sat_bot_False {ff:falsity_flag} rho phi : sat_bot False rho phi <-> sat rho phi.
  Proof.
    induction phi in rho|-*.
    - easy.
    - easy.
    - destruct b0. unfold sat_bot, falsity_to_pred in *. cbn.
      split; intros H H1 %IHphi1; apply IHphi2; apply H, H1.
    - destruct q. unfold sat_bot, falsity_to_pred in *. cbn.
      split; intros H d; apply IHphi, H.
  Qed.

End Bottom.

