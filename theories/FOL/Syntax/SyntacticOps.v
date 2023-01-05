From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation Shared.Dec.
Import ListAutomationNotations.

From Coq Require Import Eqdep_dec.
Require Import Coq.Vectors.Vector.
From Undecidability.Shared.Libs.PSL.Vectors Require Import Vectors.
Require Import EqdepFacts.

Local Notation vec := t.

From Undecidability.FOL.Syntax Require Export Core Subst Bounded.


Local Set Implicit Arguments.
Local Unset Strict Implicit.



Section FalsitySubstitution.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Fixpoint to_falsity {ff:falsity_flag} (phi : form) : @form _ _ _ falsity_on :=
    match phi with
      falsity => falsity
    | atom P v => atom P v
    | bin b f1 f2 => bin b (to_falsity f1) (to_falsity f2)
    | quant q f => quant q (to_falsity f)
    end.

  Fixpoint subst_falsity {ff ff_old:falsity_flag} (default : @form _ _ _ ff) (phi : @form _ _ _ ff_old) : @form _ _ _ ff :=
    match phi with
      falsity => default
    | atom P v => atom P v
    | bin b f1 f2 => (bin b (subst_falsity default f1) (subst_falsity default f2))
    | quant q f => (quant q (subst_falsity (default[↑]) f))
    end.
  Notation "phi [ psi /⊥]" := (@subst_falsity _ _ psi phi) (at level 7, left associativity) : subst_scope.

  Lemma to_falsity_id (phi : @form _ _ _ falsity_on) : to_falsity phi = phi.
  Proof.
    enough ((forall ff (phi : @form _ _ _ ff) (Heq : ff = falsity_on),
              to_falsity phi = match Heq in _ = fff return @form _ _ _ fff with eq_refl => phi end)) as H by apply (H _ _ eq_refl).
    clear phi. intros ff phi. induction phi; intros Heq; try congruence; try subst.
    - pattern Heq. unshelve eapply (@K_dec_type falsity_flag _ falsity_on _ _ Heq). 1:decide equality.
      easy.
    - easy.
    - cbn. rewrite IHphi1 with eq_refl. rewrite IHphi2 with eq_refl. easy.
    - cbn. rewrite IHphi with eq_refl. easy.
  Qed.

  Lemma subst_falsity_id {f} (phi : @form _ _ _ f) : phi[falsity /⊥] = to_falsity phi.
  Proof.
    induction phi; cbn; try congruence.
  Qed.

  Lemma subst_falsity_invert d (phi : @form _ _ _ falsity_off) : (to_falsity phi)[d/⊥] = phi.
  Proof.
    remember falsity_off as Hff.
    induction phi; cbn; try discriminate.
    - eauto.
    - rewrite IHphi1. 2:easy. now rewrite IHphi2.
    - now rewrite IHphi.
  Qed.

  Lemma subst_falsity_comm {ff1 ff2} (phi : @form _ _ _ ff1) (psi : @form _ _ _ ff2) rho :
    phi[psi/⊥][rho] = phi[rho][psi[rho]/⊥].
  Proof.
    induction phi in rho,psi|-*.
    - easy.
    - easy.
    - cbn. rewrite IHphi1. rewrite IHphi2. easy.
    - cbn. f_equal. rewrite IHphi. f_equal. apply up_form.
  Qed.

End FalsitySubstitution.

#[global] Notation "phi [ psi /⊥]" := (@subst_falsity _ _ _ _ _ psi phi) (at level 7, left associativity) : subst_scope.

Section FunctionSubstitution.

  Context {Σ_funcs1 : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Fixpoint func_subst_term {Σ_funcs2} (s : forall (f : Σ_funcs1), Vector.t (@term Σ_funcs2) (ar_syms f) -> @term Σ_funcs2)
     (t : @term Σ_funcs1) {struct t} : @term Σ_funcs2 :=
    match t with
      var k => var k
    | func f v => s f (Vector.map (func_subst_term s) v)
    end.

  Notation "t `[ s '/func' ]" := (func_subst_term s t) (at level 7, left associativity) : subst_scope.

  (* Warning: this property is to weak to be useful and should be refined into something "more useful" *)
  Definition func_subst_respects {Σ_funcs2} (s : forall (f : Σ_funcs1), Vector.t (@term Σ_funcs2) (ar_syms f) -> @term Σ_funcs2)
    := forall f v sigma, (s f v)`[sigma>>var] = s f (map (subst_term (sigma >> var)) v).

  Lemma func_subst_term_id t : t`[ func /func] = t.
  Proof.
    induction t.
    - easy.
    - cbn. rewrite <- (@map_id _ _ v). f_equal. rewrite map_map. apply VectorSpec.map_ext_in, IH.
  Qed.

  Lemma func_subst_term_comp s rho t : func_subst_respects s -> t`[s/func]`[rho>>var] = t`[rho>>var]`[s/func].
  Proof.
  intros Hresp.
  induction t in s,rho,Hresp|-*.
  - easy.
  - cbn. rewrite Hresp. f_equal. rewrite ! map_map. apply VectorSpec.map_ext_in.
    intros a Hva. now rewrite IH.
  Qed.

  Fixpoint func_subst {Σ_funcs2} {ff:falsity_flag} (s : forall (f : Σ_funcs1), Vector.t (@term Σ_funcs2) (ar_syms f) -> @term Σ_funcs2)
     (f : @form Σ_funcs1 _ _ _) {struct f} : @form Σ_funcs2 _ _ _ :=
    match f with
      falsity => falsity
    | atom _ _ P v => atom _ _ P (map (func_subst_term s) v)
    | bin _ _ b phi psi => bin _ _ b (func_subst s phi) (func_subst s psi)
    | quant _ _ q phi => quant _ _ q (func_subst s phi)
    end.

  Notation "phi [ s '/func' ]" := (func_subst s phi) (at level 7, left associativity) : subst_scope.

  Lemma func_subst_id {ff:falsity_flag} phi : phi[ func /func] = phi.
  Proof.
    induction phi.
    - easy.
    - cbn. rewrite <- (@map_id _ _ t). f_equal. rewrite map_map. apply VectorSpec.map_ext_in.
      intros a Hva; now rewrite func_subst_term_id.
    - cbn. rewrite IHphi1. now rewrite IHphi2.
    - cbn. now rewrite IHphi.
  Qed.

  Lemma up_var_comp rho x : (up (rho >> var)) x = ((fun n => match n with 0 => 0 | S n => S (rho n) end) >>var) x.
  Proof.
    now destruct x.
  Qed.

  Lemma func_subst_comp {ff:falsity_flag} s rho phi : func_subst_respects s -> phi[s/func][rho>>var] = phi[rho>>var][s/func].
  Proof.
  intros Hresp.
  induction phi in s,rho,Hresp|-*.
  - easy.
  - cbn. rewrite ! map_map. f_equal. apply map_ext. intros a. now apply func_subst_term_comp.
  - cbn. rewrite IHphi1. 1: now rewrite IHphi2. easy.
  - cbn. f_equal. rewrite ! (subst_ext _ (up_var_comp _) ). rewrite IHphi. 1:easy.
    easy.
  Qed.


End FunctionSubstitution.

#[global] Notation "t `[ s '/func' ]" := (func_subst_term s t) (at level 7, left associativity) : subst_scope.
#[global] Notation "phi [ s '/func' ]" := (func_subst s phi) (at level 7, left associativity) : subst_scope.

Section PredicateSubstitution.

  Context {Σ_funcs1 : funcs_signature}.
  Context {Σ_preds1 : preds_signature}.
  Context {ops : operators}.

  Fixpoint atom_subst {Σ_funcs2} {Σ_preds2} {ff:falsity_flag} (s : forall (P : Σ_preds1), Vector.t (@term Σ_funcs1) (ar_preds P) -> (@form Σ_funcs2 Σ_preds2 _ _))
     (f : @form Σ_funcs1 Σ_preds1 _ _) {struct f} : @form Σ_funcs2 Σ_preds2 _ _.
  Proof.
  destruct f as [|ff P v|ff b phi psi|ff q phi].
  + exact falsity.
  + exact (s P v).
  + exact (bin b (atom_subst _ _ _ s phi) (atom_subst _ _ _ s psi)).
  + exact (quant q (atom_subst _ _ _ s phi)).
  Defined.

  Notation "phi [ s '/atom' ]" := (atom_subst s phi) (at level 7, left associativity) : subst_scope.

  Definition atom_subst_respects {Σ_preds2} {ff:falsity_flag} 
    (s : forall (P : Σ_preds1), Vector.t (@term Σ_funcs1) (ar_preds P) -> (@form Σ_funcs1 Σ_preds2 _ _))
    := forall f v sigma, (s f v)[sigma] = s f (map (subst_term (sigma)) v).

  Lemma atom_subst_id {ff:falsity_flag} phi : phi[ atom /atom] = phi.
  Proof.
    induction phi.
    - easy.
    - cbn. easy.
    - cbn. rewrite IHphi1. now rewrite IHphi2.
    - cbn. now rewrite IHphi.
  Qed.

  Lemma atom_subst_comp {Σ_preds2} {ff:falsity_flag} s rho phi : 
    @atom_subst_respects Σ_preds2 _ s -> phi[s/atom][rho] = phi[rho][s/atom].
  Proof.
  intros Hresp.
  induction phi in s,rho,Hresp|-*.
  - easy.
  - cbn. rewrite Hresp. easy.
  - cbn. rewrite IHphi1. 1: now rewrite IHphi2. easy.
  - cbn. now rewrite IHphi.
  Qed.

End PredicateSubstitution.

#[global] Notation "phi [ s '/atom' ]" := (atom_subst s phi) (at level 7, left associativity) : subst_scope.

Section BottomToPred.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Definition Σ_preds_bot : preds_signature := {|
    preds := sum unit (@preds Σ_preds) ;
    ar_preds := fun k => match k with inl _ => 0 | inr k' => @ar_preds Σ_preds k' end
  |}.

  Definition falsity_to_pred {ff} (phi : @form _ Σ_preds _ ff) : @form _ Σ_preds_bot _ falsity_off
    := phi[(fun P v => @atom _ Σ_preds_bot _ _ (inr P) v) /atom]
          [( @atom _ Σ_preds_bot _ _ (inl tt) (Vector.nil _)) /⊥].

  Lemma falsity_to_pred_subst {ff:falsity_flag} phi rho : falsity_to_pred (phi[rho]) = (falsity_to_pred phi)[rho].
  Proof.
    unfold falsity_to_pred.
    rewrite subst_falsity_comm.
    cbn. now rewrite atom_subst_comp.
  Qed.

End BottomToPred.
