(* * First-Order Logic *)


From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.

Require Import Coq.Vectors.Vector.
Local Notation vec := t.

From Undecidability Require Export FOL.Util.Syntax.

Require Import Equations.Equations.

Section fix_signature.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  (* Induction principle for terms *)

  Inductive Forall {A : Type} (P : A -> Type) : forall {n}, t A n -> Type :=
  | Forall_nil : Forall P (@Vector.nil A)
  | Forall_cons : forall n (x : A) (l : t A n), P x -> Forall P l -> Forall P (@Vector.cons A x n l).

  Inductive vec_in {A : Type} (a : A) : forall {n}, t A n -> Type :=
  | vec_inB {n} (v : t A n) : vec_in a (cons A a n v)
  | vec_inS a' {n} (v : t A n) : vec_in a v -> vec_in a (cons A a' n v).
  Hint Constructors vec_in : core.
  
  Lemma term_rect' (p : term -> Type) :
    (forall x, p (var x)) -> (forall F v, (Forall p v) -> p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. fix strong_term_ind' 1. destruct t as [n|F v].
    - apply f1.
    - apply f2. induction v.
      + econstructor.
      + econstructor. now eapply strong_term_ind'. eauto.
  Qed.

  Lemma term_rect (p : term -> Type) :
    (forall x, p (var x)) -> (forall F v, (forall t, vec_in t v -> p t) -> p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. eapply term_rect'.
    - apply f1.
    - intros. apply f2. intros t. induction 1; inversion X; subst; eauto.
      apply Eqdep_dec.inj_pair2_eq_dec in H2; subst; eauto. decide equality.
  Qed.

  Lemma term_ind (p : term -> Prop) :
    (forall x, p (var x)) -> (forall F v (IH : forall t, In t v -> p t), p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. eapply term_rect'.
    - apply f1.
    - intros. apply f2. intros t. induction 1; inversion X; subst; eauto.
      apply Eqdep_dec.inj_pair2_eq_dec in H3; subst; eauto. decide equality.
  Qed.

  (* Substitution induction principle for formulas *)

  Fixpoint size {ff : falsity_flag} (phi : form) :=
    match phi with
    | atom _ _ => 0
    | falsity => 0
    | bin b phi psi => S (size phi + size psi)
    | quant q phi => S (size phi)
    end.

  Lemma size_ind {X : Type} (f : X -> nat) (P : X -> Prop) :
    (forall x, (forall y, f y < f x -> P y) -> P x) -> forall x, P x.
  Proof.
    intros H x. apply H.
    induction (f x).
    - intros y. lia.
    - intros y. intros [] % Lt.le_lt_or_eq.
      + apply IHn; lia.
      + apply H. injection H0. now intros ->.
  Qed.

  Lemma subst_size {ff : falsity_flag} rho phi :
    size (subst_form rho phi) = size phi.
  Proof.
    revert rho; induction phi; intros rho; cbn; congruence.
  Qed.

  Derive Signature for form.

  Lemma form_ind_subst :
    forall P : form -> Prop,
      P falsity ->
      (forall P0 (t : vec term (ar_preds P0)), P (atom P0 t)) ->
      (forall (b0 : binop) (f1 : form), P f1 -> forall f2 : form, P f2 -> P (bin b0 f1 f2)) ->
      (forall (q : quantop) (f2 : form), (forall sigma, P (subst_form sigma f2)) -> P (quant q f2)) ->
      forall (f4 : form), P f4.
  Proof.
    intros P H1 H2 H3 H4 phi. induction phi using (@size_ind _ size). depelim phi; trivial.
    - injection H. intros -> % Eqdep_dec.inj_pair2_eq_dec; trivial. decide equality.
    - apply H3; apply H; cbn; lia.
    - apply H4. intros sigma. apply H. cbn. rewrite subst_size. lia.
  Qed.

End fix_signature.



(* ** Substituion lemmas *)

Section Subst.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Lemma subst_term_ext (t : term) sigma tau :
    (forall n, sigma n = tau n) -> t`[sigma] = t`[tau].
  Proof.
    intros H. induction t; cbn.
    - now apply H.
    - f_equal. now apply map_ext_in.
  Qed.

  Lemma subst_term_id (t : term) sigma :
    (forall n, sigma n = var n) -> t`[sigma] = t.
  Proof.
    intros H. induction t; cbn.
    - now apply H.
    - f_equal. now erewrite map_ext_in, map_id.
  Qed.

  Lemma subst_term_var (t : term) :
    t`[var] = t.
  Proof.
    now apply subst_term_id.
  Qed.

  Lemma subst_term_comp (t : term) sigma tau :
    t`[sigma]`[tau] = t`[sigma >> subst_term tau].
  Proof.
    induction t; cbn.
    - reflexivity.
    - f_equal. rewrite map_map. now apply map_ext_in.
  Qed.

  Lemma subst_term_shift (t : term) s :
    t`[↑]`[s..] = t.
  Proof.
    rewrite subst_term_comp. apply subst_term_id. now intros [|].
  Qed.

  Lemma up_term (t : term) xi :
    t`[↑]`[up xi] = t`[xi]`[↑].
  Proof.
    rewrite !subst_term_comp. apply subst_term_ext. reflexivity.
  Qed.

  Lemma up_ext sigma tau :
    (forall n, sigma n = tau n) -> forall n, up sigma n = up tau n.
  Proof.
    destruct n; cbn; trivial.
    unfold funcomp. now rewrite H.
  Qed.

  Lemma up_var sigma :
    (forall n, sigma n = var n) -> forall n, up sigma n = var n.
  Proof.
    destruct n; cbn; trivial.
    unfold funcomp. now rewrite H.
  Qed.

  Lemma up_funcomp sigma tau :
    forall n, (up sigma >> subst_term (up tau)) n = up (sigma >> subst_term tau) n.
  Proof.
    intros [|]; cbn; trivial.
    setoid_rewrite subst_term_comp.
    apply subst_term_ext. now intros [|].
  Qed.

  Lemma subst_ext {ff : falsity_flag} (phi : form) sigma tau :
    (forall n, sigma n = tau n) -> phi[sigma] = phi[tau].
  Proof.
    induction phi in sigma, tau |- *; cbn; intros H.
    - reflexivity.
    - f_equal. apply map_ext. intros s. now apply subst_term_ext.
    - now erewrite IHphi1, IHphi2.
    - erewrite IHphi; trivial. now apply up_ext.
  Qed.

  Lemma subst_id {ff : falsity_flag} (phi : form) sigma :
    (forall n, sigma n = var n) -> phi[sigma] = phi.
  Proof.
    induction phi in sigma |- *; cbn; intros H.
    - reflexivity.
    - f_equal. erewrite map_ext; try apply map_id. intros s. now apply subst_term_id.
    - now erewrite IHphi1, IHphi2.
    - erewrite IHphi; trivial. now apply up_var.
  Qed.

  Lemma subst_var {ff : falsity_flag} (phi : form) :
    phi[var] = phi.
  Proof.
    now apply subst_id.
  Qed.

  Lemma subst_comp {ff : falsity_flag} (phi : form) sigma tau :
    phi[sigma][tau] = phi[sigma >> subst_term tau].
  Proof.
    induction phi in sigma, tau |- *; cbn.
    - reflexivity.
    - f_equal. rewrite map_map. apply map_ext. intros s. apply subst_term_comp.
    - now rewrite IHphi1, IHphi2.
    - rewrite IHphi. f_equal. now apply subst_ext, up_funcomp.
  Qed.

  Lemma subst_shift {ff : falsity_flag} (phi : form) s :
    phi[↑][s..] = phi.
  Proof.
    rewrite subst_comp. apply subst_id. now intros [|].
  Qed.

  Lemma up_form {ff : falsity_flag} xi psi :
    psi[↑][up xi] = psi[xi][↑].
  Proof.
    rewrite !subst_comp. apply subst_ext. reflexivity.
  Qed.
  
End Subst.



(* ** Bounded formulas *)

Section Bounded.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Inductive bounded_t n : term -> Prop :=
  | bounded_var x : n > x -> bounded_t n $x
  | bouded_func f v : (forall t, Vector.In t v -> bounded_t n t) -> bounded_t n (func f v).

  Inductive bounded : forall {ff}, nat -> form ff -> Prop :=
  | bounded_atom ff n P v : (forall t, Vector.In t v -> bounded_t n t) -> @bounded ff n (atom P v)
  | bounded_bin binop ff n phi psi : @bounded ff n phi -> @bounded ff n psi -> @bounded ff n (bin binop phi psi)
  | bounded_quant quantop ff n phi : @bounded ff (S n) phi -> @bounded ff n (quant quantop phi)
  | bounded_falsity n : @bounded falsity_on n falsity.

  Arguments bounded {_} _ _.

  Definition bounded_L {ff : falsity_flag} n A :=
    forall phi, phi el A -> bounded n phi.

  Lemma bounded_subst_t n t sigma tau :
    (forall k, n > k -> sigma k = tau k) -> bounded_t n t -> t`[sigma] = t`[tau].
  Proof.
    intros H. induction 1; cbn; auto.
    f_equal. now apply Vector.map_ext_in.
  Qed.

  Lemma bounded_subst {ff : falsity_flag} {n phi sigma tau} :
    bounded n phi -> (forall k, n > k -> sigma k = tau k) -> phi[sigma] = phi[tau].
  Proof.
    induction 1 in sigma, tau |- *; cbn; intros HN; trivial.
    - f_equal. apply Vector.map_ext_in. intros t Ht.
      eapply bounded_subst_t; try apply HN. now apply H.
    - now rewrite (IHbounded1 sigma tau), (IHbounded2 sigma tau).
    - f_equal. apply IHbounded. intros [|k] Hk; cbn; trivial.
      unfold funcomp. rewrite HN; trivial. lia.
  Qed.

  Lemma bounded_up_t {n t k} :
    bounded_t n t -> k >= n -> bounded_t k t.
  Proof.
    induction 1; intros Hk; constructor; try lia. firstorder.
  Qed.

  Lemma bounded_up {ff : falsity_flag} {n phi k} :
    bounded n phi -> k >= n -> bounded k phi.
  Proof.
    induction 1 in k |- *; intros Hk; constructor; eauto.
    - intros t Ht. eapply bounded_up_t; eauto.
    - apply IHbounded. lia.
  Qed.

  Derive Signature for In.

  Lemma find_bounded_step n (v : vec term n) :
    (forall t : term, vec_in t v -> {n : nat | bounded_t n t}) -> { n | forall t, In t v -> bounded_t n t }.
  Proof.
    induction v; cbn; intros HV.
    - exists 0. intros t. inversion 1.
    - destruct IHv as [k Hk], (HV h) as [l Hl]; try left.
      + intros t Ht. apply HV. now right.
      + exists (k + l). intros t H. depelim H; cbn in *.
        * injection H. intros _ <-. apply (bounded_up_t Hl). lia.
        * injection H0. intros -> % Eqdep_dec.inj_pair2_eq_dec _; try decide equality.
          apply (bounded_up_t (Hk t H)). lia.
  Qed.

  Lemma find_bounded_t t :
    { n | bounded_t n t }.
  Proof.
    induction t using term_rect.
    - exists (S x). constructor. lia.
    - apply find_bounded_step in X as [n H]. exists n. now constructor.
  Qed.

  Lemma find_bounded {ff : falsity_flag} phi :
    { n | bounded n phi }.
  Proof.
    induction phi.
    - exists 0. constructor.
    - destruct (find_bounded_step _ t) as [n Hn].
      + eauto using find_bounded_t.
      + exists n. now constructor.
    - destruct IHphi1 as [n Hn], IHphi2 as [k Hk]. exists (n + k).
      constructor; eapply bounded_up; try eassumption; lia.
    - destruct IHphi as [n Hn]. exists n. constructor. apply (bounded_up Hn). lia.
  Qed.

  Lemma find_bounded_L {ff : falsity_flag} A :
    { n | bounded_L n A }.
  Proof.
    induction A; cbn.
    - exists 0. intros phi. inversion 1.
    - destruct IHA as [k Hk], (find_bounded a) as [l Hl].
      exists (k + l). intros t [<-|H]; eapply bounded_up; try eassumption; try (now apply Hk); lia.
  Qed.

End Bounded.

Lemma vec_cons_inv X n (v : Vector.t X n) x y :
  In y (Vector.cons X x n v) -> {y = x} + {In y v}.
Proof.
Admitted.

Ltac solve_bounds :=
  repeat constructor; try lia; try inversion X; intros;
  match goal with
  | H : Vector.In ?x (@Vector.cons _ ?y _ ?v) |- _ => repeat apply vec_cons_inv in H as [->|H]; try inversion H
  | H : Vector.In ?x (@Vector.nil _) |- _ => try inversion H
  | _ => idtac
  end.



(* ** Discreteness *)

Require Import EqdepFacts.

Lemma inj_pair2_eq_dec' A :
  eq_dec A -> forall (P : A -> Type) (p : A) (x y : P p), existT P p x = existT P p y -> x = y.
Proof.
  apply Eqdep_dec.inj_pair2_eq_dec.
Qed.

Ltac resolve_existT := try
  match goal with
     | [ H2 : @existT ?X _ _ _ = existT _ _ _ |- _ ] => eapply Eqdep_dec.inj_pair2_eq_dec in H2;
                                                      [subst | try (eauto || now intros; decide equality)]
  end.

Lemma dec_vec_in X n (v : vec X n) :
  (forall x, vec_in x v -> forall y, dec (x = y)) -> forall v', dec (v = v').
Proof with subst; try (now left + (right; intros[=])).
  intros Hv. induction v; intros v'; dependent elimination v'...
  destruct (Hv h (vec_inB h v) h0)... edestruct IHv.
  - intros x H. apply Hv. now right.
  - left. f_equal. apply e.
  - right. intros H. inversion H. resolve_existT. tauto.
Qed.

Instance dec_vec X {HX : eq_dec X} n : eq_dec (vec X n).
Proof.
  intros v. refine (dec_vec_in _ _ _ _).
Qed.

Section EqDec.
  
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Hypothesis eq_dec_Funcs : eq_dec syms.
  Hypothesis eq_dec_Preds : eq_dec preds.
  Hypothesis eq_dec_binop : eq_dec binop.
  Hypothesis eq_dec_quantop : eq_dec quantop.

  Global Instance dec_term : eq_dec term.
  Proof with subst; try (now left + (right; intros[=]; resolve_existT; congruence)).
    intros t. induction t as [ | ]; intros [|? v']...
    - decide (x = n)... 
    - decide (F = f)... destruct (dec_vec_in _ _ _ X v')...
  Qed.

  Instance dec_falsity : eq_dec falsity_flag.
  Proof.
    intros b b'. unfold dec. decide equality.
  Qed.

  Lemma eq_dep_falsity b phi psi :
    eq_dep falsity_flag (@form Σ_funcs Σ_preds ops) b phi b psi <-> phi = psi.
  Proof.
    rewrite <- eq_sigT_iff_eq_dep. split.
    - intros H. resolve_existT. reflexivity.
    - intros ->. reflexivity.
  Qed.

  Lemma dec_form_dep {b1 b2} phi1 phi2 : dec (eq_dep falsity_flag (@form _ _ _) b1 phi1 b2 phi2).
  Proof with subst; try (now left + (right; intros ? % eq_sigT_iff_eq_dep; resolve_existT; congruence)).
    unfold dec. revert phi2; induction phi1; intros; try destruct phi2.
    all: try now right; inversion 1. now left.
    - decide (b = b0)... decide (P = P0)... decide (t = t0)... right.
      intros [=] % eq_dep_falsity. resolve_existT. tauto.
    - decide (b = b1)... decide (b0 = b2)... destruct (IHphi1_1 phi2_1).
      + apply eq_dep_falsity in e as ->. destruct (IHphi1_2 phi2_2).
        * apply eq_dep_falsity in e as ->. now left.
        * right. rewrite eq_dep_falsity in *. intros [=]. now resolve_existT.
      + right. rewrite eq_dep_falsity in *. intros [=]. now repeat resolve_existT.
    - decide (b = b0)... decide (q = q0)... destruct (IHphi1 phi2).
      + apply eq_dep_falsity in e as ->. now left.
      + right. rewrite eq_dep_falsity in *. intros [=]. now resolve_existT.
  Qed.

  Global Instance dec_form {ff : falsity_flag} : eq_dec form.
  Proof.
    intros phi psi. destruct (dec_form_dep phi psi); rewrite eq_dep_falsity in *; firstorder.
  Qed.

End EqDec.



(* ** Enumerability *)

Section Enumerability.
  
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Variable list_Funcs : nat -> list syms.
  Hypothesis enum_Funcs' : list_enumerator__T list_Funcs syms.

  Variable list_Preds : nat -> list preds.
  Hypothesis enum_Preds' : list_enumerator__T list_Preds preds.

  Variable list_binop : nat -> list binop.
  Hypothesis enum_binop' : list_enumerator__T list_binop binop.

  Variable list_quantop : nat -> list quantop.
  Hypothesis enum_quantop' : list_enumerator__T list_quantop quantop.

  Fixpoint vecs_from X (A : list X) (n : nat) : list (vec X n) :=
    match n with
    | 0 => [Vector.nil X]
    | S n => [ Vector.cons X x _ v | (x,  v) ∈ (A × vecs_from X A n) ]
    end.

  Fixpoint L_term n : list term :=
    match n with
    | 0 => []
    | S n => L_term n ++ var n :: concat ([ [ func F v | v ∈ vecs_from _ (L_term n) (ar_syms F) ] | F ∈ L_T n])
    end.

  Lemma L_term_cml :
    cumulative L_term.
  Proof.
    intros ?; cbn; eauto.
  Qed.

  Lemma list_prod_in X Y (x : X * Y) A B :
    x el (A × B) -> exists a b, x = (a , b) /\ a el A /\ b el B.
  Proof.
    induction A; cbn.
    - intros [].
    - intros [H | H] % in_app_or. 2: firstorder.
      apply in_map_iff in H as (y & <- & Hel). exists a, y. tauto.
  Qed.

  Lemma vecs_from_correct X (A : list X) (n : nat) (v : vec X n) :
    (forall x, vec_in x v -> x el A) <-> v el vecs_from X A n.
  Proof.
    induction n; cbn.
    - split.
      + intros. left. now dependent elimination v.
      + intros [<- | []] x H. inv H.
    - split.
      + intros. dependent elimination v. in_collect (pair h t0); destruct (IHn t0).
        eauto using vec_inB. apply H0. intros x Hx. apply H. now right. 
      + intros Hv. apply in_map_iff in Hv as ([h v'] & <- & (? & ? & [= <- <-] & ? & ?) % list_prod_in).
        intros x H. inv H; destruct (IHn v'); eauto. apply H2; trivial. now resolve_existT.
  Qed.

  Lemma vec_forall_cml X (L : nat -> list X) n (v : vec X n) :
    cumulative L -> (forall x, vec_in x v -> exists m, x el L m) -> exists m, v el vecs_from _ (L m) n.
  Proof.
    intros HL Hv. induction v; cbn.
    - exists 0. tauto.
    - destruct IHv as [m H], (Hv h) as [m' H']. 1,3: eauto using vec_inB.
      + intros x Hx. apply Hv. now right.
      + exists (m + m'). in_collect (pair h v). 1: apply (cum_ge' (n:=m')); intuition lia.
      apply vecs_from_correct. rewrite <- vecs_from_correct in H. intros x Hx.
      apply (cum_ge' (n:=m)). all: eauto. lia.
  Qed.

  Lemma enum_term :
    list_enumerator__T L_term term.
  Proof with try (eapply cum_ge'; eauto; lia).
    intros t. induction t using term_rect.
    - exists (S x); cbn; eauto.
    - apply vec_forall_cml in H as [m H]. 2: exact L_term_cml. destruct (el_T F) as [m' H'].
      exists (S (m + m')); cbn. in_app 3. eapply in_concat_iff. eexists. split. 2: in_collect F...
      apply in_map. rewrite <- vecs_from_correct in H |-*. intros x H''. specialize (H x H'')...
  Qed.

  Lemma enumT_term :
    enumerable__T term.
  Proof.
    apply enum_enumT. exists L_term. apply enum_term.
  Qed.

  Fixpoint L_form {ff : falsity_flag} n : list form :=
    match n with
    | 0 => match ff with falsity_on => [falsity] | falsity_off => [] end
    | S n => L_form n
              ++ concat ([ [ atom P v | v ∈ vecs_from _ (L_term n) (ar_preds P) ] | P ∈ L_T n])
              ++ concat ([ [ bin op phi psi | (phi, psi) ∈ (L_form n × L_form n) ] | op ∈ L_T n])
              ++ concat ([ [ quant op phi | phi ∈ L_form n ] | op ∈ L_T n])
    end.

  Lemma L_form_cml {ff : falsity_flag} :
    cumulative L_form.
  Proof.
    intros ?; cbn; eauto.
  Qed.

  Lemma enum_form {ff : falsity_flag} :
    list_enumerator__T L_form form.
  Proof with (try eapply cum_ge'; eauto; lia).
    intros phi. induction phi.
    - exists 1. cbn; eauto.
    - rename t into v. destruct (el_T P) as [m Hm], (vec_forall_cml term L_term _ v) as [m' Hm']; eauto using enum_term.
      exists (S (m + m')); cbn. in_app 2. eapply in_concat_iff. eexists. split.
      2: in_collect P... eapply in_map. rewrite <- vecs_from_correct in *. intuition...
    - destruct (el_T b0) as [m Hm], IHphi1 as [m1], IHphi2 as [m2]. exists (1 + m + m1 + m2). cbn.
      in_app 3. apply in_concat. eexists. split. apply in_map... in_collect (pair phi1 phi2)...
    - destruct (el_T q) as [m Hm], IHphi as [m' Hm']. exists (1 + m + m'). cbn -[L_T].
      in_app 4. apply in_concat. eexists. split. apply in_map... in_collect phi...
  Qed.

  Lemma enumT_form {ff : falsity_flag} :
    enumerable__T form.
  Proof.
    apply enum_enumT. exists L_form. apply enum_form.
  Defined.

End Enumerability.
 
