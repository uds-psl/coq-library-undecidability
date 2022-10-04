(** ** Syntax Facts *)

From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation Shared.Dec.
Import ListAutomationNotations.

From Coq Require Import Eqdep_dec.
Require Import Coq.Vectors.Vector.
From Undecidability.Shared.Libs.PSL.Vectors Require Import Vectors VectorForall.
Require Import EqdepFacts.

Local Notation vec := t.

From Undecidability Require Export FOL.Syntax.Core.

Set Default Proof Using "Type".

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Section fix_signature.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

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

(*
  Definition size_rec {X:Type} (f : X -> nat) (P : X -> Type) :
    (forall x, (forall y, f y < f x -> P y) -> P x) -> forall x, P x.
  Proof.
  refine (fun H x => H x _).
  refine ((fix IH n y (H' : f y < n) : P y := _) (f x)).
  destruct n as [|n].
  - exfalso. eapply PeanoNat.Nat.nlt_0_r. apply H'.
  - destruct (nat_eq_dec (S (f y)) (S n)) as [Heq|Hne].
    + apply H. injection Heq. intros ->. apply IH.
    + apply (IH n). apply Lt.lt_n_Sm_le in H'. apply PeanoNat.Nat.le_lteq in H'. destruct H'. 1:easy. subst. exfalso. now apply Hne.
  Defined.

  Lemma size_rec_cbn {X} (f:X->nat) P H (x:X) : 
  (forall x Hf1 Hf2, (forall y (Hy1 : f y < f x), Hf1 y Hy1 = Hf2 y Hy1) -> H x Hf1 = H x Hf2) ->
    @size_rec X f P H x = H x (fun (y:X) _ => @size_rec X f P H y).
  Proof. unfold size_rec.
    induction (f x). in Hirrel|-*. ; intros y.
    - intros HC. exfalso. eapply PeanoNat.Nat.nlt_0_r. apply HC.
    - intros Hy1. destruct nat_eq_dec eqn:Heq.
      + apply Hirrel. intros y0 Hy0. assert (f y = n) as <- by lia. destruct f_equal. unfold eq_rect_r, eq_rect, eq_sym. f_equal.
      + rewrite IHn. apply Hirrel. intros y0 Hy0. f_equal.
  Qed.
*)
  Lemma subst_size {ff : falsity_flag} rho phi :
    size (subst_form rho phi) = size phi.
  Proof.
    revert rho; induction phi; intros rho; cbn; congruence.
  Qed.

  Lemma form_ind_subst' {ff : falsity_flag} :
    forall P : form -> Prop,
      (match ff return ((form Σ_funcs Σ_preds ops ff) -> Prop) -> Prop with 
      | falsity_off => fun _ => True
      | falsity_on => fun P' => P' falsity
      end) P ->
      (forall P0 (t : vec term (ar_preds P0)), P (atom P0 t)) ->
      (forall (b0 : binop) (f1 : form), P f1 -> forall f2 : form, P f2 -> P (bin b0 f1 f2)) ->
      (forall (q : quantop) (f2 : form), (forall sigma, P (subst_form sigma f2)) -> P (quant q f2)) ->
      forall (f4 : form), P f4.
  Proof.
    intros P H1 H2 H3 H4 phi. induction phi using (@size_ind _ size).
    destruct phi; cbn in *.
    - easy.
    - apply H2.
    - apply H3; apply H; lia.
    - apply H4. intros sigma. apply H. rewrite subst_size. econstructor.
  Qed.
(*

  Lemma form_rec_subst' {ff : falsity_flag} :
    forall P : form -> Type,
      (match ff return ((form Σ_funcs Σ_preds ops ff) -> Type) -> Type with 
      | falsity_off => fun _ => True
      | falsity_on => fun P' => P' falsity
      end) P ->
      (forall P0 (t : vec term (ar_preds P0)), P (atom P0 t)) ->
      (forall (b0 : binop) (f1 : form), P f1 -> forall f2 : form, P f2 -> P (bin b0 f1 f2)) ->
      (forall (q : quantop) (f2 : form), (forall sigma, P (subst_form sigma f2)) -> P (quant q f2)) ->
      forall (f4 : form), P f4.
  Proof.
    intros P H1 H2 H3 H4 phi. induction phi using (@size_rec _ size).
    destruct phi; cbn in *.
    - easy.
    - apply H2.
    - apply H3; apply X; apply Lt.le_lt_n_Sm. 1: apply Plus.le_plus_l. apply Plus.le_plus_r.
    - apply H4. intros sigma. apply X. rewrite subst_size. econstructor.
  Defined.

  Lemma form_rec_subst'_cbn_falsity P f1 f2 f3 f4: 
    (* forall q x H1 H2, (forall sigma, H1 sigma = H2 sigma) -> f4 q x H1 = f4 q x H2) -> *)
    @form_rec_subst' _ P f1 f2 f3 f4 falsity = f1.
  Proof.
    unfold form_rec_subst'. rewrite size_rec_cbn. 1:reflexivity. intros ? ? ? ?. destruct x. 1-3: repeat f_equal.
    + reflexivity.
    + apply Hirrel. intros sigma. apply H.
  Qed.

  Lemma form_rec_subst'_cbn_atom {ff} P f1 f2 f3 f4 p v: 
    (forall q x H1 H2, (forall sigma, H1 sigma = H2 sigma) -> f4 q x H1 = f4 q x H2) ->
    @form_rec_subst' ff P f1 f2 f3 f4 (atom p v) = f2 p v.
  Proof. intros Hirrel.
    unfold form_rec_subst'. rewrite size_rec_cbn. 1:reflexivity. intros ? ? ? ?. destruct x. 1-3: repeat f_equal.
    + reflexivity.
    + intros _ _. apply H.
    + intros _ _. apply H.
    + apply Hirrel. intros sigma. apply H.
  Qed.

  Lemma form_rec_subst'_cbn_bin {ff} P f1 f2 f3 f4 b phi psi: 
    (forall q x H1 H2, (forall sigma, H1 sigma = H2 sigma) -> f4 q x H1 = f4 q x H2) ->
    @form_rec_subst' ff P f1 f2 f3 f4 (bin b phi psi) =
    f3 b phi (@form_rec_subst' ff P f1 f2 f3 f4 phi) psi (@form_rec_subst' _ P f1 f2 f3 f4 psi).
  Proof. intros Hirrel.
    unfold form_rec_subst'. rewrite size_rec_cbn. 1:reflexivity. intros ? ? ? ?. destruct x. 1-3: repeat f_equal.
    + reflexivity.
    + intros _ _. apply H.
    + intros _ _. apply H.
    + apply Hirrel. intros sigma. apply H.
  Qed.

  Lemma form_rec_subst'_cbn_quant {ff} P f1 f2 f3 f4 q phi: 
    (forall q x H1 H2, (forall sigma, H1 sigma = H2 sigma) -> f4 q x H1 = f4 q x H2) ->
    @form_rec_subst' ff P f1 f2 f3 f4 (quant q phi) =
    f4 q phi (fun sigma => @form_rec_subst' ff P f1 f2 f3 f4 phi[sigma]).
  Proof. intros Hirrel.
    unfold form_rec_subst'. rewrite size_rec_cbn. 1:reflexivity. intros ? ? ? ?. destruct x. 1-3: repeat f_equal.
    + reflexivity.
    + intros _ _. apply H.
    + intros _ _. apply H.
    + apply Hirrel. intros sigma. apply H.
  Qed.
*)
  Lemma form_ind_subst :
    forall P : form -> Prop,
      P falsity ->
      (forall P0 (t : vec term (ar_preds P0)), P (atom P0 t)) ->
      (forall (b0 : binop) (f1 : form), P f1 -> forall f2 : form, P f2 -> P (bin b0 f1 f2)) ->
      (forall (q : quantop) (f2 : form), (forall sigma, P (subst_form sigma f2)) -> P (quant q f2)) ->
      forall (f4 : form), P f4.
  Proof.
    apply (form_ind_subst' (ff := falsity_on)).
  Qed.

  Lemma form_ind_falsity  (P : form falsity_on -> Prop) :
    P falsity ->
    (forall  (P0 : Σ_preds ) (t : t term (ar_preds P0)), P (atom P0 t)) ->
    (forall  (b0 : binop) (f1 : form), P f1 -> forall f2 : form, P f2 -> P (bin b0 f1 f2)) ->
    (forall (q : quantop) (f2 : form), P f2 -> P (quant q f2)) ->
    forall (f4 : form), P f4.
  Proof.
    intros H1 H2 H3 H4 phi.
    change ((fun ff => match ff with falsity_on => fun phi => P phi | _ => fun _ => True end) falsity_on phi).
    induction phi; try destruct b; [apply H1|easy| apply H2|easy|apply H3|easy|apply H4]. 1: apply IHphi1; assumption. 1: apply IHphi2; assumption. apply IHphi; assumption.
  Qed.

  Lemma form_ind_no_falsity  (P : form falsity_off -> Prop) :
    (forall  (P0 : Σ_preds ) (t : t term (ar_preds P0)), P (atom P0 t)) ->
    (forall  (b0 : binop) (f1 : form), P f1 -> forall f2 : form, P f2 -> P (bin b0 f1 f2)) ->
    (forall (q : quantop) (f2 : form), P f2 -> P (quant q f2)) ->
    forall (f4 : form), P f4.
  Proof.
    intros H2 H3 H4 phi.
    change ((fun ff => match ff with falsity_on => fun phi => True | _ => fun _ => P phi end) falsity_off phi).
    induction phi; try destruct b; [easy|apply H2|easy|apply H3|easy|apply H4|easy].
    1: apply IHphi1; assumption.
    1: apply IHphi2; assumption.
       apply IHphi; assumption.
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

  Lemma up_decompose {ff : falsity_flag} sigma phi :
    phi[up (S >> sigma)][(sigma 0)..] = phi[sigma].
  Proof.
    rewrite subst_comp. apply subst_ext.
    intros [].
    - reflexivity.
    - apply subst_term_shift.
  Qed.  
  
End Subst.



(* ** Bounded formulas *)


Global Ltac invert_bounds :=
  inversion 1; subst;
  repeat match goal with
           H : existT _ _ _ = existT _ _ _ |- _ => apply Eqdep_dec.inj_pair2_eq_dec in H; try decide equality
         end; subst.

Section Bounded.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Inductive bounded_t n : term -> Prop :=
  | bounded_var x : n > x -> bounded_t n $x
  | bouded_func f v : (forall t, Vector.In t v -> bounded_t n t) -> bounded_t n (func f v).

  Inductive bounded : forall {ff}, nat -> form ff -> Prop :=
  | bounded_atom ff n P v : (forall t, Vector.In t v -> @bounded_t n t) -> @bounded ff n (atom P v)
  | bounded_bin binop ff n phi psi : @bounded ff n phi -> @bounded ff n psi -> @bounded ff n (bin binop phi psi)
  | bounded_quant quantop ff n phi : @bounded ff (S n) phi -> @bounded ff n (quant quantop phi)
  | bounded_falsity n : @bounded falsity_on n falsity.

  Arguments bounded {_} _ _.

(*
  Fixpoint bounded_t_comp (n:nat) (t:term) : Prop := match t with
    var x => n > x
  | func f v => VectorDef.fold_right (fun x y => bounded_t_comp n x /\ y) v True end.

  Fixpoint bounded_comp  {ff} (n:nat) (phi : form ff) : Prop := match phi with
    falsity => True
  | atom P v => VectorDef.fold_right (fun x y => bounded_t_comp n x /\ y) v True
  | bin b phi psi => bounded_comp n phi /\ bounded_comp n psi
  | quant q phi => bounded_comp (S n) phi end.

  Lemma bounded_t_comp_correct n t : @bounded_t_comp n t <-> @bounded_t n t.
  Proof.
    induction t.
    - cbn; split. 1: intros H; now econstructor. now inversion 1.
    - cbn; split; intros H.
      + econstructor. induction v in IH,H|-*.
        * intros ? K. inversion K.
        * intros t [->|H2]%In_cons.
          -- cbn in H. apply IH. 1: now left. apply H.
          -- apply IHv. 
             { intros tt Htt. apply IH. now right. }  
             { apply H. }
             easy.
      + inversion H. apply inj_pair2_eq_dec in H2. 2: 
 cbn in H. destruct H as [Hl Hr].
          Search In cons. apply IHv.
  Lemma bounded_comp_eq {ff} n phi : @bounded_comp ff n phi <-> @bounded ff n phi.
*)
  Definition closed {ff:falsity_flag} phi := bounded 0 phi.

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

  Lemma bounded_t_0_subst t ρ :
    bounded_t 0 t -> t`[ρ] = t.
  Proof.
    intros Hb. rewrite <-subst_term_var.
    eapply bounded_subst_t.
    2: eassumption. lia.
  Qed.

  Lemma bounded_0_subst {ff : falsity_flag} φ ρ : bounded 0 φ -> φ[ρ] = φ.
  Proof.
    intros H. setoid_rewrite <-subst_var at 3. eapply bounded_subst.
    - eassumption.
    - lia.
  Qed.

  Lemma bounded_up_t {n t k} :
    bounded_t n t -> k >= n -> bounded_t k t.
  Proof using Σ_preds ops.
    induction 1; intros Hk; constructor; try lia. firstorder.
  Qed.

  Lemma bounded_up {ff : falsity_flag} {n phi k} :
    bounded n phi -> k >= n -> bounded k phi.
  Proof.
    induction 1 in k |- *; intros Hk; constructor; eauto.
    - intros t Ht. eapply bounded_up_t; eauto.
    - apply IHbounded. lia.
  Qed.

  Lemma In_inv {n} {t} {v : vec term n} :
    In t v ->
    (match n return vec term n -> Prop with
    | 0 => fun _ => False
    | S n => fun v' => (t = Vector.hd v') \/ (In t (Vector.tl v'))
    end) v.
  Proof. intros []; cbn; tauto. Qed.

  Lemma find_bounded_step n (v : vec term n) :
    (forall t : term, Vector_In2 t v -> {n : nat | bounded_t n t}) -> { n | forall t, In t v -> bounded_t n t }.
  Proof using Σ_preds ops.
    induction v; cbn; intros HV.
    - exists 0. intros t. inversion 1.
    - destruct IHv as [k Hk], (HV h) as [l Hl]; try left.
      + intros t Ht. apply HV. now right.
      + exists (k + l). intros t H.
        destruct (In_inv H) as [->|H'].
        * cbn. apply (bounded_up_t Hl). lia.
        * cbn in H'. apply (bounded_up_t (Hk t H')). lia.
  Qed.

  Lemma find_bounded_t t :
    { n | bounded_t n t }.
  Proof using Σ_preds ops.
    induction t using term_rect.
    - exists (S x). constructor. lia.
    - apply find_bounded_step in X as [n H]. exists n. now constructor.
  Qed.

  Lemma find_bounded {ff : falsity_flag} phi :
    { n | bounded n phi }.
  Proof.
    induction phi.
    - exists 0. constructor.
    - destruct (@find_bounded_step _ t) as [n Hn].
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

  Definition capture {ff:falsity_flag} (q:quantop) n phi := nat_rect _ phi (fun _ => quant q) n.

  Lemma capture_captures {ff:falsity_flag} n m l q phi :
    bounded n phi -> l >= n - m -> bounded l (capture q m phi).
  Proof.
    intros H Hl. induction m in l,Hl|-*; cbn. 
    - rewrite <- Minus.minus_n_O in *. now eapply (@bounded_up _ n).
    - constructor. eapply bounded_up; [apply IHm |]. 2: apply le_n. lia.
  Qed.

  Definition close {ff:falsity_flag} (q:quantop) phi := capture q (proj1_sig (find_bounded phi)) phi.

  Lemma close_closed {ff:falsity_flag} q phi :
    closed (close q phi).
  Proof.
    unfold close,closed. destruct (find_bounded phi) as [m Hm]; cbn.
    apply (capture_captures q Hm). lia.
  Qed.

  Lemma subst_up_var k x sigma :
    x < k -> (var x)`[iter up k sigma] = var x.
  Proof.
    induction k in x, sigma |-*.
    - now intros ?%PeanoNat.Nat.nlt_0_r.
    - intros H.
      destruct (Compare_dec.lt_eq_lt_dec x k) as [[| <-]|].
      + cbn [iter]. rewrite iter_switch. now apply IHk.
      + destruct x. reflexivity.
        change (iter _ _ _) with (up (iter up (S x) sigma)).
        change (var (S x)) with ((var x)`[↑]).
        rewrite up_term, IHk. reflexivity. constructor.
      + lia.
  Qed.
  
  Lemma subst_bounded_term t sigma k :
    bounded_t k t -> t`[iter up k sigma] = t.
  Proof.
    induction 1.
    - now apply subst_up_var.
    - cbn. f_equal.
      rewrite <-(Vector.map_id _ _ v) at 2.
      apply Vector.map_ext_in. auto.
  Qed.

  Lemma subst_bounded {ff : falsity_flag} k phi sigma :
    bounded k phi -> phi[iter up k sigma] = phi.
  Proof.
    induction 1 in sigma |-*; cbn.
    - f_equal.
      rewrite <-(Vector.map_id _ _ v) at 2.
      apply Vector.map_ext_in.
      intros t Ht. apply subst_bounded_term. auto.
    - now rewrite IHbounded1, IHbounded2.
    - f_equal.
      change (up _) with (iter up (S n) sigma).
      apply IHbounded.
    - reflexivity.
  Qed.

  Lemma subst_closed {ff : falsity_flag} phi sigma :
    closed phi -> phi[sigma] = phi.
  Proof.
    intros Hn.
    erewrite <- (@subst_id _ _ _ _ phi var) at 2. 2:easy.
    eapply bounded_subst. 1: apply Hn.
    lia.
  Qed.


  Lemma vec_cons_inv X n (v : Vector.t X n) x y :
    In y (Vector.cons X x n v) -> (y = x) \/ (In y v).
  Proof.
    inversion 1; subst.
    - now left.
    - apply (inj_pair2_eq_dec nat PeanoNat.Nat.eq_dec) in H3 as ->. now right.
  Qed.

  Lemma vec_all_dec X n (v : vec X n) (P : X -> Prop) :
    (forall x, Vector_In2 x v -> dec (P x)) -> dec (forall x, In x v -> P x).
  Proof.
    induction v; intros H.
    - left. intros x. inversion 1.
    - destruct (H h) as [H1|H1], IHv as [H2|H2]; try now left.
      + intros x Hx. apply H. now right.
      + intros x Hx. apply H. now right.
      + left. intros x [<-| Hx] % vec_cons_inv; intuition.
      + right. contradict H2. intros x Hx. apply H2. now right.
      + intros x Hx. apply H. now right.
      + right. contradict H1. apply H1. now left.
      + right. contradict H1. apply H1. now left.
  Qed.

  Context {sig_funcs_dec : eq_dec Σ_funcs}.
  Context {sig_preds_dec : eq_dec Σ_preds}.

  Lemma bounded_t_dec n t :
    dec (bounded_t n t).
  Proof using sig_funcs_dec.
    induction t.
    - destruct (Compare_dec.gt_dec n x) as [H|H].
      + left. now constructor.
      + right. inversion 1; subst. tauto.
    - apply vec_all_dec in X as [H|H].
      + left. now constructor.
      + right. inversion 1; subst. apply (inj_pair2_eq_dec _ sig_funcs_dec) in H3 as ->. tauto.
  Qed.

  Lemma bounded_dec {ff : falsity_flag} phi :
      forall n, dec (bounded n phi).
  Proof using sig_preds_dec sig_funcs_dec.
      induction phi; intros n.
      - left. constructor.
      - destruct (@vec_all_dec _ _ t (bounded_t n)) as [H|H].
        + intros t' _. apply bounded_t_dec.
        + left. now constructor.
        + right. inversion 1. apply (inj_pair2_eq_dec _ sig_preds_dec) in H5 as ->. tauto.
      - destruct (IHphi1 n) as [H|H], (IHphi2 n) as [H'|H'].
        2-4: right; invert_bounds; tauto.
        left. now constructor.
      - destruct (IHphi (S n)) as [H|H].
        + left. now constructor.
        + right. invert_bounds. tauto.
    Qed.

  Lemma bounded_S_quant {ff : falsity_flag} {q : quantop} N phi :
    bounded (S N) phi <-> bounded N (@quant _ _ _ _ q phi).
  Proof.
    split; intros H.
    - now constructor.
    - inversion H. apply Eqdep_dec.inj_pair2_eq_dec in H4 as ->; trivial.
      unfold Dec.dec. decide equality.
  Qed.

  Lemma subst_bounded_max_t {ff : falsity_flag} n m t sigma : 
    (forall i, i < n -> bounded_t m (sigma i)) -> bounded_t n t -> bounded_t m (t`[sigma]).
  Proof.
    intros Hi. induction 1 as [|? ? ? IH].
    - cbn. apply Hi. lia.
    - cbn. econstructor. intros t [x [<- Hx]]%vect_in_map_iff.
      now apply IH.
  Qed.

  Lemma subst_bounded_up_t {ff : falsity_flag} i m sigma : 
    (forall i', i' < i -> bounded_t m (sigma i')) -> bounded_t (S m) (up sigma i).
  Proof.
    intros Hb. unfold up,funcomp,scons. destruct i.
    - econstructor. lia.
    - eapply subst_bounded_max_t. 2: apply Hb. 2:lia.
      intros ii Hii. econstructor. lia.
  Qed.

  Lemma subst_bounded_max {ff : falsity_flag} n m phi sigma : 
    (forall i, i < n -> bounded_t m (sigma i)) -> bounded n phi -> bounded m (phi[sigma]).
  Proof. intros Hi.
    induction 1 as [ff n P v H| bo ff n phi psi H1 IH1 H2 IH2| qo ff n phi H1 IH1| n] in Hi,sigma,m|-*; cbn; econstructor.
    - intros t [x [<- Hx]]%vect_in_map_iff. eapply subst_bounded_max_t. 1: exact Hi. now apply H.
    - apply IH1. easy.
    - apply IH2. easy.
    - apply IH1. intros l Hl.
      apply subst_bounded_up_t. intros i' Hi'. apply Hi. lia.
  Qed.

End Bounded.

#[global] Arguments subst_bounded {_} {_} {_} {_} k phi sigma.

Ltac solve_bounds :=
  repeat (lia + constructor); try inversion X; intros;
  match goal with
  | H : Vector.In ?x (@Vector.cons _ ?y _ ?v) |- _ => repeat apply vec_cons_inv in H as [->|H]; try inversion H
  | H : Vector.In ?x (@Vector.nil _) |- _ => try inversion H
  | _ => idtac
  end.



(* ** Discreteness *)

Ltac resolve_existT := try
  match goal with
     | [ H2 : @existT ?X _ _ _ = existT _ _ _ |- _ ] => eapply Eqdep_dec.inj_pair2_eq_dec in H2;
                                                      [subst | try (eauto || now intros; decide equality)]
  end.

Lemma dec_vec_in X n (v : vec X n) :
  (forall x, Vector_In2 x v -> forall y, dec (x = y)) -> forall v', dec (v = v').
Proof with subst; try (now left + (right; intros[=])).
  intros Hv. induction v; intros v'.
  - pattern v'. apply Vector.case0...
  - apply (Vector.caseS' v'). clear v'. intros h0 v'.
    destruct (Hv h (vec_inB h v) h0)... edestruct IHv.
    + intros x H. apply Hv. now right.
    + left. f_equal. apply e.
    + right. intros H. inversion H. resolve_existT. tauto.
Qed.

#[global]
Instance dec_vec X {HX : eq_dec X} n : eq_dec (vec X n).
Proof.
  intros v. refine (dec_vec_in _).
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
  Proof with subst; try (now left + (right; intros[=]; resolve_existT; congruence))
    using eq_dec_Funcs.
    intros t. induction t as [ | ]; intros [|? v']...
    - decide (x = n)... 
    - decide (F = f)... destruct (dec_vec_in X v')...
  Qed.

  Instance dec_falsity : eq_dec falsity_flag.
  Proof.
    intros b b'. unfold dec. decide equality.
  Qed.

  Lemma eq_dep_falsity b phi psi :
    eq_dep falsity_flag (form Σ_funcs Σ_preds ops) b phi b psi <-> phi = psi.
  Proof.
    rewrite <- eq_sigT_iff_eq_dep. split.
    - intros H. resolve_existT. reflexivity.
    - intros ->. reflexivity.
  Qed.

  Lemma dec_form_dep {b1 b2} phi1 phi2 : dec (eq_dep falsity_flag (@form _ _ _) b1 phi1 b2 phi2).
  Proof with subst; try (now left + (right; intros ? % eq_sigT_iff_eq_dep; resolve_existT; congruence))
    using eq_dec_Funcs eq_dec_Preds eq_dec_quantop eq_dec_binop.
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
  Proof using eq_dec_Funcs eq_dec_Preds eq_dec_quantop eq_dec_binop.
    intros phi psi. destruct (dec_form_dep phi psi); rewrite eq_dep_falsity in *; firstorder.
  Qed.

  Lemma dec_full_logic_sym : eq_dec FullSyntax.full_logic_sym.
  Proof.
    cbv -[not]. decide equality.
  Qed.

  Lemma dec_full_logic_quant : eq_dec FullSyntax.full_logic_quant.
  Proof.
    cbv -[not]. decide equality.
  Qed.

  Lemma dec_frag_logic_binop : eq_dec FragmentSyntax.frag_logic_binop.
  Proof.
    cbv -[not]. decide equality.
  Qed.

  Lemma dec_frag_logic_quant : eq_dec FragmentSyntax.frag_logic_quant.
  Proof.
    cbv -[not]. decide equality.
  Qed.

  #[global] Existing Instance dec_full_logic_sym.
  #[global] Existing Instance dec_full_logic_quant.
  #[global] Existing Instance dec_frag_logic_binop.
  #[global] Existing Instance dec_frag_logic_quant.

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
    | S n => [ Vector.cons X x _ v | (x,  v) ∈ (A × @vecs_from X A n) ]
    end.


  Fixpoint L_term n : list term :=
    match n with
    | 0 => []
    | S n => L_term n ++ var n :: concat ([ [ func F v | v ∈ vecs_from (@L_term n) (ar_syms F) ] | F ∈ L_T n])
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
    (forall x, Vector_In2 x v -> x el A) <-> v el vecs_from A n.
  Proof.
    induction n; cbn.
    - split.
      + intros. left. pattern v. now apply Vector.case0.
      + intros [<- | []] x H. inv H.
    - split.
      + intros. revert H. apply (Vector.caseS' v).
        clear v. intros ? t0 H. in_collect (pair h t0); destruct (IHn t0).
        eauto using vec_inB. apply H0. intros x Hx. apply H. now right. 
      + intros Hv. apply in_map_iff in Hv as ([h v'] & <- & (? & ? & [= <- <-] & ? & ?) % list_prod_in).
        intros x H. inv H; destruct (IHn v'); eauto. apply H2; trivial. now resolve_existT.
  Qed.

  Lemma vec_forall_cml X (L : nat -> list X) n (v : vec X n) :
    cumulative L -> (forall x, Vector_In2 x v -> exists m, x el L m) -> exists m, v el vecs_from (L m) n.
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
  Proof using enum_Funcs'.
    apply enum_enumT. exists L_term. apply enum_term.
  Qed.

  Fixpoint L_form {ff : falsity_flag} n : list form :=
    match n with
    | 0 => match ff with falsity_on => [falsity] | falsity_off => [] end
    | S n => L_form n
              ++ concat ([ [ atom P v | v ∈ vecs_from (L_term n) (ar_preds P) ] | P ∈ L_T n])
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
    - rename t into v. destruct (el_T P) as [m Hm], (@vec_forall_cml term L_term _ v) as [m' Hm']; eauto using enum_term.
      exists (S (m + m')); cbn. in_app 2. eapply in_concat_iff. eexists. split.
      2: in_collect P... eapply in_map. rewrite <- vecs_from_correct in *. intuition...
    - destruct (el_T b0) as [m Hm], IHphi1 as [m1], IHphi2 as [m2]. exists (1 + m + m1 + m2). cbn.
      in_app 3. apply in_concat. eexists. split. apply in_map... in_collect (pair phi1 phi2)...
    - destruct (el_T q) as [m Hm], IHphi as [m' Hm']. exists (1 + m + m'). cbn -[L_T].
      in_app 4. apply in_concat. eexists. split. apply in_map... in_collect phi...
  Qed.

  Lemma enumT_form {ff : falsity_flag} :
    enumerable__T form.
  Proof using enum_Funcs' enum_Preds' enum_binop' enum_quantop'.
    apply enum_enumT. exists L_form. apply enum_form.
  Defined.

  Definition list_enumerator_full_logic_sym (n:nat) := [FullSyntax.Conj; FullSyntax.Disj; FullSyntax.Impl].
  Lemma enum_full_logic_sym : 
    list_enumerator__T list_enumerator_full_logic_sym FullSyntax.full_logic_sym.
  Proof.
    intros [| |]; exists 0; cbn; eauto.
  Qed.
  Lemma enumT_full_logic_sym : enumerable__T FullSyntax.full_logic_sym.
  Proof.
    apply enum_enumT. eexists. apply enum_full_logic_sym.
  Qed.

  Definition list_enumerator_full_logic_quant (n:nat) := [FullSyntax.All; FullSyntax.Ex].
  Lemma enum_full_logic_quant : 
    list_enumerator__T list_enumerator_full_logic_quant FullSyntax.full_logic_quant.
  Proof.
    intros [|]; exists 0; cbn; eauto.
  Qed.
  Lemma enumT_full_logic_quant : enumerable__T FullSyntax.full_logic_quant.
  Proof.
    apply enum_enumT. eexists. apply enum_full_logic_quant.
  Qed.

  Definition list_enumerator_frag_logic_binop (n:nat) := [FragmentSyntax.Impl].
  Lemma enum_frag_logic_binop : 
    list_enumerator__T list_enumerator_frag_logic_binop FragmentSyntax.frag_logic_binop.
  Proof.
    intros []; exists 0; cbn; eauto.
  Qed.
  Lemma enumT_frag_logic_binop : enumerable__T FragmentSyntax.frag_logic_binop.
  Proof.
    apply enum_enumT. eexists. apply enum_frag_logic_binop.
  Qed.

  Definition list_enumerator_frag_logic_quant (n:nat) := [FragmentSyntax.All].
  Lemma enum_frag_logic_quant : 
    list_enumerator__T list_enumerator_frag_logic_quant FragmentSyntax.frag_logic_quant.
  Proof.
    intros []; exists 0; cbn; eauto.
  Qed.
  Lemma enumT_frag_logic_quant : enumerable__T FragmentSyntax.frag_logic_quant.
  Proof.
    apply enum_enumT. eexists. apply enum_frag_logic_quant.
  Qed.

End Enumerability.

Definition enumT_form' {ff : falsity_flag} {Σ_funcs : funcs_signature} {Σ_preds : preds_signature} {ops : operators} :
  enumerable__T Σ_funcs -> enumerable__T Σ_preds -> enumerable__T binop -> enumerable__T quantop -> enumerable__T form.
Proof.
  intros. apply enum_enumT.
  apply enum_enumT in H as [L1 HL1].
  apply enum_enumT in H0 as [L2 HL2].
  apply enum_enumT in H1 as [L3 HL3].
  apply enum_enumT in H2 as [L4 HL4].
  exists (L_form HL1 HL2 HL3 HL4). apply enum_form.
Qed.

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
    - cbn. rewrite <- (@map_id _ _ v). f_equal. rewrite map_map. apply map_ext_forall, Forall_in.
      intros a Hva; now rewrite IH.
  Qed.

  Lemma func_subst_term_comp s rho t : func_subst_respects s -> t`[s/func]`[rho>>var] = t`[rho>>var]`[s/func].
  Proof.
  intros Hresp.
  induction t in s,rho,Hresp|-*.
  - easy.
  - cbn. rewrite Hresp. f_equal. rewrite ! map_map. apply map_ext_forall, Forall_in.
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
    - cbn. rewrite <- (@map_id _ _ t). f_equal. rewrite map_map. apply map_ext_forall, Forall_in.
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


