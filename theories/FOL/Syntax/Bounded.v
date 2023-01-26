(* ** Bounded formulas *)

From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation Shared.Dec.
Import ListAutomationNotations.

From Coq Require Import Eqdep_dec PeanoNat.
Require Import Coq.Vectors.Vector.
From Undecidability.Shared.Libs.PSL.Vectors Require Import Vectors.
Require Import EqdepFacts.

Local Notation vec := t.

From Undecidability.FOL.Syntax Require Export Core Subst.


Local Set Implicit Arguments.
Local Unset Strict Implicit.


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
    (forall t : term, InT t v -> {n : nat | bounded_t n t}) -> { n | forall t, In t v -> bounded_t n t }.
  Proof using Σ_preds ops.
    induction v; cbn; intros HV.
    - exists 0. intros t. inversion 1.
    - destruct IHv as [k Hk], (HV h) as [l Hl]; try now left.
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
    - rewrite Nat.sub_0_r in *. now eapply (@bounded_up _ n).
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
    (forall x, InT x v -> dec (P x)) -> dec (forall x, In x v -> P x).
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

  Lemma vector_in_map {X Y:Type} (f : X -> Y) n (v : Vector.t X n) y : In y (map f v) -> exists x, In x v /\ f x = y.
  Proof.
    induction v; cbn; try easy.
    intros [-> | H]%vec_cons_inv. 1: exists h; split; eauto.
    1: eapply In_cons_hd.
    destruct (IHv H) as (x & H1 & H2). exists x.
    split; eauto. now eapply In_cons_tl.
  Qed.

  Lemma subst_bounded_max_t {ff : falsity_flag} n m t sigma : 
    (forall i, i < n -> bounded_t m (sigma i)) -> bounded_t n t -> bounded_t m (t`[sigma]).
  Proof.
    intros Hi. induction 1 as [|? ? ? IH].
    - cbn. apply Hi. lia.
    - cbn. econstructor. intros t [x [Hx <-]]%vector_in_map.
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
    - intros t [x [Hx <-]]%vector_in_map. eapply subst_bounded_max_t. 1: exact Hi. now apply H.
    - apply IH1. easy.
    - apply IH2. easy.
    - apply IH1. intros l Hl.
      apply subst_bounded_up_t. intros i' Hi'. apply Hi. lia.
  Qed.

  Fixpoint bounded_t_comp (n:nat) (t:term) : Prop := match t with
    var x => n > x
  | func f v => VectorDef.fold_right (fun x y => bounded_t_comp n x /\ y) v True end.

  Fixpoint bounded_comp  {ff} (n:nat) (phi : form ff) : Prop := match phi with
    falsity => True
  | atom P v => VectorDef.fold_right (fun x y => bounded_t_comp n x /\ y) v True
  | bin b phi psi => bounded_comp n phi /\ bounded_comp n psi
  | quant q phi => bounded_comp (S n) phi end.

  Lemma bounded_t_comp_correct n t : @bounded_t_comp n t <-> @bounded_t n t.
  Proof using sig_funcs_dec.
    induction t.
    - cbn; split. 1: intros H; now econstructor. now inversion 1.
    - cbn; split; intros H.
      + econstructor. induction v in IH,H|-*.
        * intros ? K. inversion K.
        * intros t [->|H2]%vec_cons_inv.
          -- cbn in H. apply IH. 1: now left. apply H.
          -- apply IHv. 
             { intros tt Htt. apply IH. now right. }  
             { apply H. }
             easy.
      + inversion H. apply inj_pair2_eq_dec in H2. 2: easy.
        subst. induction v in IH,H1|-*.
        * cbn. easy.
        * cbn. split. 1: apply IH; [now left|apply H1; now left].
          apply IHv. 1: intros t Ht; apply (IH t); now right.
          intros t Ht; apply H1; now right.
  Qed.
  Lemma bounded_comp_eq {ff} n phi : @bounded_comp ff n phi <-> @bounded ff n phi.
  Proof using sig_funcs_dec sig_preds_dec.
    induction phi in n|-*; cbn; (split; [intros H; econstructor|inversion 1; subst]).
    - easy.
    - induction t in H|-*; try easy.
      intros t' [->|Hin]%vec_cons_inv.
      + apply bounded_t_comp_correct. destruct H as [H1 H2]; apply H1.
      + apply IHt; try easy. destruct H as [H1 H2]; apply H2; easy.
    - apply inj_pair2_eq_dec in H4. 2: easy. subst.
      induction t in H3|-*; try easy.
      cbn. split.
      * apply bounded_t_comp_correct. apply H3. now left.
      * apply IHt. intros t' Ht'; apply H3. now right.
    - apply IHphi1. apply H.
    - apply IHphi2. apply H.
    - apply inj_pair2_eq_dec in H1. 2: decide equality.
      apply inj_pair2_eq_dec in H5. 2: decide equality.
      subst. split; try apply IHphi1; try apply IHphi2; easy.
    - now apply IHphi.
    - apply inj_pair2_eq_dec in H4. 2: decide equality.
      subst. apply IHphi. easy.
  Qed.

End Bounded.

#[global] Arguments subst_bounded {_} {_} {_} {_} k phi sigma.

Lemma vector_not_in_nil (X:Type) (x:X) (v : Vector.t X 0) : In x v -> False.
Proof.
  revert v. refine (case0 _ _). inversion 1.
Qed.

Ltac solve_bounds := let rec IH := match goal with
  |- bounded ?n ?H   => first [apply bounded_falsity; fail
                              |apply bounded_bin; [IH|IH]
                              |apply bounded_quant; [IH]
                              |apply bounded_atom; intros ?; IHvec]
| |- bounded_t ?n ?T => first [apply bounded_var; lia
                              |apply bouded_func; intros ?; IHvec]
| |- _ => idtac end
with IHvec := let H := fresh "H" in intros H;
                  first [exfalso; apply (@vector_not_in_nil _ _ _ H)
                        |apply vec_cons_inv in H; destruct H as [->|H];
                          [IH
                          |revert H; try IHvec]]
in IH.
