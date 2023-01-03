From Undecidability.FOL Require Import FullSyntax.
From Undecidability.FOL.Arithmetics Require Import Signature PA DeductionFacts.
From Undecidability.FOL.Syntax Require Import Theories.
From Undecidability.Shared Require Import ListAutomation.
From Undecidability.Synthetic Require Import ListEnumerabilityFacts.
From Undecidability.FOL.Tennenbaum Require Import MoreDecidabilityFacts Church Coding NumberUtils Formulas SyntheticInType Peano CantorPairing Tennenbaum_diagonal Tennenbaum_insep.

Require Import Lia.
Import Vector.VectorNotations.
(* Require Import FOL Peano Tarski Deduction NumberTheory Synthetic Enumerability DecidabilityFacts Formulas Tennenbaum_diagonal Tennenbaum_insep Makholm McCarty Church Coding. *)


Notation "⊨ phi" := (forall rho, rho ⊨ phi) (at level 21).

(** * Variants of Tennenbaum's theorem *)

(*  Statements are formatted rougly as follows:

    Lemma Name (Parameters) :
      Logical Assumptions ->
      Assumptions about the Model ->
      other Assumptions ->
      Conclusion.
    Proof. [...] Qed.
 *)


Module T.
Section Variants.
Instance ff : falsity_flag := falsity_on.
Context {Δ1 : Delta1}.

Variable D : Type.
Variable I : interp D.
Local Definition I' : interp D := extensional_model I.
Existing Instance I | 100.
Existing Instance I' | 0.

Variable axioms : forall ax, PA ax -> ⊨ ax.
Hypothesis ct : CT_Q.
Hypothesis delta1_definite : forall phi, delta1 phi -> Q ⊢I phi ∨ ¬ phi.
(* Definition obj_Insep := exists α β, def_obj_Insep α β. *)
  Notation "x 'i=' y"  := (@i_atom PA_funcs_signature PA_preds_signature D I Eq ([x ; y])) (at level 80).
  Notation "'iσ' x" := (@i_func PA_funcs_signature PA_preds_signature D I Succ ([x])) (at level 60).
  Notation "x 'i⊕' y" := (@i_func PA_funcs_signature PA_preds_signature D I Plus ([x ; y])) (at level 62).
  Notation "x 'i⊗' y" := (@i_func PA_funcs_signature PA_preds_signature D I Mult ([x ; y])) (at level 61).
  Notation "'i0'" := (i_func (Σ_funcs:=PA_funcs_signature) (f:=Zero) []) (at level 2) : PA_Notation.

Definition div e d := exists k : D, e i⊗ k = d.
Definition div_num n (d : D) := exists e, inu n i⊗ e = d.
Definition Div_nat (d : D) := fun n => div_num n d.
Definition div_pi ψ n a :=  (inu n .: (fun _ => a)) ⊨ (∃ (ψ ∧ ∃ $1 ⊗ $0 == $3)). 
Definition prime_form ψ := bounded 2 ψ /\ (forall x, Q ⊢I ∀ ψ[up (num x)..] ↔ $0 == num (Irred x) ).


(** CT_Q yields a formula for prime numbers. *)
Lemma Irred_repr :
  exists ψ, prime_form ψ.
Proof.
  destruct (ct Irred) as [phi Hphi].
  exists (∃ phi). split.
  - now constructor.
  - apply Hphi.
Qed.

Fact ψ_equiv n a ψ :
  prime_form ψ -> div_pi ψ n a <-> div_num (Irred n) a.
Proof.
  intros Hψ. unfold div_pi. cbn. split.
  - intros [d [HH H]]. unfold I' in HH. rewrite <- inu_I in HH. apply ψ_repr in HH; auto. subst d. apply H.
  - intros. exists (inu (Irred n)). unfold I'. rewrite <- !inu_I. rewrite ψ_repr; auto.
Qed.


Fact MP_Discrete_stable_std :
  MP -> Discrete D -> Stable std.
Proof.
  intros mp [eq]%Discrete_sum e. unfold Stable.
  refine (MP_Dec_stable mp _ _).
  constructor. intros ?; apply eq.
Qed.

Fact stable_Std :
  Stable std -> stable (forall e, std e).
Proof.
  intros H h ?. apply H.
  now apply (DN_chaining h), DN.
Qed.

Lemma Dec_Div_nat_std ψ :
  prime_form ψ -> forall e, std e -> Dec (Div_nat e).
Proof.
  intros Hψ e [n <-].
  constructor; intros x.
  destruct n.
  - left. exists (inu 0).
    now rewrite mult_zero_r.
  - destruct (dec_eq_nat (Mod x (S n)) 0) as [h|nh].
    + left. apply Mod_divides in h.
      destruct h as [k ->].
      exists (inu k). now rewrite inu_mult_hom, mult_comm.
    + right. intros [K HK]. apply nh.
      enough (exists k, inu k = K) as [k <-].
      * apply Mod_divides. exists k.
        unfold I' in HK. rewrite <- !inu_I in HK.
        rewrite mult_comm, <-inu_mult_hom in HK; auto.
        now apply inu_inj in HK; auto.
      * eapply std_mult'; eauto.
Qed.

Lemma Dec_div_reduction d ψ :
  prime_form ψ -> Dec (Div_nat d) -> Dec (fun n => div_pi ψ n d).
Proof.
  intros Hψ [H].
  constructor. intros n.
  destruct (H (Irred n)) as [h|nh].
  + left. apply ψ_equiv; auto.
  + right. intros [k ]%ψ_equiv; auto. apply nh.
    now exists k.
Qed.

Fact Std_is_Enumerable :
  (forall e, std e) -> Enumerable D.
Proof.
  intros H.
  exists (fun n => Some (inu n)).
  intros d. destruct (H d) as [n <-]; eauto.
Qed.


(* ** Variants of Tennenbaum's Theorem *)

(** ** Tennenbaum via diagonal proof *)
Theorem Tennenbaum1 :
  MP ->
  Discrete D ->
  Enumerable D <-> forall e, std e.
Proof.
  intros mp eq.
  destruct Irred_repr as [ψ ]; auto.
  split.
  - intros ?.
    assert (~~ forall e, std e) as He.
    { eapply Tennenbaum_diagonal with (ψ:=ψ); eauto. }
    intros e. apply MP_Discrete_stable_std; auto.
  - intros ?. now apply Std_is_Enumerable.
Qed.

Print Assumptions Tennenbaum1.

(** ** Tennenbaum via inseparable formulas *)
Corollary Tennenbaum_insep :
  MP ->
  Discrete D ->
  (forall d, ~~Dec (Div_nat d)) -> (forall e, ~~std e).
Proof.
  intros mp eq DecDiv e He.
  destruct Irred_repr as [ψ ]; auto.
  eapply nonDecDiv; eauto.
  - apply CT_Inseparable; auto.
    + eapply surj_form_. 4: apply enum_full_logic_quant. 3: apply enum_full_logic_sym.
      3: exact falsity.
      all: eapply enumerator__T_of_list. 1: apply enumerator_PA_funcs. 1: apply enumerator_PA_preds.
    + intros Φ. unfold enumerable.
      epose proof (enum_prv (enumerator__T_of_list enumerator_PA_funcs) (enumerator__T_of_list enumerator_PA_preds) PA_funcs_eq PA_preds_eq Qeq) as Henum.
      apply list_enumerator_enumerator in Henum.
      match type of Henum with (@enumerator _ ?H _) => pose H as fn end.
      unfold enumerator in Henum. eexists 
      (fun k => match Cantor.of_nat k with (k1,k2) => 
          match fn k1 with None => None 
              | Some k1' => if @dec_form PA_funcs_signature PA_preds_signature _ PA_funcs_eq PA_preds_eq _ _ falsity_on k1' (Φ k2) then Some k2 else None end end).
      intros x; split.
      * intros Hprv. apply Henum in Hprv. destruct Hprv as [n Hn]. exists (Cantor.to_nat (n,x)).
        rewrite Cantor.cancel_of_to. unfold fn; rewrite Hn. destruct dec_form; congruence.
      * intros [n Hn]. revert Hn. destruct (Cantor.of_nat n) as [k1 k2] eqn:Heq. destruct (fn k1) as [k1'|] eqn:Heq'; try congruence.
        destruct (dec_form); try congruence. subst. injection 1. intros ->. apply Henum. unfold fn in Heq'. eexists k1. apply Heq'.
  - now apply MP_Discrete_stable_std.
  - now exists e.
  - intros [d Hd]. apply (DecDiv d).
    intros h. apply Hd.
    now apply Dec_div_reduction.
Qed.

Print Assumptions Tennenbaum_insep.


Theorem Tennenbaum :
  MP ->
  Discrete D ->
  (forall d, ~~Dec (Div_nat d)) <-> (forall e, std e).
Proof.
  destruct Irred_repr as [ψ ].
  intros mp eq. split.
  - intros ??. apply MP_Discrete_stable_std; auto.
    eapply Tennenbaum_insep; eauto.
  - intros ??. eapply DN, Dec_Div_nat_std; eauto.
Qed.

Print Assumptions Tennenbaum.

(*
(** ** Makholm's Variant *)
Theorem Makholm :
  (exists ψ, prime_form ψ /\ (obj_Coding ψ)) -> obj_Insep -> 
  nonStd D <-> exists d, ~ Dec (Div_nat d).
Proof.
  intros [ψ [H1 H2]] ?. split.
  - eapply Makholm; eauto.
  - intros [d Hd]. exists d.
  now intros ?%(Dec_Div_nat_std _ H1).
Qed.

Corollary Makholm' :
  (exists ψ, prime_form ψ /\ (obj_Coding ψ)) -> obj_Insep ->
  (forall e, ~~std e) <-> (forall d, ~~ Dec (Div_nat d)).
Proof.
  intros H1 H2.
  specialize (Makholm H1 H2) as [m1 m2].
  split.
  - intros H d nH. destruct m2 as [e He%H]; [now exists d | auto].
  - intros H d nH. destruct m1 as [e He%H]; [now exists d | auto].
Qed.


Lemma Tennenbaum3 :
  (exists ψ, prime_form ψ /\ (obj_Coding ψ)) -> obj_Insep -> 
  (UC nat bool) -> ~ nonStd D.
Proof.
  intros ??? H.
  assert (nonStd D) as [e He]%Makholm by assumption; auto.
  refine (DN_Div_nat _ _ _ _ _ e _); auto.
Qed.

Lemma UC_Discrete :
  (forall X, UC X bool) -> Discrete D.
Proof.
  intros uc. unfold Discrete.
  apply UC_Def_Dec. apply uc.
  intros [x y]. destruct (@Peano.eq_dec D I axioms x y); now (left + right).
Qed.

(** ** McCarty's proof for the categoricity of HA. *)
Theorem McCarty :
  MP -> (forall X, UC X bool) ->
  (exists ψ, prime_form ψ /\ (obj_Coding ψ)) -> obj_Insep ->
  (forall e, std e).
Proof.
  intros ???? e.
  apply MP_Discrete_stable_std; auto.
  { now apply UC_Discrete. }
  intros He. apply Tennenbaum3; auto.
  now exists e.
Qed.
*)
End Variants.
End T.



(*  Below, we list all major results again in a way that makes
    all their assumptions explicit.
 *)

Definition PA_model D I := forall ax, PA ax -> forall rho, @sat _ _ D (extensional_model I) _ rho ax.

Theorem Tennenbaum {Δ1 : Delta1} D (I : interp D) :
 CT_Q -> MP ->
 PA_model I -> Discrete D ->
 (forall d, ~~Dec(T.Div_nat I d)) <-> (forall e, std e).
Proof.
  intros; now apply T.Tennenbaum.
Qed.
(*

Theorem Makholm  {Δ1 : Delta1} D (I : interp D) ψ :
  T.obj_Insep ->
  PA_model I ->
  T.prime_form ψ /\ obj_Coding ψ ->
  nonStd D -> exists d, ~ Dec (T.Div_nat D I d).
Proof.
  intros; eapply T.Makholm; eauto.
Qed.


Theorem Makholm' {Δ1 : Delta1} D (I : interp D) ψ :
  T.obj_Insep ->
  PA_model D I ->
  T.prime_form ψ /\ obj_Coding ψ ->
  (forall e, ~~std e) <-> (forall d, ~~Dec (T.Div_nat D I d)).
Proof.
  intros; eapply T.Makholm'; eauto.
Qed.


Lemma Tennenbaum3 {Δ1 : Delta1} D (I : interp D) ψ :
  (UC nat bool) -> T.obj_Insep ->
  PA_model D I ->
  T.prime_form ψ /\ (obj_Coding ψ) ->
  ~ nonStd D.
Proof.
  intros; eapply T.Tennenbaum3; eauto.
Qed.


Theorem McCarty {Δ1 : Delta1} D (I : interp D) ψ :
  MP -> (forall X, UC X bool) ->
  PA_model D I ->
  T.prime_form ψ /\ obj_Coding ψ -> T.obj_Insep -> 
  forall e, std e.
Proof.
  intros; eapply T.McCarty; eauto.
Qed.


*)


