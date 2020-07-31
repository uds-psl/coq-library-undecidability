Set Implicit Arguments.
Require Import List Omega Lia.
Import ListNotations.
From Undecidability.HOU Require Import std.std unification.unification calculus.calculus second_order.diophantine_equations.

(** * Higher-Order Motivation *)

(** ** Church Numerals *)
Section ChurchEncoding.
  Context {X: Const}.
  Implicit Type (n c: nat) (x y z: fin) (e: deq) (E: list deq).
  
  Definition enc n : exp X :=
    lambda lambda AppL (repeat (var 0) n) (var 1).

  Definition add (s t: exp X) :=
    lambda lambda (ren (shift >> shift) s)
      ((ren (shift >> shift) t) (var 1) (var 0)) (var 0).

  Definition mul (s t: exp X) :=
    lambda lambda (ren (shift >> shift) s) (var 1)
      (lambda ((ren (shift >> shift >> shift) t) (var 0) (var 1))).



  Section Substitution.
    Lemma enc_ren n delta:
      ren delta (enc n) = enc n.
    Proof.
      unfold enc. cbn. do 2 f_equal. asimpl.
      now rewrite repeated_map. 
    Qed.

    Lemma enc_subst n sigma:
      sigma • (enc n) = enc n.
    Proof.
      unfold enc. cbn. do 2 f_equal. asimpl.
      now rewrite repeated_map. 
    Qed.


    Lemma add_ren s t delta:
      ren delta (add s t) = add (ren delta s) (ren delta t).
    Proof. unfold add; asimpl; reflexivity. Qed.
    
    Lemma add_subst s t sigma:
      sigma • (add s t) = add (sigma • s) (sigma • t).
    Proof.
      unfold add; asimpl; cbn.
      do 4 f_equal. now asimpl.
      now asimpl.
    Qed. 

    Lemma mul_ren s t delta:
      ren delta (mul s t) = mul (ren delta s) (ren delta t).
    Proof. unfold mul; asimpl; reflexivity. Qed.
    
    Lemma mul_subst s t sigma:
      sigma • (mul s t) = mul (sigma • s) (sigma • t).
    Proof.
      unfold mul; asimpl; cbn.
      do 4 f_equal. now asimpl.
      now asimpl.
    Qed. 



  End Substitution.
  Hint Rewrite add_ren add_subst mul_ren mul_subst
       enc_ren enc_subst : asimpl.


  Lemma typing_enc Gamma n: Gamma ⊢(3) enc n : alpha → (alpha → alpha) → alpha.
  Proof.
    unfold enc. econstructor. econstructor.
    eapply AppL_ordertyping_repeated; eauto.
    eapply repeated_ordertyping; simplify; eauto.
    intros ? <- % repeated_in; eauto. 
  Qed.

  
  Lemma enc_app n s t:
    enc n s t ≡ AppL (repeat t n) s.
  Proof.
    unfold enc. do 2 (rewrite stepBeta; asimpl; cbn; eauto).
    now rewrite !repeated_map; cbn. 
  Qed.


  Lemma enc_zero s f: enc 0 s f ≡ s.
  Proof.
    now rewrite enc_app. 
  Qed.


  Lemma enc_succ n s f: enc (S n) s f ≡ f (enc n s f).
  Proof.
    now rewrite !enc_app. 
  Qed.

  Hint Rewrite enc_zero enc_succ : simplify.


  Lemma enc_eta n:
    enc n ≡ lambda lambda (enc n) (var 1) (var 0).
  Proof.
    now rewrite enc_app.
  Qed.



  Lemma enc_add' n m s f:
    enc (n + m) s f ≡ (enc n) (enc m s f) f.
  Proof.
    induction n; cbn; simplify; eauto.
    now rewrite IHn.
  Qed.

  Lemma enc_add n m:
    enc (n + m) ≡ add (enc n) (enc m).
  Proof.
    unfold add; rewrite enc_eta; asimpl.
    now rewrite enc_add'.
  Qed.


  Lemma enc_mul' n m s f:
    enc (n * m) s f ≡ (enc n) s (lambda (enc m (var 0) (ren shift f))).
  Proof.
    induction n; cbn.
    - now simplify. 
    - rewrite enc_add', IHn. simplify.
      rewrite stepBeta; asimpl; eauto.
  Qed.

   Lemma enc_mul n m:
    enc (n * m) ≡ mul (enc n) (enc m).
  Proof.
    unfold mul; rewrite enc_eta; asimpl.
    now rewrite enc_mul'. 
  Qed.


  Lemma enc_injective n m:
    enc n = enc m -> n = m.
  Proof.
    injection 1 as H.
    induction n in m, H |-*; destruct m; try discriminate; eauto.
    erewrite IHn; eauto.
    injection H; eauto.
  Qed.

  Lemma normal_enc n: normal (enc n).
  Proof.
    do 2 eapply normal_lam_intro.
    induction n; cbn; eauto.
  Qed.

  
  Hint Resolve normal_enc : core.


  Lemma enc_equiv_injective n m:
    enc n ≡ enc m -> n = m.
  Proof.
    intros ? % equiv_unique_normal_forms; eauto.
    eapply enc_injective; eauto.
  Qed.
  

  Lemma dec_enc s:
    { n | s = enc n} + forall n, s <> enc n.
  Proof with try (right; intros [] ?; discriminate).
    unfold enc. 
    destruct s...  
    destruct s...  
    enough ({ n | s = AppL (repeat (var 0) n) (var 1)} +
            forall n, s <> AppL (repeat (var 0) n) (var 1)).
    - destruct H; [left|right]; intuition.
      destruct s0 as [n]; exists n; now subst.
      injection H; eapply n; eauto. 
    - induction s...  
      + destruct f as [| []]...  
        left; now (exists 0).
      + destruct s1 as [[] | | |]...
        destruct IHs2 as [[n IHs2]|IHs2].
        * left. exists (S n). now subst.
        * right. intros []; try discriminate.
          cbn; injection 1; eapply IHs2.
  Qed.


End ChurchEncoding.
Hint Rewrite @add_ren @add_subst @mul_ren @mul_subst
       @enc_ren @enc_subst : asimpl.


(** ** Characteristic Equation *)
Lemma enc_characteristic X (s: exp X):
  normal s ->
  lambda lambda (var 0) ((ren (shift >> shift) s) (var 1) (var 0)) ≡
    lambda lambda (ren (shift >> shift) s) ((var 0) (var 1)) (var 0) ->
  exists n, s = enc n.
Proof.
  intros N; apply normal_nf in N as N'. induction N' as [k a t T _ _ isA ->].
  intros H'; Injection H'. clear H'. Injection H. clear H. rename H0 into H.
  asimpl in H. 
  destruct k as [|[|[]]]; cbn in H.
  - eapply equiv_app_elim in H; intuition.
    symmetry in H1; eapply equiv_neq_var_app in H1 as [].
    all: cbn; simplify; destruct a; cbn in isA; eauto.
  - do 2 (rewrite stepBeta in H; asimpl; eauto).
    eapply equiv_app_elim in H; intuition.
    symmetry in H1; eapply equiv_neq_var_app in H1 as [].
    all: cbn; simplify; destruct a as [[] | | |]; cbn in isA; eauto.  
  - rewrite <-AppR_subst in H. remember (AppR a T) as t. clear isA a T Heqt.
    do 4 (rewrite stepBeta in H; asimpl; cbn; asimpl; eauto).
    rewrite idSubst_exp in H; [|intros [|[]]; cbn; eauto].  eapply normal_Lambda in N.
    pose (sigma := @var X 0 .: var 0 (var 1) .: shift >> (shift >> var)). fold sigma in H.
    enough (exists n, t = AppL (repeat (var 0) n) (var 1)) as [n ->] by now (exists n).
    induction t as [[| [|]] | | |]; cbn in H; try solve [unfold funcomp in H; Discriminate].
    + exists 0; reflexivity.
    + eapply head_atom in N as isA; eauto. 
      eapply equiv_app_elim in H as [EQ1 EQ2]; eauto.
      2: eapply atom_head_lifting; eauto.
      2: intros [| [| []]]; cbn; eauto.
      destruct t1 as [[| [|]] | | |]; cbn in EQ1; try Discriminate.
      * mp IHt2; [eauto using normal_app_r|]. specialize (IHt2 EQ2). 
        destruct IHt2 as [n IHt2]; exists (S n); cbn; now rewrite IHt2.
      * unfold funcomp in EQ1; Injection EQ1. discriminate.
      * eapply equiv_neq_var_app in EQ1 as [].
        eapply atom_head_lifting; eauto.
        intros [| [| []]]; cbn; eauto.
  - repeat (rewrite stepBeta in H; cbn; asimpl; eauto).
    Discriminate. 
Qed.


Lemma church_commute X (s: exp X) n:
  s = enc n ->
  lambda lambda (var 0) ((ren (shift >> shift) s) (var 1) (var 0)) ≡
    lambda lambda (ren (shift >> shift) s) ((var 0) (var 1)) (var 0).
Proof.
  intros ->. asimpl. change (var 0 (var 1)) with (AppL (repeat (@var X 0) 1) (var 1)).
  rewrite !enc_app, <-AppL_app, <-repeated_plus; now simplify.
Qed.





(** ** Diophantine Equations Encoding *)
Section Encoding.

  Context {X: Const}.
  Implicit Type (n c: nat) (x y z: fin) (e: deq) (E: list deq).
  

  Definition varEQ x: eq X :=
    (lambda lambda (var 0) (var (S (S x)) (var 1) (var 0)), lambda lambda (var (S (S x))) ((var 0) (var 1)) (var 0)).

  Definition constEQ (x: nat): eq X :=
    (var x, enc 1).

  Definition addEQ (x y z: nat): eq X :=
    (add (var x) (var y), var z).

  Definition mulEQ (x y z: nat) : eq X :=
    (mul (var x) (var y), var z). 

  Definition eqs (e: deq) : eqs X :=
    match e with
    | x =ₑ 1 => [varEQ x; constEQ x]
    | x +ₑ y =ₑ z => [varEQ x; varEQ y; varEQ z; addEQ x y z]
    | x *ₑ y =ₑ z => [varEQ x; varEQ y; varEQ z; mulEQ x y z]
    end.

  Notation Eqs E := (flat_map eqs E). 

  Lemma in_Equations q E:
    q ∈ Eqs E <-> (exists e, e ∈ E /\ q ∈ eqs e).
  Proof.
    eapply in_flat_map.
  Qed.

  Section Typing.

    Variable (E: list deq).
    Hint Resolve Vars__de_in : core.

    Definition Gamma__dwk := repeat (alpha → (alpha → alpha) → alpha) (S (Sum (Vars__de E))).

    Lemma Gamma__dwk_nth x:
      x ∈ Vars__de E -> nth Gamma__dwk x = Some (alpha → (alpha → alpha) → alpha).
    Proof.
      intros H. unfold Gamma__dwk.
      eapply nth_error_repeated, le_n_S, Sum_in, H.
    Qed.

    Hint Resolve Gamma__dwk_nth : core.


    Lemma typing_varEQ x:
      x ∈ Vars__de E -> Gamma__dwk ⊢₂(3) varEQ x : alpha → (alpha → alpha) → alpha.
    Proof.  
      intros; unfold varEQ. split; cbn [fst snd].
      all: repeat match goal with [|- _ ⊢(_) _ : _] => econstructor end; try reflexivity.
      all: cbn; eauto. 
    Qed. 
    

    Lemma typing_constEQ x c:
      x =ₑ 1 ∈ E ->  Gamma__dwk ⊢₂(3) constEQ x : alpha → (alpha → alpha) → alpha. 
    Proof.
      intros; unfold constEQ.
      split; cbn [fst snd].
      + econstructor; eauto. 
        eapply Gamma__dwk_nth, Vars__de_in; eauto; cbn; intuition.
      + eapply typing_enc. 
    Qed.

    Lemma typing_addEQ x y z:
      x +ₑ y =ₑ z ∈ E -> Gamma__dwk ⊢₂(3) addEQ x y z : alpha → (alpha → alpha) → alpha. 
    Proof.
      intros; unfold addEQ.
      split; cbn [fst snd]; [| econstructor].
      repeat  match goal with [|- _ ⊢(_) _ : _] => econstructor end; try reflexivity. 
      all: try eapply Gamma__dwk_nth; eauto.
      all: eapply Vars__de_in; eauto; cbn; intuition.
    Qed.

    Lemma typing_mulEQ x y z:
      x *ₑ y =ₑ z ∈ E -> Gamma__dwk ⊢₂(3) mulEQ x y z : alpha → (alpha → alpha) → alpha.
    Proof.
      intros; unfold mulEQ.
      split; cbn [fst snd]; [| econstructor].
      repeat  match goal with [|- _ ⊢(_) _ : _] => econstructor end; try reflexivity.
      all: try eapply Gamma__dwk_nth; eauto.
      all: eapply Vars__de_in; eauto; cbn; intuition.
    Qed.


    Lemma typing_equations d e:
      e ∈ E -> d ∈ eqs e -> Gamma__dwk ⊢₂(3) d : alpha → (alpha → alpha) → alpha. 
    Proof.
      intros H H1; destruct e; cbn in H1; intuition; subst.
      all: eauto using typing_constEQ, typing_addEQ, typing_mulEQ. 
      all: eapply typing_varEQ, Vars__de_in; eauto; cbn; intuition.
    Qed. 

  End Typing.

End Encoding.
Hint Rewrite @enc_ren @enc_subst : asimpl.

Notation Eqs E := (flat_map eqs E). 


(** ** Reduction Function *)
Program Instance H10_to_DWK X (E: list deq): ordsysuni X 3 :=
  {
    Gamma₀' := Gamma__dwk E;
    E₀' := Eqs E;
    L₀' := repeat (alpha → (alpha → alpha) → alpha) (length (Eqs E));
    H₀' := _;
  }.
Next Obligation.
  eapply ordertyping_combine. all: unfold left_side, right_side.
  all:  eapply repeated_ordertyping; simplify; [|eauto].
  all: intros ? ?; mapinj;
    eapply in_Equations in H1 as [? []];eapply typing_equations; eauto.
Qed.


