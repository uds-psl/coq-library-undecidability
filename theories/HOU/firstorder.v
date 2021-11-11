Set Implicit Arguments.

From Equations Require Import Equations.
Require Import List Lia Arith Wf Morphisms Program.Program.
From Undecidability.HOU Require Import unification.unification concon.conservativity calculus.calculus.
Import ListNotations.

Tactic Notation "simplify" := Undecidability.HOU.std.tactics.simplify.  

Set Default Proof Using "Type".

(* * First-Order Unification *)

(* ** Singlepoint Substitution *)
Section Update.

  Context {X: Const}.

  Definition update x v (sigma: fin -> exp X) :=
    fun y => if x == y then v else sigma y.

  Lemma singlepoint_subst_vars x s t: vars (update x s var • t) ⊆ vars s ++ vars t.
  Proof.
    intros ? (y & H1 & H2) % vars_varof % varof_subst.
    unfold update in *; destruct eq_dec; subst.
    eapply varof_vars in H2; simplify; eauto.  
    inv H2. eapply varof_vars in H1; simplify; eauto. 
  Qed.


  Lemma singlepoint_subst_vars_variable x s t:
    x ∈ vars (update x s var • t) -> x ∈ vars s /\ x ∈ vars t.
  Proof.
    intros (y & ? & ?) % vars_varof % varof_subst.
    unfold update in *; destruct eq_dec; subst; split; eauto using varof_vars.
    all: exfalso; inv H0; intuition.
  Qed.
  
  
  Lemma singlepoint_subst_Vars' x s E: Vars' (update x s var •₊₊ E) ⊆ vars s ++ Vars' E.
  Proof.
    induction E as [|[u v]]; [cbn; easy|]; simplify.
    cbn; rewrite !singlepoint_subst_vars, IHE, <-!app_assoc.
    repeat eapply incl_app_build. all:eauto using incl_refl,incl_appr,incl_appl.
  Qed.


  Lemma singlepoint_subst_Vars'_variable x s E:
    x ∈ Vars' (update x s var •₊₊ E) -> x ∈ vars s /\ x ∈ Vars' E.
  Proof.
    induction E as [|[u v]]; [cbn; intuition|]; simplify.
    cbn; simplify;
      intros [[H % singlepoint_subst_vars_variable | H % singlepoint_subst_vars_variable] | H].
    all:tauto.
  Qed.


  Lemma update_irrelevant x s t sigma:
    ~ x ∈ vars t -> update x s sigma • t = sigma • t.
  Proof.
    intros H; eapply subst_extensional; intros y.  
    unfold update; destruct eq_dec; subst; intuition.
  Qed.


  Lemma update_typing n Delta Gamma sigma (s: exp X) x A:
    Delta ⊩(n) sigma : Gamma -> Delta ⊢(n) s : A -> nth Gamma x = Some A -> Delta ⊩(n) update x s sigma : Gamma.
  Proof.
    intros ??????; unfold update; destruct eq_dec; subst; eauto; congruence.
  Qed.

End Update.


(* ** Lambda-Freeness *)
Section LambdaFreeness.

  Context {X: Const}.

  Inductive lambda_free : exp X -> Prop :=
  | lambda_free_var x: lambda_free (var x)
  | lambda_free_const c: lambda_free (const c)
  | lambda_free_app s t: lambda_free s -> lambda_free t -> lambda_free (s t).


  Lemma lambda_free_AppR s T:
    lambda_free s -> (forall t, t ∈ T -> lambda_free t) -> lambda_free (AppR s T).
  Proof.
    induction T; cbn; intuition (econstructor; eauto).
  Qed.

  Lemma ordertyping_one_atom Gamma (s: exp X) A:
    Gamma ⊢ s : A -> nf s -> ord A <= 1 -> isAtom (head s).
  Proof.
    destruct 2; subst; intros.
    destruct k; cbn; simplify; eauto.
    inv H. now eapply ord_arr_one in H0.
  Qed.

  Lemma order_one_lambda_free Gamma s A:
    normal s ->
    (Gamma ⊢(1) s : A) ->
    isAtom (head s) -> lambda_free s.
  Proof.
    intros N % normal_nf. induction N in Gamma, A |-*; subst.
    destruct k; cbn;[intros|easy].
    simplify in H1. eapply lambda_free_AppR.
    - destruct s; cbn in i; intuition econstructor.
    - eapply AppR_ordertyping_inv in H0 as H4; destruct H4 as [L H4].
      intuition. assert (ord' L <= 1).
      + destruct s; cbn in i. 3-4:intuition.
        * inv H3. simplify in H6. lia. 
        * inv H3. rewrite H6 in H7.
          simplify in H7. lia.
      + eapply orderlisttyping_element in H2 as [B []]. 2:now eauto.
        eapply H; eauto.
        eapply ordertyping_one_atom; eauto.
        eapply ord'_elements; eauto.
  Qed.


  Lemma lambda_free_subst Delta (sigma: fin -> exp X) x A:
    (Delta ⊢(1) sigma x : A) -> ord A <= 1 ->
    normal (sigma x) -> lambda_free (sigma x).
  Proof.
    intros H1  H3 H4; eapply order_one_lambda_free; eauto.
    eapply head_atom; eauto.
    destruct sigma; cbn; intuition.
    inv H1. eapply ord_arr_one; eauto.
  Qed.


  Lemma lambda_free_not_lam s:
    lambda_free s -> ~ isLam s.
  Proof.
    destruct 1; cbn; intuition.
  Qed.


  Lemma lambda_free_substitution sigma s:
    lambda_free s -> (forall x, x ∈ vars s -> lambda_free (sigma x)) -> lambda_free (sigma • s).
  Proof.
    induction 1; cbn; eauto using lambda_free.
    intros; econstructor; eauto;
      [eapply IHlambda_free1 | eapply IHlambda_free2]; intuition.
  Qed.
  
  Lemma lambda_free_subst_eqs sigma E:
    (forall x, x ∈ Vars' E -> lambda_free (sigma x)) -> all_terms lambda_free E -> all_terms lambda_free (sigma •₊₊ E).
  Proof.
    intros H; induction E as [| [s t]]; cbn; eauto; simplify; cbn in *.
    intros (H1 & H2 & H3). split; [|split]. 
    1 - 2: eapply lambda_free_substitution; eauto; intros; eapply H; intuition.
    eapply IHE; eauto; intuition; eapply H; intuition.
  Qed.
  
  Lemma lambda_free_normal s:
    lambda_free s -> normal s.
  Proof.
    induction 1; [ eauto.. |].
    eapply normal_app_intro; eauto.
    inv H; intuition.
  Qed.

End LambdaFreeness.

(* ** Simplified First-Order Unification *)
Local Hint Constructors lambda_free : core. 
Section Unification.

  Variable (X: Const).
  Implicit Types (Gamma: ctx) (n: nat) (sigma tau: fin -> exp X) (s t: exp X)
           (E: list (exp X * exp X)).

  Variable (free: fin -> Prop) (isFree: Dec1 free).
  Definition bound x := ~ free x.

  Definition free' sigma :=
    (forall x, bound x -> sigma x = var x) /\
    (forall x, free x -> forall y, y ∈ vars (sigma x) -> free y).

  (* *** Term Decompositon *)
  Section Decomposition.
    
    Fixpoint decomp s t: option (eqs X) :=
      if s == t then Some nil
      else match s, t with
           | var x, t => Some [(var x, t)]
           | s, var x => Some [(var x, s)]
           | app s1 s2, app t1 t2 =>
             match decomp s1 t1, decomp s2 t2 with
             | Some E1, Some E2 => Some (E1 ++ E2)
             |  _, _ => None
             end
           | _, _ => None
           end.


    Fixpoint decomp' E :=
      match E with
      | nil => Some nil
      | e :: E => match decomp (fst e) (snd e),  decomp' E with
                 | Some E1, Some E2 => Some (E1 ++ E2)
                 | _, _ => None
                 end
      end.


    Lemma decomp_some_ind (P: exp X -> exp X -> eqs X -> Type):
      (forall s, P s s nil) ->
      (forall x s, var x <> s -> P (var x) s [(var x, s)]) ->
      (forall x s, var x <> s -> P s (var x) [(var x, s)]) ->
      (forall s1 s2 t1 t2 E1 E2, s1 s2 <> t1 t2 ->
                            decomp s1 t1 = Some E1 -> P s1 t1 E1 ->
                            decomp s2 t2 = Some E2 -> P s2 t2 E2 ->
                            P (s1 s2) (t1 t2) (E1 ++ E2)) ->
      forall s t E, decomp s t = Some E -> P s t E.
    Proof.
      intros H1 H2 H3; induction s; intros [] E; cbn.
      all: destruct eq_dec as [EQ|NEQ]; try discriminate.
      1 - 11: injection 1 as ?; subst E; eauto.
      1 - 4: injection EQ; intros; subst; eauto.
      destruct (decomp s1 e) eqn: EQ1; try discriminate.
      destruct (decomp s2 e0) eqn: EQ2; try discriminate.
      injection 1 as ?; subst.
      eapply X0; eauto.
    Qed.



    Lemma decomp_none_ind (P: exp X -> exp X -> Type):
      (forall x t, const x <> t -> ~ isVar t -> P (const x) t) ->
      (forall x t, const x <> t -> ~ isVar t -> P t (const x)) ->
      (forall s t, lambda s <> t -> P (lambda s) t) ->
      (forall s t, s <> lambda t -> P s (lambda t)) ->
      (forall s1 s2 t1 t2, s1 s2 <> t1 t2 -> P s1 t1 -> P (s1 s2) (t1 t2)) ->
      (forall s1 s2 t1 t2, s1 s2 <> t1 t2 -> P s2 t2 -> P (s1 s2) (t1 t2)) ->
      forall s t, decomp s t = None -> P s t.
    Proof.
      intros H1 H2 H3 H4 IH1 IH2 s t; induction s in t |-*; cbn.
      all: destruct eq_dec; try discriminate.
      all: destruct t; try discriminate; eauto.
      destruct decomp eqn: D1; [destruct (decomp s2 t2) eqn: D2|];
        try discriminate.
      all: intros _; eauto.
    Qed.



    Lemma decomp'_some_ind (P: eqs X -> eqs X -> Prop):
      P nil nil ->
      (forall s t E E1 E2, decomp s t = Some E1 ->
                      decomp' E = Some E2 -> P E E2 -> P ((s, t) :: E) (E1 ++ E2)) ->
      forall E E', decomp' E = Some E' -> P E E'.
    Proof.
      intros H IH; induction E as [| [s t]]; cbn.
      - now injection 1 as <-.
      - intros E'; destruct decomp eqn: H1;
          destruct decomp' eqn: H2; try discriminate.
        intros [= <-]; eauto.
    Qed.


    Lemma decomp'_none_ind (P: eqs X -> Type):
      (forall E s t, decomp s t = None -> P ((s, t) :: E)) ->
      (forall E s t, P E -> P ((s, t) :: E)) -> 
      forall E, decomp' E = None -> P E.
    Proof.
      intros H IH; induction E as [| [s t]]; cbn; try discriminate.
      destruct decomp eqn: EQ1; [destruct decomp' eqn: EQ2 |]; try discriminate.
      all: intros _.  eapply IH; intuition. eapply H; intuition.
    Qed.

    Ltac decomp_ind :=
      match goal with
      | [|- decomp ?s ?t = Some ?E -> _] =>
        intros H; pattern s, t, E; eapply decomp_some_ind; [idtac..|eapply H]; clear s t E H
      | [|- decomp ?s ?t = None -> _] =>
        intros H; pattern s, t; eapply decomp_none_ind; [idtac..|eapply H]; clear s t H
      | [|- decomp' ?E = Some ?E' -> _] =>
        intros H; pattern E, E'; eapply decomp'_some_ind; [idtac..|eapply H]; clear E E' H
      | [|- decomp' ?E = None -> _] =>
        intros H; pattern E; eapply decomp'_none_ind; [idtac..|eapply H]; clear E H
      end.



    Lemma decomp_some_head_consts s t E x y:
      decomp s t = Some E -> head s = const x -> head t = const y -> x = y.
    Proof.
      decomp_ind; eauto.  
      all: cbn in *; congruence. 
    Qed.


    Lemma decomp_typing s t E Gamma:
      decomp s t = Some E ->
      forall A, lambda_free s -> lambda_free t ->
           (Gamma ⊢(1) s : A) -> (Gamma ⊢(1) t : A) ->
           exists L, Gamma ⊢₊₊(1) E : L.
    Proof.
      decomp_ind; intros.
      - exists nil; econstructor. 
      - exists [A]; eauto using eqs_ordertyping. 
      - exists [A]; eauto using eqs_ordertyping.  
      - inv H4. inv H5. inv H6. inv H7.
        enough (A0 → A = A1 → A) as H4. injection H4 as ->.
        edestruct H1 as [L1]; eauto. edestruct H3 as [L2]; eauto.
        exists (L1 ++ L2). eapply ordertyping_combine; unfold left_side, right_side; simplify.
        1 - 2: eapply orderlisttyping_app; try eapply left_ordertyping;
          try eapply right_ordertyping; eauto.
        eapply lambda_free_normal in H10 as H10'; eapply lambda_free_not_lam in H10 as H10''.
        eapply lambda_free_normal in H9 as H9'; eapply lambda_free_not_lam in H9 as H9''.
        eapply head_atom in H10' as H10'''; eauto. eapply head_atom in H9' as H9'''; eauto.
        destruct (head_decompose s1) as [S1].  destruct (head_decompose t1) as [T1].
        destruct (head s1); cbn in *;[  | | now intuition..];[| destruct (head t1)]; cbn in *. 4,5:now intuition.
        1: subst s1; eapply AppR_ordertyping_inv in H8 as (L & ? & V); inv V.
        2: subst t1; eapply AppR_ordertyping_inv in H6 as (L & ? & V); inv V.
        1: rewrite ord_Arr in H8; eapply Nat.max_lub_r, ord_arr_one in H8 as [].
        1: rewrite ord_Arr in H7; eapply Nat.max_lub_r, ord_arr_one in H7 as [].
        eapply decomp_some_head_consts in H0; subst; simplify; cbn; eauto. subst.
        eapply AppR_ordertyping_inv in H8 as (L1 & ? & ?).
        eapply AppR_ordertyping_inv in H6 as (L2 & ? & ?).
        inv H4. inv H6. rewrite H7 in H8. 
        change (A0 → A) with (Arr [A0] A) in H8. change (A1 → A) with (Arr [A1] A) in H8.
        rewrite <-!Arr_app in H8. eapply Arr_left_injective in H8.
        eapply app_injective_right in H8. 2:now intuition. intuition congruence. 
    Qed.


    Lemma decomp_lambda_free s t E:
      decomp s t = Some E ->  lambda_free s -> lambda_free t -> all_terms (@lambda_free X) E.
    Proof.
      decomp_ind; intros; eauto; simplify; cbn; eauto using all_terms_nil.
      inv H4; inv H5; intuition. 
    Qed.




    Lemma decomp'_typing Gamma E E':
      decomp' E = Some E' ->
      forall L, all_terms (@lambda_free X) E ->
           Gamma ⊢₊₊(1) E : L -> exists L,  Gamma ⊢₊₊(1) E' : L.
    Proof.
      decomp_ind; eauto.  
      intros s t E E1 E2 H H' IH L LF T. inv T. simplify in LF; intuition.
      eapply decomp_typing in H as [L1]; eauto.
      edestruct IH as [L2]; eauto. 
      exists (L1 ++ L2). eapply ordertyping_combine; unfold left_side, right_side; simplify.
      1 - 2: eapply orderlisttyping_app; try eapply left_ordertyping; try eapply right_ordertyping.
      all: eauto.
    Qed.



    Lemma decomp'_lambda_free E E':
      decomp' E = Some E' ->  all_terms (@lambda_free X) E -> all_terms (@lambda_free X) E'.
    Proof.
      decomp_ind; intros; eauto; simplify in *; intuition.  
      eapply decomp_lambda_free in H; firstorder.
    Qed.


    Lemma vars_decomp s t E:
      decomp s t = Some E -> Vars' E ⊆ vars s ++ vars t.
    Proof.
      decomp_ind; cbn; intros; simplify. 1-2:easy. now intros ? [->|];eauto using in_or_app,in_eq.  
      rewrite H1, H3. (repeat eapply incl_app_build); intros ?; simplify. all:tauto. 
    Qed.


    Lemma Vars_decomp' E E':
      decomp' E = Some E' -> Vars' E' ⊆ Vars' E.
    Proof.
      decomp_ind. easy. intros. simplify.
      now rewrite H1, vars_decomp; eauto. 
    Qed.

  End Decomposition.

  Ltac decomp_ind :=
    match goal with
    | [|- decomp ?s ?t = Some ?E -> _] =>
      intros H; pattern s, t, E; eapply decomp_some_ind; [idtac..|eapply H]; clear s t E H
    | [|- decomp ?s ?t = None -> _] =>
      intros H; pattern s, t; eapply decomp_none_ind; [idtac..|eapply H]; clear s t H
    | [|- decomp' ?E = Some ?E' -> _] =>
      intros H; pattern E, E'; eapply decomp'_some_ind; [idtac..|eapply H]; clear E E' H
    | [|- decomp' ?E = None -> _] =>
      intros H; pattern E; eapply decomp'_none_ind; [idtac..|eapply H]; clear E H
    end.





  (* *** Unification Relation *)
  Reserved Notation "E ↦ sigma" (at level 80).

  Inductive unify E: (fin -> exp X) -> Prop :=
  | unifyId: decomp' E = Some nil -> E ↦ var
  | unifyStep x s E' sigma: 
      decomp' E = Some ((var x, s) :: E') ->
      free x -> (forall y, y ∈ vars s -> free y) ->
      update x s var •₊₊ E' ↦ sigma ->
      ~ x ∈ vars s ->
      E ↦ update x (sigma • s) sigma
  where "E ↦ sigma" := (unify E sigma).

  (* *** Computability *)
  Section Computability.

    Definition subvars := MR strict_incl (@Vars' X).

    Instance wf_subvars : WellFounded subvars.
    Proof. eapply measure_wf, wf_strict_incl, eq_dec. Qed.

    Notation "( a ; b )" := (exist _ a b).

    Definition remember Y (x : Y) : {y | x = y}.
    Proof.
      exists x. reflexivity.
    Qed.      

    Lemma unif (E: list (exp X * exp X)) : { sigma | E ↦ sigma } + ({ sigma | E ↦ sigma } -> False).
    Proof using isFree.
      pattern E. revert E. apply (well_founded_induction_type wf_subvars).
      intros E unif. destruct (decomp' E) as [[|[[x| | |] s] E']|] eqn:H.
      1: left; exists var; now econstructor.
      2-5: right; intros [σ H']; inv H'; congruence.
      destruct (x el vars s) as [?|?].
      { right; intros [σ H']; inv H'; congruence. }
      destruct (isFree x) as [?|?].
      2: { right; intros [σ H']; inv H'; congruence. }
      destruct (dec_all isFree (vars s)) as [?|?].
      2: { right. intros [σ H']; inv H'; [congruence|].
           rewrite H in H0. inv H0; eauto. }
      (* case ~ x ∈ vars s, free x, forall x : fin, x ∈ vars s -> free x *)
      destruct (unif [subst_eq (update x s var) p | p ∈ E']) as [[sigma IH]|IH].
      { unfold subvars, MR. eapply Vars_decomp' in H.
        split.
        + rewrite singlepoint_subst_Vars'. cbn in H. lauto.
        + exists x. split. cbn in H; lauto. intros ? % singlepoint_subst_Vars'_variable.
          intuition. }
      - left. exists (update x (sigma • s) sigma).
        econstructor; eauto. 
      - right; intros [σ H']; inv H'; [congruence|].
        rewrite H in H0. inv H0. eauto.
    Qed.

   (* Bug in Equations?
      Global Obligation Tactic := idtac.
      Equations? unif (E: list (exp X * exp X)) : { sigma | E ↦ sigma } + ({ sigma | E ↦ sigma } -> False) by wf E subvars :=
      unif E1 with remember (decomp' E1) => {
        unif E2 (Some nil ; H) := inl (var ; _) ;
        unif E3 (Some ((var x1, s1) :: E') ; H)
          with (x1 el vars s1, isFree x1, dec_all isFree (vars s1)) => {
          unif E4 (Some ((var x2, s2) :: E'') ; H') (right H1, left H2, left H3)
            with (unif (update x2 s2 var •₊₊ E'')) => {
            unif E5 (Some ((var x3, s3) :: E') ; H'') (right H1', left H2', left H3') (inl (sigma1;HH))
            := inl (update x3 (sigma1 • s3) sigma1 ; _);
            unif a b c d := inr _
          };
          unif E5 a1 b1 := inr _
        };
        unif E6 a2 => inr _
      }.
    Proof.
      all: try now intros [σ H]; inv H; intuition congruence.
      - now econstructor.
      - unfold subvars, MR. eapply Vars_decomp' in H.
        split.
        + rewrite singlepoint_subst_Vars'. cbn in H. lauto.
        + exists x. split. cbn in H; lauto. intros ? % singlepoint_subst_Vars'_variable.
          intuition.
      - econstructor; eauto.
      - intros [σ H]; inv H.  intuition congruence.
        rewrite unknown0 in H0. inv H0; eauto.
      - intros [σ H]; inv H. congruence.
        rewrite unknown0 in H0. inv H0; eauto.
    Qed. *)
    
  End Computability.


  Section Unifiability.
    
    Definition unifies sigma s t := sigma • s = sigma • t.
    Definition Unifies sigma E := forall e, e ∈ E -> unifies sigma (fst e) (snd e).
    
    Global Instance unifies_equiv sigma: Equivalence (unifies sigma).
    Proof.
      constructor; unfold unifies; congruence.
    Qed.

    Lemma Unifies_cons sigma e E:
      Unifies sigma (e :: E) <-> unifies sigma (fst e) (snd e) /\ Unifies sigma E.
    Proof.
      unfold Unifies; cbn in *; intuition (subst; intuition).
    Qed.
    
    Lemma Unifies_nil sigma: Unifies sigma nil.
    Proof. intros ? []. Qed.


    Hint Rewrite Unifies_cons : simplify.
    Hint Resolve Unifies_nil : core.

    Lemma Unifies_app sigma E1 E2:
      Unifies sigma (E1 ++ E2) <-> Unifies sigma E1 /\ Unifies sigma E2.
    Proof.
      induction E1; cbn; simplify; intuition.
    Qed.

    Hint Rewrite Unifies_app : simplify.

    Definition equi_unifiable (E1 E2: eqs X) :=
      forall sigma, Unifies sigma E1 <-> Unifies sigma E2.

    Notation "E1 ≈ E2" := (equi_unifiable E1 E2) (at level 80).


    Global Instance equi_unifiable_equivalence: Equivalence equi_unifiable.
    Proof.
      econstructor; [firstorder.. |].
      intros E1 E2 E3 H1 H2 sigma; unfold equi_unifiable in *.
      now rewrite H1, H2.
    Qed.

    Instance equi_unifiable_app:
      Proper (equi_unifiable ++> equi_unifiable ++> equi_unifiable)
             (@List.app (eq X)).
    Proof.
      intros ?????? sigma; simplify; firstorder. 
    Qed.
    
    Lemma equi_unifiable_refl s: [(s, s)] ≈ nil.
    Proof.
      intros ?; simplify; cbn; intuition. 
    Qed.
    
    Lemma equi_unifiable_comm s t: [(s, t)] ≈ [(t, s)].
    Proof.
      intros ?; simplify; cbn; intuition.
    Qed.

    Lemma equi_unifiable_decompose_app s1 s2 t1 t2:
      [(s1 s2, t1 t2)] ≈ [(s1, t1); (s2, t2)].
    Proof.
      intros ?;simplify; cbn; intuition (unfold unifies in *; cbn in *; congruence).
    Qed.


    Lemma equi_unifiable_cons x s E:
      (var x, s) :: E ≈ (var x, s) :: (update x s var •₊₊ E).
    Proof.
      intros ?; simplify; intuition idtac; cbn in *.
      - intros [u v] ?; mapinj; cbn; destruct x0 as [u' v'].
        injection H2 as <- <-. eapply H1 in H3; cbn in H3.
        unfold unifies in *; cbn in *.
        asimpl. etransitivity; [ etransitivity; [| eapply H3] |].
        all: eapply ext_exp;
          intros y; unfold funcomp, update; destruct eq_dec; subst; eauto.
      - intros [u v] ?; cbn. unfold unifies in H0; cbn in H0.
        eapply in_map with (f := subst_eq (update x s var)) in H. 
        eapply H1 in H; cbn in H; unfold unifies in H.
        unfold unifies in *; cbn in *.
        asimpl in H. etransitivity; [ etransitivity; [| eapply H] |].
        all: eapply ext_exp; intros y; unfold funcomp, update;
          destruct eq_dec; subst; eauto.
    Qed.

    Hint Resolve equi_unifiable_refl equi_unifiable_app equi_unifiable_comm
         equi_unifiable_cons equi_unifiable_decompose_app
      : equi_unifiable.

    
    Lemma equi_unifiable_decomp s t E:
      decomp s t = Some E -> [(s,t)] ≈ E.
    Proof.
      decomp_ind; eauto with equi_unifiable. intuition. intros.
      now rewrite <-H1, <-H3, equi_unifiable_decompose_app. 
    Qed.


    Lemma equi_unifiable_decomp' E E':
      decomp' E = Some E' -> E ≈ E'.
    Proof.
      decomp_ind; intuition.
      now rewrite <-H1, <-equi_unifiable_decomp with (E := E1); eauto. 
    Qed. 


  End Unifiability.


  Hint Rewrite Unifies_cons Unifies_app: simplify.
  Hint Resolve Unifies_nil : core.




  (* *** Soundness *)
  Section Soundness.
    Lemma unify_lambda_free E sigma:
      E ↦ sigma -> all_terms (@lambda_free X) E -> forall x, lambda_free (sigma x).
    Proof.
      induction 1.
      - intros; eauto using @lambda_free.
      - intros H'; eapply decomp'_lambda_free in H; eauto. simplify in H. 
        intros y; unfold update; destruct eq_dec; subst;intuition idtac.
        eapply lambda_free_substitution; eauto; intros x; intros.
        all: eapply IHunify; eapply lambda_free_subst_eqs; eauto.
        all: intros z; unfold update; destruct eq_dec; intuition econstructor.
    Qed.


    Lemma unify_unifiable E sigma:
      E ↦ sigma -> Unifies sigma E.
    Proof.
      induction 1.
      - eapply equi_unifiable_decomp' in H. eapply H; intuition.
      - eapply equi_unifiable_decomp' in H. eapply H.
        eapply equi_unifiable_cons.
        eapply Unifies_cons; cbn; intuition idtac.
        + unfold unifies; cbn.
          unfold update at 1; destruct eq_dec. 2:intuition.
          symmetry; erewrite subst_extensional; eauto.
          intros y ?. unfold update.
          destruct eq_dec; eauto; subst; intuition.
        + intros [s' t'] ?; eapply IHunify in H4 as H4';
            unfold unifies in *; cbn in *.
          mapinj; destruct x0 as [u v]; injection H5 as <- <-.
          rewrite update_irrelevant. symmetry. rewrite update_irrelevant. symmetry.
          now rewrite H4'.
          all: intros ? % singlepoint_subst_vars_variable; intuition.
    Qed.

    
    Lemma unify_free' E sigma:
      E ↦ sigma -> free' sigma.
    Proof.
      induction 1.
      - split; intuition. now destruct H1 as [[= ->]|[]].
      - destruct IHunify; split; intros y; intros.
        + unfold update, bound in *; destruct eq_dec; subst; intuition.
        + unfold update in H7; destruct eq_dec; subst; eauto.
          eapply vars_subst in H7 as [y'].
          destruct H7; eauto. 
    Qed.

    Variable (Gamma: ctx).
    Hypothesis (HO: ord' Gamma <= 1).

    Lemma unify_typing E L sigma:
      E ↦ sigma -> all_terms (@lambda_free X) E ->
      Gamma ⊢₊₊(1) E : L -> Gamma ⊩(1) sigma : Gamma.
    Proof using HO.
      induction 1 in L |-*.
      - intros; now eapply var_typing. 
      - intros LF T. eapply decomp'_typing in T as T'; eauto. 
        eauto; destruct T' as [L' T']; inv T'; inv H7.
        specialize (IHunify L0); mp IHunify; [| mp IHunify].
        + eapply decomp'_lambda_free in H; eauto. simplify in H; cbn in H. intuition idtac.
          eapply lambda_free_subst_eqs; eauto.
          intros y; unfold update; destruct eq_dec; subst; intros; eauto.  
        + eapply eqs_ordertyping_preservation_subst; eauto.
          eapply update_typing; eauto; eapply var_typing; eauto.
        + eapply update_typing; [eauto| | eauto]. 
          eapply ordertyping_weak_preservation_under_substitution; eauto.
    Qed.

    
  End Soundness.

  (* *** Completeness *)
  Section Completeness.

    Lemma decomp_none_not_unifiable sigma s t:
      decomp s t = None -> lambda_free s -> lambda_free t -> ~ unifies sigma s t.
    Proof.
      decomp_ind.
      1 - 2: intros; destruct t; unfold unifies; eauto; cbn; congruence.
      1 - 2: intros ?? _ H1 H2; inv H1; inv H2.
      1 - 2: intros ???? _ H H1 H2 U; inv H1; inv H2;
        eapply H; eauto; unfold unifies in *; cbn in *; congruence.
    Qed.

    Lemma decomp'_none_not_unifiable sigma E:
      decomp' E = None -> all_terms (@lambda_free X) E -> ~ Unifies sigma E.
    Proof.
      decomp_ind; intros; simplify in *; intuition idtac.
      eapply decomp_none_not_unifiable in H; intuition eauto.
    Qed.


    Lemma decomp_some_var s t e E:
      decomp s t = Some (e :: E) -> exists x, fst e = var x.
    Proof.
      remember (e :: E) as E'. intros H; revert H e E HeqE'; decomp_ind; intros. 
      - discriminate.
      - injection HeqE' as ? ?; subst; eexists; cbn; eauto.
      - injection HeqE' as ? ?; subst; eexists; cbn; eauto.
      - destruct E1; eauto; injection HeqE' as ? ?; subst; eauto.
    Qed.

    Lemma decomp'_some_var e E E':
      decomp' E = Some (e :: E') -> exists x, fst e = var x .
    Proof.
      remember (e :: E') as E''. intros H; revert H e E' HeqE''; decomp_ind; intros. 
      - discriminate.
      - destruct E1; eauto; injection HeqE'' as ? ?; subst; eauto.
        eapply decomp_some_var in H; eauto. 
    Qed.


    Fixpoint size (s: exp X) :=
      match s with
      | var x => 0
      | const x => 0
      | lambda s => S (size s)
      | app s1 s2 => S(size s1 + size s2)
      end.
    

    
    Lemma size_ren delta s:
      size (ren delta s) = size s.
    Proof.
      induction  s in delta |-*; cbn; congruence.
    Qed.
    
    Lemma size_subst tau s:
      size (tau • s) = size s + Sum (map (tau >> size) (vars s)).
    Proof.
      induction s in tau |-*; cbn; simplify; eauto.  
      - rewrite IHs. f_equal. f_equal. clear IHs.  generalize (vars s) as A.
        induction A as [|[] ?]; cbn; eauto.
        + destruct eq_dec; rewrite IHA; intuition.
        + destruct eq_dec; rewrite IHA. intuition. lia. cbn.
          unfold funcomp at 1; now rewrite size_ren. 
      - rewrite IHs1, IHs2; lia.
    Qed.


    Lemma unifies_not_var x s tau:
      var x <> s -> unifies tau (var x) s -> ~ x ∈ vars s.
    Proof.
      intros H1; unfold unifies; cbn; intros S % (f_equal size).
      rewrite size_subst in S.
      intros H; eapply H1; eapply in_map with (f := tau >> size) in H as H'.
      eapply Sum_in in H'.  
      eapply vars_varof in H; inv H; cbn in *; eauto.
      all: unfold funcomp in *; lia.
    Qed.

    Lemma unifies_free sigma x s:
      ~ x ∈ vars s -> free' sigma -> unifies sigma (var x) s -> free x.
    Proof using isFree.
      intros H1 F H2; unfold unifies in *; cbn in *.
      destruct F as [F1 F2]. destruct (isFree x) as [H|H]; eauto.
      eapply F1 in H as H'. rewrite H' in H2.
      destruct s; try discriminate; cbn in H2.
      destruct (isFree f) as [L|L]; eauto.
      - eapply F2 with (y := x) in L; eauto; rewrite <-H2; cbn; intuition. 
      - exfalso; eapply H1; left; eapply F1 in L; congruence.
    Qed.
    

    Lemma unifies_free_all sigma x s:
      ~ x ∈ vars s -> free' sigma -> free x ->
      unifies sigma (var x) s -> (forall y, y ∈ vars s -> free y) .
    Proof using isFree.
      intros H1 F H2 H3 y H4; unfold unifies in *; cbn in *.
      destruct F as [F1 F2]. destruct (isFree y) as [H|H]; eauto.
      specialize (F2 _ H2) as H5. rewrite H3 in H5. eapply H5.
      eapply subst_vars. eauto. rewrite F1. cbn; eauto. now unfold bound. 
    Qed.


    Lemma decomp_irrefl s t E:
      decomp s t = Some E -> forall u v, (u,v) ∈ E -> u <> v.
    Proof.
      decomp_ind; cbn. all: intuition idtac; simplify in *; try congruence.
      subst; destruct H4; eauto. 
    Qed.


    Lemma decomp'_irrefl E E':
      decomp' E = Some E' -> forall u v, (u,v) ∈ E' -> u <> v.
    Proof.
      decomp_ind. all: intuition idtac; simplify in *.
      subst; destruct H2; eauto; eapply decomp_irrefl; eauto.
    Qed.

    Lemma eqs_size_induction P:
      (forall E, (forall E' x, Vars' E' ⊆ Vars' E -> x ∈ Vars' E -> ~ x ∈ Vars' E' -> P E') -> P E) ->
      forall E, P E.
    Proof.
      intros IH E. eapply well_founded_induction_type.
      eapply measure_wf, wf_strict_incl with (X := nat); typeclasses eauto.
      intros x H; eapply IH; intros; eapply H. split; eauto. 
    Qed.

    Lemma unify_complete sigma E:
      free' sigma -> Unifies sigma E -> all_terms (@lambda_free X) E -> exists tau, E ↦ tau.
    Proof using isFree.
      intros F; 
        induction E as [E IH] using eqs_size_induction; intros U LF.
      destruct (decomp' E) as [[| [t s] E']|] eqn: DE.
      - exists var. now econstructor. 
      - eapply decomp'_some_var in DE as H'; cbn in H'; destruct H' as [x ->].
        eapply equi_unifiable_decomp' in DE as U'.
        eapply U' in U as H4; simplify in H4; destruct H4 as [H4 H5]; cbn in H4.
        eapply unifies_not_var in H4 as H6;
          [| eapply decomp'_irrefl; eauto; firstorder].
        eapply unifies_free in H6 as H7; eauto.
        specialize (unifies_free_all H6 F H7 H4) as H8.
        eapply Vars_decomp' in DE as H9; simplify in H9; cbn in H9.
        assert (Vars' (update x s var •₊₊ E') ⊆ Vars' E) by
            (rewrite singlepoint_subst_Vars'; eapply incl_cons_project_r; eauto).
        destruct (IH (update x s var •₊₊ E') x) as [tau]; eauto.
        + eapply H9; firstorder.
        + intros ? % singlepoint_subst_Vars'_variable; intuition. 
        + rewrite equi_unifiable_cons in U'.
          eapply U' in U; simplify in U; intuition. 
        + eapply decomp'_lambda_free in DE; eauto; simplify in DE; eauto.
          eapply lambda_free_subst_eqs; intuition idtac; eauto.
          unfold update; destruct eq_dec; intuition; eauto using lambda_free.
        + exists (update x (tau • s) tau); econstructor; eauto.
      - eapply decomp'_none_not_unifiable in DE; intuition eauto.
        exfalso; eauto.
    Qed.
  End Completeness.

End Unification.




(* ** Retyping *)
Section Retyping.

  Variable (X: Const).
  Arguments s₀ {_} {_} _.
  Arguments t₀ {_} {_} _.
  Arguments Gamma₀ {_} {_} _.
  Arguments A₀ {_} {_} _.

  Definition retype_ctx (n: nat) (Gamma : ctx) :=
    map (fun A => if dec2 le (ord A) n then A else alpha) Gamma.

  Lemma retype_ctx_ord n Gamma: 1 <= n -> ord' (retype_ctx n Gamma) <= n.
  Proof.
    intros H; induction Gamma; cbn; eauto; unfold retype_ctx in *.
    rewrite IHGamma; destruct dec2; eauto.
  Qed.
  
  Fixpoint retype_type (n: nat) (A : type) :=
    match A with
    | typevar beta => typevar beta
    | A → B => (if dec2 le (ord A) n then A else alpha) → retype_type n B
    end.


  Lemma retype_type_ord n A: 1 <= n -> ord (retype_type n A) <= S n.
  Proof.
    intros H; induction A; cbn [retype_type].
    - cbn; lia.
    - destruct dec2; simplify; intuition. 
  Qed.

  Lemma retype_type_id n A: ord A <= S n -> retype_type n A = A.
  Proof.
    induction A; cbn [retype_type]; simplify; intuition.
    destruct dec2; [congruence | lia].
  Qed.


  Lemma retype_Arr n L A:
    retype_type n (Arr L A) = Arr (retype_ctx n L) (retype_type n A).
  Proof.
    induction L; cbn; eauto; now rewrite IHL.
  Qed.

  Lemma normal_retyping n Gamma (s: exp X) A:
    normal s -> Gamma ⊢(n) s : A -> retype_ctx n Gamma ⊢(n) s : retype_type n A.
  Proof.
    intros H % normal_nf; induction H in Gamma, A |-*; subst.
    intros (L & B & ? & -> & ?) % Lambda_ordertyping_inv.
    rewrite retype_Arr. eapply Lambda_ordertyping; [unfold retype_ctx; now simplify|].
    unfold retype_ctx; rewrite <-map_rev, <-map_app; fold (retype_ctx n (rev L ++ Gamma)).
    eapply AppR_ordertyping_inv in H0 as (L' & ? &  ?).
    assert (ord' L' <= n).
    - destruct s; destruct i; inv H2; simplify in H4. intuition.
      rewrite H4 in H5; simplify in H5; intuition.
    - eapply AppR_ordertyping with (L0 := retype_ctx n L').
      + clear H2.
        induction H0; eauto.
        econstructor. all: cbn in H3; simplify in H3. 2:intuition.
        destruct dec2; intuition.
        erewrite <-retype_type_id; [| transitivity n; eauto].
        eapply H; cbn; intuition.
      + unfold retype_ctx at 2;
          rewrite <-map_rev; fold (retype_ctx n (rev L')).
        rewrite <-retype_Arr. destruct s; destruct i.
        all: inv H2; rewrite retype_type_id. 2-4:eauto.
        econstructor; eauto.
        unfold retype_ctx; erewrite map_nth_error; eauto.
        destruct dec2; intuition.
  Qed.

  Instance retype n (I: orduni n X) : orduni n X.
  Proof.
    refine {|
      Gamma₀ := retype_ctx n (Gamma₀ I);
      s₀ := eta₀ (s₀ I) H1₀;
      t₀ := eta₀ (t₀ I) H2₀;
      A₀ := retype_type n (A₀ I) |}.
    - abstract (eapply normal_retyping; [apply eta₀_normal | apply eta₀_typing]).
    - abstract (eapply normal_retyping; [apply eta₀_normal | apply eta₀_typing]).
  Defined.

  Lemma retype_iff n (I: orduni n X):
    1 <= n -> OU n X I <-> OU n X (@retype n I).
  Proof.
    intros Leq. rewrite orduni_normalise_correct. 
    destruct I as [Gamma s t A ? ?]; unfold orduni_normalise, retype, OU; cbn.
    split; intros (Delta & sigma & ? & ?); eapply conservativity.ordertyping_weak_ordertyping. 1,3,4,6:now eauto.
    all: intros ??; simplify; intros ? [H'|H']; eapply H.
    all: rewrite nth_error_map_option in *.
    all: destruct (nth Gamma x) eqn: N; try discriminate; cbn in *.
    all: destruct dec2 as [|L]; eauto.
    all: exfalso; eapply L.
    all: eauto using vars_ordertyping_nth, eta₀_typing. 
  Qed.

End Retyping.


(* ** Full First-Order Unification  *)
Section FirstOrderDecidable.

  Variable (X: Const).
  Implicit Types (Gamma: ctx) (n: nat) (sigma tau: fin -> exp X) (s t: exp X)
           (E: list (exp X * exp X)).
  


  Let free (k: nat) (x: nat) := x >= k.

  Instance dec_free k: Dec1 (free k).
  Proof. unfold free; typeclasses eauto. Qed.


  
  Definition decr (k: nat) (sigma: fin -> exp X) (x: nat) := ren (fun y => y - k) (sigma (x + k)).


  Lemma decr_lambda_free k sigma:
    (forall x, lambda_free (sigma x)) -> (forall x, lambda_free (decr k sigma x)).
  Proof.
    intros H x; unfold decr; asimpl.
    eapply lambda_free_substitution; intros; cbn; eauto; econstructor.  
  Qed.

  
  Lemma FO_subst_equiv_eq Delta sigma Gamma (s t: exp X) A:
    (Delta ⊩(1) sigma : Gamma) -> (forall x, normal (sigma x)) ->
    normal s -> normal t -> (Gamma ⊢(1) s : A) -> (Gamma ⊢(1) t : A) ->
    sigma • s ≡ sigma • t -> sigma • s = sigma • t.
  Proof.
    intros. rewrite !subst_extensional
              with (sigma0 := sigma)
                   (tau := fun x => if x el (vars s ++ vars t) then sigma x else var x).
    2 - 3: intros; edestruct dec_in as [D|D]; simplify in D; intuition.
    eapply equiv_unique_normal_forms. intuition.
    1: rewrite !subst_extensional
      with (tau := sigma)
           (sigma0 := fun x => if x el (vars s ++ vars t) then sigma x else var x); eauto. 
    1 - 2: intros; edestruct dec_in as [D|D]; simplify in D; intuition.
    all: eapply normal_subst; eauto 2; intros x; destruct dec_in; eauto 2.
    all: simplify in i; destruct i as [V|V]; eapply vars_ordertyping in V as V'; eauto 2.
    all: destruct V' as (B & V1 & V2).
    all: eapply lambda_free_not_lam, lambda_free_subst; eauto 2. 
  Qed.


  Lemma decr_typing L Gamma n sigma:
    free' (free (length L)) sigma -> L ++ Gamma ⊩(n) sigma : L ++ Gamma -> Gamma ⊩(n) decr (length L) sigma : Gamma.
  Proof.
    intros ? ? x A ?; unfold decr. destruct H as [F1 F2].
    eapply ordertyping_weak_preservation_under_renaming with (Gamma0 := L ++ Gamma).
    - eapply H0. rewrite nth_error_app2; simplify; eauto. 
    - intros y B H ?. eapply F2 in H2; unfold free in *; eauto. 
      rewrite nth_error_app2 in H; simplify in *; eauto.
  Qed.

  Lemma decr_unifies sigma (s t: exp X) k:
    unifies sigma s t -> free' (free k) sigma -> unifies (decr k sigma) (Lambda k s) (Lambda k t).
  Proof.
    intros H1 [H2 H3]; unfold unifies in *; asimpl; f_equal.
    erewrite subst_extensional. symmetry. erewrite subst_extensional; eauto.
    all: intros x V; destruct (le_lt_dec k x).
    1, 3:  rewrite it_up_ge; eauto; unfold decr; asimpl.
    1 - 2: rewrite Nat.sub_add;
      eauto; asimpl; rewrite subst_extensional with (tau := var); [now asimpl|].
    1 - 2: intros y ? % H3; unfold free in *; eauto; unfold funcomp; f_equal; lia.
    1 - 2: rewrite it_up_lt; eauto; symmetry; eapply H2; unfold bound, free; intuition; lia.
  Qed.


  Lemma it_up_free' k (sigma: fin -> exp X): free' (free k) (it k up sigma).
  Proof.
    unfold free; split; intros x; unfold bound.
    - intros ?; rewrite it_up_lt; intuition. lia.
    - intros ? y. rewrite it_up_ge; eauto. 
      intros [z [->]] % vars_varof % varof_ren; eauto.
  Qed.


  Lemma firstorder_decidable' (I: orduni 1 X):
    ord' Gamma₀ <= 1 -> ord A₀ <= 2 ->
    normal s₀ -> normal t₀ -> Dec (NOU 1 I).
  Proof.
    intros O1 O2 N1 N2; eapply iff_dec with (P := exists Delta sigma, Delta ⊩(1) sigma : Gamma₀  /\ sigma • s₀ = sigma • t₀ /\ (forall x : fin, normal (sigma x))).
    split; intros (Delta & sigma & ?); exists Delta; exists sigma; intuition idtac; eauto 2 using FO_subst_equiv_eq, eq_equiv.
    destruct I as [Gamma s t A H1 H2]; cbn in *; subst. unfold NOU; cbn in *.
    eapply normal_nf in N1 as N1'; destruct N1' as [k1 s ? ? ? ? ->].
    eapply normal_nf in N2 as N2'; destruct N2' as [k2 t ? ? ? ? ->].
    eapply normal_Lambda in N1. eapply normal_Lambda in N2.
    destruct (k1 == k2) as [H4|H4];
      [subst; destruct (@unif _ (fun x => x >= k2) _ [(AppR s T, AppR t T0)]) as [[sigma H']|H']|].
    1: left. 2: right. 3: right.
    all: eapply Lambda_ordertyping_inv in H1 as (L & B & ? & ? & ?).
    all: eapply Lambda_ordertyping_inv in H2 as (L' & B' & ? & ? & ?); subst.
    1, 2: assert (L = L' /\ B = B') as []; [|subst L' B'; clear H3 H4].
    1, 3: try (clear H'); eapply Arr_inversion in H3 as [? []]; try lia; rewrite ?H4;
      eauto 2; destruct x; cbn in *; simplify in H0; eauto 2;
        subst; simplify in H4; cbn in H4; lia.
    all: simplify in O2; cbn in O2; destruct O2 as [O2 _]; eapply le_S_n in O2.
    all: assert (ord' (rev L ++ Gamma) <= 1) by now simplify.
    all: eapply order_one_lambda_free in N1 as L1; simplify; eauto 2.
    all: eapply order_one_lambda_free in N2 as L2; simplify; eauto 2.  
    + eapply unify_free' in H' as P.
      eapply unify_typing with (Gamma := rev L ++ Gamma) (L := [B]) in H' as T2;
        [| eauto|simplify; cbn; intuition idtac; eauto using all_terms_nil|eauto using eqs_ordertyping].
      specialize (unify_lambda_free H') as LF; mp LF; simplify; intuition idtac;
        eauto using all_terms_nil.
      exists Gamma. exists (decr (length L) sigma). intuition idtac.
      * specialize decr_typing with (L := rev L) as H9; simplify in H9; eauto. 
      * eapply decr_unifies; eauto.
        specialize (unify_unifiable H' (AppR s T, AppR t T0)); cbn; intuition.
      * eapply lambda_free_normal. pose proof (free := fun (k: nat) (x: nat) => x >= k).
        eapply decr_lambda_free; intros; eapply LF.
    + intros (Delta & sigma & E1 & E2 & E3).  asimpl in E2. 
      eapply Lambda_injective in E2.
      edestruct unify_complete with (sigma := it (|L|) up sigma)
                                    (E := [(AppR s T,AppR t T0)])
                                    (free := free (|L|)); eauto. 
      * typeclasses eauto.
      * eapply it_up_free'. 
      * rewrite Unifies_cons. cbn; unfold unifies; asimpl; asimpl in E2; intuition eauto using Unifies_nil.
      * simplify; eauto using all_terms_nil.
    + intros (Delta & sigma & ? & ? & ?).
      assert (|L| < |L'| \/ |L'| < |L|) as [LT|LT] by lia.
      2: symmetry in H3.
      all: eapply Arr_inversion in H3 as [L'']. 2,4:intuition. all:intuition idtac;subst.
      all: simplify in H5; asimpl in H5; rewrite <-Lambda_plus in H5.
      all: eapply Lambda_injective in H5; destruct L''; [ simplify in LT; try lia; cbn in H5 | ].
      1: destruct T; destruct s; cbn in H5; try discriminate; [| destruct i].
      2: destruct T0; destruct t; cbn in H5; try discriminate; [| destruct i0].
      all: try destruct (le_lt_dec (length L') f); try destruct (le_lt_dec (length L) f).
      2, 4: rewrite it_up_lt in H5; try discriminate;eauto 2.
      1: inv H. 2: inv H2.
      all: cbn [Arr] in H7; now eapply ord_arr_one in H7.
  Qed.

  Lemma firstorder_decidable: Dec1 (OU 1 X).
  Proof.
    intros I. eapply iff_dec. eapply retype_iff; eauto.
    eapply iff_dec. eapply OU_NOU; eauto.
    eapply firstorder_decidable'; cbn; eauto 2 using retype_ctx_ord, retype_type_ord, eta₀_normal.
  Qed.
  
End FirstOrderDecidable.
 