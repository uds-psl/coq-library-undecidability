Set Implicit Arguments.
Require Import List Arith Lia Morphisms FinFun.
Import ListNotations.
From Undecidability.HOU Require Import std.std.
From Undecidability.HOU.calculus Require Import 
  prelim terms syntax semantics equivalence typing order confluence. 
Import ListAutomationInstances ArsInstances.
(* * Terms Extension *)

Notation "sigma •₊ A" := (map (subst_exp sigma) A) (at level 69).
Notation renL delta A := (map (ren delta) A).
Notation Vars := (flat_map vars).


Lemma tab_subst {X} sigma (f: nat -> exp X) n:
  sigma •₊ tab f n = tab (f >> subst_exp sigma) n.
Proof.
  induction n; cbn; simplify; cbn; rewrite ?IHn; reflexivity.
Qed.


Section TermsExtension.

  Context {X: Const}.
  Implicit Types (s t: exp X) (n m: nat) (Gamma Delta: ctx) (A B: type)
           (sigma tau: fin -> exp X) (delta xi: fin -> fin)
           (S T: list (exp X)) (L: list type).  

  (* ** Typing *)
  Reserved Notation "Gamma ⊢₊ A : L" (at level 80, A at level 99).

  Inductive listtyping Gamma : list (exp X) -> list type -> Prop :=
  | listtyping_nil: Gamma ⊢₊ nil : nil
  | listtyping_cons s S A L:
      Gamma ⊢ s : A -> Gamma ⊢₊ S : L -> Gamma ⊢₊ s :: S : A :: L
  where "Gamma ⊢₊ A : L" := (listtyping Gamma A L).

  Hint Constructors listtyping : core. 


  Reserved Notation "Gamma ⊢₊( n ) A : L" (at level 80, A at level 99).


  Inductive orderlisttyping n Gamma: list (exp X) -> list type -> Prop :=
  | orderlisttyping_nil: Gamma ⊢₊(n) nil : nil
  | orderlisttyping_cons s S A L:
      Gamma ⊢(n) s : A -> Gamma ⊢₊(n) S : L -> Gamma ⊢₊(n) s :: S : A :: L
  where "Gamma ⊢₊( n ) A : L" := (orderlisttyping n Gamma A L).

  Hint Constructors orderlisttyping : core. 



  Section ListTypingProperties.
    Lemma listtyping_app Gamma S1 S2 L1 L2:
      Gamma ⊢₊ S1 : L1 -> Gamma ⊢₊ S2 : L2 -> Gamma ⊢₊ S1 ++ S2 : L1 ++ L2.
    Proof.
      induction 1; cbn; (eauto 3).  
    Qed.

    Lemma orderlisttyping_app n Gamma S1 S2 L1 L2:
      Gamma ⊢₊(n) S1 : L1 -> Gamma ⊢₊(n) S2 : L2 -> Gamma ⊢₊(n) S1 ++ S2 : L1 ++ L2.
    Proof.
      induction 1; cbn; (eauto 3).  
    Qed.

    Lemma Vars_listtyping x Gamma S L:
      Gamma ⊢₊ S : L -> x ∈ Vars S -> x ∈ dom Gamma.
    Proof.
      induction 1; cbn; simplify; intuition eauto using typing_variables.
    Qed.

    Lemma Vars_listordertyping x n Gamma S L:
      Gamma ⊢₊(n) S : L -> x ∈ Vars S -> exists A, nth Gamma x = Some A /\ ord A <= n.
    Proof.
      induction 1; cbn; simplify; intuition eauto using vars_ordertyping.
    Qed.


    Lemma repeated_typing Gamma S A:
      (forall s, s ∈ S -> Gamma ⊢ s : A) ->
      forall n, n = length S -> Gamma ⊢₊ S : repeat A n.
    Proof.
      induction S; cbn; intros; subst; cbn;eauto.
      intuition.
    Qed.

    Lemma repeated_ordertyping n Gamma S A:
      (forall s, s ∈ S -> Gamma ⊢(n) s : A) ->
      forall m, m = length S -> Gamma ⊢₊(n) S : repeat A m.
    Proof.
      induction S; cbn; intros; subst; cbn; (eauto 2).
      intuition.  
    Qed.

    Lemma map_var_typing n Gamma N L:
      N ⊆ dom Gamma -> select N Gamma = L ->
      ord' L <= n -> Gamma ⊢₊(n) map var N : L.
    Proof.
      induction N in L |-*; cbn; intuition.  
      - destruct L; try discriminate; intuition.
      - specialize (H a) as H'; mp H'; (intuition (auto with datatypes)); domin H'.
        rewrite H' in H0. subst. econstructor.
        all: cbn in H1; simplify in H1; intuition.
        eapply IHN; (eauto 1); lauto.
    Qed.

    Lemma var_typing n Gamma:
      ord' Gamma <= n -> Gamma ⊩(n) @var X : Gamma.
    Proof.
      intros ????; econstructor; (eauto 1);
        eapply ord'_elements; eauto using nth_error_In.
    Qed.

    Lemma const_ordertyping_list Gamma n Cs:
      ord' (map (ctype X) Cs) <= S n ->
      Gamma ⊢₊(n) map const Cs : map (ctype X) Cs.
    Proof.
      induction Cs; cbn; (eauto 2).
      intros H; simplify in H; intuition; econstructor; (eauto 2). 
    Qed.


    Lemma listtyping_preservation_under_renaming delta Gamma Delta S L:
      Gamma ⊢₊ S : L -> Delta ⊫ delta : Gamma -> Delta ⊢₊ renL delta S : L.
    Proof.
      intros H1 H2; induction H1; cbn; (eauto 3).
    Qed.

    Lemma orderlisttyping_preservation_under_renaming n delta Gamma Delta S L:
      Gamma ⊢₊(n) S : L -> Delta ⊫ delta : Gamma -> Delta ⊢₊(n) renL delta S : L.
    Proof.
      intros H1 H2; induction H1; cbn; (eauto 3).
    Qed.

    Lemma orderlisttyping_preservation_under_substitution Gamma n S L Delta sigma:
      Gamma ⊢₊(n) S : L -> Delta ⊩(n) sigma : Gamma -> Delta ⊢₊(n) sigma •₊ S : L.
    Proof.
      induction 1; cbn; (eauto 4).
    Qed.

    Lemma orderlisttyping_element Gamma n S L:
      Gamma ⊢₊(n) S : L -> forall s, s ∈ S -> exists A, Gamma ⊢(n) s : A /\ A ∈ L.
    Proof.
      induction 1; cbn; intros; intuition; subst.
      eexists; intuition; (eauto 2).
      edestruct IHorderlisttyping; (eauto 1); intuition;
        eexists; split; (eauto 2).
    Qed.



  End ListTypingProperties.


  (* ** Semantics *)
  Notation "S >₊ T" := (lstep step S T) (at level 60).
  Notation "S >₊* T" := (star (lstep step) S T) (at level 60).
  Notation "S ≡₊ T" := (equiv (lstep step) S T) (at level 60).


  Section ListSemanticProperties.
    Lemma list_equiv_ren delta S T:
      S ≡₊ T -> renL delta S ≡₊ renL delta T.
    Proof.
      intros; pattern S, T; eapply list_equiv_ind; (eauto 2).
      intros s t S' T' H1 H2 IH; cbn; now rewrite H1, IH. 
    Qed.

    Lemma list_equiv_subst sigma S T:
      S ≡₊ T -> (sigma •₊ S) ≡₊ (sigma •₊ T).
    Proof.
      intros; pattern S, T; eapply list_equiv_ind; (eauto 2).
      intros s t S' T' H1 H2 IH; cbn; now rewrite H1, IH.
    Qed.


    Lemma list_equiv_anti_ren delta (S T: list (exp X)):
      Injective delta -> renL delta S ≡₊ renL delta T -> S ≡₊ T.
    Proof.
      intros In. remember (renL delta S) as S'. remember (renL delta T) as T'.
      intros H; revert S T HeqS' HeqT'; pattern S', T'. 
      eapply list_equiv_ind; (eauto 2).
      all: intros. 
      - destruct S, T; try discriminate. reflexivity.
      - destruct S0, T0; try discriminate.
        injection HeqS' as ??; injection HeqT' as ??; subst.
        eapply equiv_lstep_cons_proper; (eauto 2).
        eapply equiv_anti_ren; (eauto 2).
    Qed.

    Global Instance list_ren_proper delta:
      Proper (equiv (lstep step) ++> equiv (lstep (@step X))) (map (ren delta)).
    Proof.
      intros ??; now eapply list_equiv_ren.
    Qed.

    Global Instance list_subst_proper sigma:
      Proper (equiv (lstep step) ++> equiv (lstep (@step X))) (map (subst_exp sigma)).
    Proof.
      intros ??; now eapply list_equiv_subst.
    Qed.


  End ListSemanticProperties.

  (* ** Big Arrow *)
  Section ArrowProperties.
    
    Fixpoint Arr (B: list type) (A: type) :=
      match B with
      | nil => A
      | A' :: B => A' → (Arr B A)
      end.


    Lemma Arr_app L1 L2 A:
      Arr (L1 ++ L2) A = Arr L1 (Arr L2 A).
    Proof.
      induction L1; cbn; congruence.
    Qed.



    Lemma arity_Arr L A: arity (Arr L A) = length L + arity A.
    Proof. induction L; cbn; congruence. Qed.



    Lemma Arr_inversion L1 L2 A1 A2:
      length L1 <= length L2 ->
      Arr L1 A1 = Arr L2 A2 -> exists L, L2 = L1 ++ L  /\ A1 = Arr L A2.
    Proof.
      induction L1 in L2, A1, A2 |-*; cbn.
      - intros _. exists L2. intuition.
      - destruct L2. inversion 1.
        intros H H1. cbn in H. eapply le_S_n in H.
        injection H1 as ??. subst. edestruct IHL1; (eauto 2).
        intuition. exists x; intuition. f_equal; (eauto 2).
    Qed.


    Lemma type_decompose:
      forall A, exists L beta, A = Arr L (typevar beta).
    Proof.
      induction A; cbn.
      - exists nil; exists n. reflexivity.
      - destruct IHA2 as (L & beta & H). subst.
        exists (A1 :: L); exists beta. reflexivity.
    Qed.

    Lemma target_ord A: ord (target A) = 1.
    Proof.
      induction A; cbn; congruence.
    Qed.


    Lemma arity_decomposed L beta:
      arity (Arr L (typevar beta)) = length L.
    Proof.
      induction L; cbn; congruence. 
    Qed.

    Lemma Arr_left_injective L1 L2 A:
      Arr L1 A = Arr L2 A -> L1 = L2.
    Proof.
      destruct (le_ge_dec (length L1) (length L2)); intros H; [|symmetry in H].
      all: eapply Arr_inversion in H as [L3]; (eauto 1); intuition.
      all: destruct L3; simplify in *; (eauto 2).
      all: eapply (f_equal arity) in H1; cbn in H1; rewrite arity_Arr in H1.
      all: lia.
    Qed.


    Lemma ord_Arr L A: ord (Arr L A) = max (1 + ord' L) (ord A).
    Proof.
      induction L; cbn -[max].
      symmetry; eapply Nat.max_r. eapply ord_1.
      rewrite IHL, Nat.max_assoc.
      cbn [plus]. reflexivity.
    Qed.

    Lemma target_Arr L A: target (Arr L A) = target A.
    Proof.
      induction L; cbn; congruence.
    Qed.

    Lemma ord_repeated n A: ord' (repeat A n) <= ord A.
    Proof.
      induction n; cbn; (eauto 2).
      lia. 
    Qed.

  End ArrowProperties.

  Hint Rewrite ord'_app ord_Arr ord_repeated : simplify.

  Hint Rewrite ord_Arr target_Arr target_ord : simplify.


  (* ** List Abstraction and Application *)

  Fixpoint Lambda (n: nat) (s: exp X) :=
    match n with
    | 0 => s
    | S n => lambda (Lambda n s)
    end.

  Fixpoint AppR (e: exp X) (A: list (exp X))  :=
    match A with
    | nil => e
    | e' :: A => AppR e A e'
    end.

  Fixpoint AppL (A: list (exp X)) (e: exp X) :=
    match A with
    | nil => e
    | e' :: A => e' (AppL A e)
    end.


  Lemma Lambda_plus (n m: nat) s:
    Lambda n (Lambda m s) = Lambda (n + m) s.
  Proof.
    induction n; cbn; congruence.
  Qed.

  Lemma Lambda_injective n (s t: exp X):
    Lambda n s = Lambda n t -> s = t.
  Proof.
    induction n; cbn; intuition; eapply IHn; congruence.
  Qed.

  Lemma AppL_app S1 S2 t:
    AppL (S1 ++ S2) t = AppL S1 (AppL S2 t).
  Proof.
    revert S2 t; induction S1; cbn; congruence.
  Qed.

  Lemma AppR_app T1 T2 s:
    AppR s (T1 ++ T2) = AppR (AppR s T2) T1.
  Proof.
    revert T2 s; induction T1; cbn; congruence.
  Qed.

  Lemma AppR_vars s T:
    vars (AppR s T) === vars s ++ Vars T.
  Proof.
    induction T; cbn; simplify; lauto.
    rewrite IHT, <-app_assoc; eapply proper_app_seteq; lauto.
    eauto using app_comm.
  Qed.
  
  Lemma AppR_head s T: head (AppR s T) = head s.
  Proof.
    induction T in s |-*; cbn ; (eauto 1); now rewrite IHA. 
  Qed.

  Hint Rewrite AppR_head : simplify.



  (* ** Substitutions and Renaming *)
  Section ListOperatorsSubstitutionRenaming.
    
    Lemma Lambda_ren delta n s:
      ren delta (Lambda n s) = Lambda n (ren (it n up_ren delta) s).
    Proof.
      induction n in delta |-*; cbn; (eauto 2).
      rewrite IHn. do 3 f_equal. 
      symmetry. eapply it_commute.
    Qed.

    Lemma Lambda_subst sigma n s:
      sigma • (Lambda n s) = Lambda n (it n up sigma • s).
    Proof.
      induction n in sigma |-*; cbn; (eauto 2).
      rewrite IHn; do 3 f_equal.
      symmetry. eapply it_commute.
    Qed.

    Lemma AppL_ren delta S t:
      ren delta (AppL S t) = AppL (renL delta S) (ren delta t).
    Proof.
      induction S; cbn; congruence.
    Qed.

    Lemma AppL_subst sigma S t:
      sigma • AppL S t = AppL (sigma •₊ S) (sigma • t).
    Proof.
      induction S; cbn; congruence.
    Qed.

    Lemma AppR_ren delta s T:
      ren delta (AppR s T) = AppR (ren delta s) (renL delta T) .
    Proof.
      induction T; cbn; congruence. 
    Qed.

    Lemma AppR_subst sigma s T:
      sigma • AppR s T = AppR (sigma • s) (sigma •₊ T).
    Proof.
      induction T; cbn; congruence.  
    Qed.

  End ListOperatorsSubstitutionRenaming.





  (* ** Compatibility Properties *)
  Section ListOperatorsCompatibilityProperties.

    Global Instance Lambda_step_proper k:
      Proper (step ++> step) (Lambda k).
    Proof.
      induction k; cbn; intros ??; (eauto 3).
    Qed.

    Global Instance AppR_step_proper:
      Proper (step ++> eq ++> step) AppR.
    Proof.
      intros s t ? ? A ->.
      induction A in s, t, H |-*; cbn; (eauto 3).
    Qed.

    Global Instance AppR_lstep_proper:
      Proper (eq ++> lstep step ++> step) AppR.
    Proof.
      intros ? ? -> ? ? H.
      induction H in y |-*; cbn; (eauto 2).
    Qed. 

    Global Instance AppL_step_proper:
      Proper (eq ++> step ++> step) AppL.
    Proof.
      intros ? A -> s t H.
      induction A in s, t, H |-*; cbn; (eauto 3).
    Qed.

    Global Instance AppL_lstep_proper:
      Proper (lstep step ++> eq ++> step) AppL.
    Proof.
      intros ? ? H ? t ->.
      induction H in t |-*; cbn; (eauto 2).
    Qed. 

    Global Instance Lambda_steps_proper k:
      Proper (star step ++> star step) (Lambda k).
    Proof.
      induction 1; (eauto 1); now rewrite H.
    Qed.

    Global Instance AppL_proper:
      Proper (star (lstep step) ++> star step ++> star step) AppL.
    Proof.
      intros ? ?. induction 1.
      - intros ? ? ?. induction H; cbn; (eauto 2). 
        rewrite <-IHstar. 
        econstructor 2; (eauto 1); eapply AppL_step_proper; (eauto 2).
      - intros ? ? ?. rewrite H. specialize (IHstar _ _ H1).
        now rewrite IHstar. 
    Qed.

    Global Instance AppR_proper:
      Proper (star step ++> star (lstep step) ++> star step) AppR.
    Proof.
      intros ? ?. induction 1.
      - intros ? ? ?. induction H; cbn; (eauto 2). 
        rewrite <-IHstar.
        econstructor 2; (eauto 1); eapply AppR_lstep_proper; (eauto 2).
      - intros ? ? ?. rewrite H. specialize (IHstar _ _ H1).
        now rewrite IHstar. 
    Qed.

    Global Instance Lambda_equiv_proper n:
      Proper (equiv step ++> equiv step) (Lambda n).
    Proof.
      intros ? ? ?; induction n; cbn; (eauto 2).
      now rewrite IHn. 
    Qed.

    Global Instance equiv_AppL_proper:
      Proper (equiv (lstep step) ++> equiv step ++> equiv step) AppL.
    Proof.
      intros ? ? (? & H1 & H2) % church_rosser ? ? (? & H3 & H4) % church_rosser;
        eauto.
      now rewrite H1, H2, H3, H4. 
    Qed.  

    Global Instance equiv_AppR_proper:
      Proper (equiv step ++> equiv (lstep step) ++> equiv step) AppR.
    Proof.
      intros ? ? (? & H1 & H2) % church_rosser ? ? (? & H3 & H4) % church_rosser; (eauto 2).
      now rewrite H1, H2, H3, H4. 
    Qed.  

  End ListOperatorsCompatibilityProperties.



  Lemma AppR_Lambda T s n sigma:
    AppR (sigma • Lambda (length T + n) s) T >* T .+ sigma • Lambda n s.
  Proof.
    revert s n sigma; induction T; intros; cbn [AppR length]; (eauto 2). 
    replace (S (length T) + n) with (length T + S n) by lia.
    rewrite IHT; cbn; econstructor 2; (eauto 2); now asimpl. 
  Qed.

  Lemma AppR_Lambda' T s m:
    m = length T -> AppR (Lambda m s) T >* T .+ var • s.
  Proof.
    intros ?; replace (Lambda m s) with (var • Lambda m s) by now asimpl.
    replace m with (length T + 0) by lia. 
    eapply AppR_Lambda with (n := 0).
  Qed.


  (* ** Equivalence Inversions *)
  Section EquivalenceInversions.

    Lemma equiv_Lambda_elim k s t:
      Lambda k s ≡ Lambda k t -> s ≡ t.
    Proof.
      induction k; cbn; eauto using equiv_lam_elim.
    Qed.
      
    Lemma equiv_AppR_elim s1 s2 T1 T2:
      AppR s1 T1 ≡ AppR s2 T2 ->
      isAtom s1 ->
      isAtom s2 ->
      T1 ≡₊ T2 /\ s1 = s2.
    Proof.
      intros; assert (isAtom (head (AppR s1 T1))); simplify; (eauto 2).
      intros; assert (isAtom (head (AppR s2 T2))); simplify; (eauto 2).
      
      revert T2 H H2 H3; induction T1 as [|a A IH]; intros [| b B]; cbn; intros.
      + intuition.
        destruct s1, s2; cbn in *; intuition; try Discriminate.
        all: Injection H; now subst. 
      + destruct s1; cbn in *; try now intuition; Discriminate.
      + destruct s2; cbn in *; try now intuition; Discriminate. 
      + Injection H. intuition; edestruct IH; (eauto 2).
        now rewrite H5, H. 
    Qed.

    Lemma equiv_AppL_elim S1 S2 t1 t2:
      AppL S1 t1 ≡ AppL S2 t2 ->
      (forall s, s ∈ S1 -> isAtom (head s)) ->
      (forall s, s ∈ S2 -> isAtom (head s)) ->
      length S1 = length S2 ->
      S1 ≡₊ S2 /\ t1 ≡ t2.
    Proof.
      revert S2; induction S1 as [|s1 S1 IH]; intros [| s2 S2];
        cbn; intros;
        try discriminate.
      + intuition. 
      + apply equiv_app_elim in H as ?; rewrite ?AppR_head; (eauto 3).
        intuition; edestruct IH; (eauto 3).
        now rewrite H3, H4.
    Qed.

  End EquivalenceInversions.



  (* ** Normality *)
  Section Normality.

    Lemma normal_Lambda k s:
      normal (Lambda k s) -> normal s.
    Proof.
      induction k; cbn; eauto using normal_lam_elim.
    Qed.

    Lemma normal_AppL_left S t:
      normal (AppL S t) -> Normal (lstep step) S.
    Proof.
      induction S; cbn; intros H ? H1; inv H1.
      - eapply H; (eauto 2).
      - eapply IHS; eauto using normal_app_r.
    Qed.

    Lemma normal_AppL_right S t:
      normal (AppL S t) -> normal t.
    Proof.
      induction S in t |-*; cbn; eauto using normal_app_r.
    Qed.

    Lemma normal_AppR_right s T:
      normal (AppR s T) -> Normal (lstep step) T.
    Proof.
      induction T; cbn; intros H ? H1; inv H1.
      - eapply H. eauto.
      - eapply IHT; eauto using normal_app_l.
    Qed.

    Lemma normal_AppR_left s T:
      normal (AppR s T) -> normal s.
    Proof.
      induction T in s |-*; cbn; eauto using normal_app_l.
    Qed.

  End Normality.

  Hint Resolve 
       normal_Lambda normal_AppR_left normal_AppR_right : core.


  (* ** List Operators Typing *)
  Section ListOperatorsTyping.
    
    Lemma Lambda_typing Gamma L B k s:
      length L = k ->
      rev L ++ Gamma ⊢ s : B ->
                      Gamma ⊢ (Lambda k s) : Arr L B.
    Proof.
      induction k in L, Gamma, s |-*.
      - destruct L; try discriminate.
        intros _; cbn; (eauto 2).
      - destruct L; try discriminate.
        intros H; injection H as H.
        cbn; intros; econstructor.
        eapply IHk; (eauto 2).
        now rewrite <-app_assoc in H0. 
    Qed.

    Lemma Lambda_ordertyping n Gamma L B k s:
      length L = k ->
      rev L ++ Gamma ⊢(n) s : B ->
                        Gamma ⊢(n) (Lambda k s) : Arr L B.
    Proof.
      induction k in L, Gamma, s |-*.
      - destruct L; try discriminate.
        intros _; cbn; (eauto 2).
      - destruct L; try discriminate.
        intros H; injection H as H.
        cbn; intros; econstructor.
        eapply IHk; (eauto 2).
        now rewrite <-app_assoc in H0.
    Qed.


    Lemma AppL_typing_repeated Gamma s T n A:
      Gamma ⊢₊ T: repeat (A → A) n -> Gamma ⊢ s : A -> Gamma ⊢ AppL T s : A.
    Proof.
      induction T in n |-*; (eauto 1); cbn.
      intros; inv H; intuition.
      destruct n; try discriminate.
      cbn in H3; injection H3 as ??; subst.  
      econstructor; (eauto 2). 
    Qed.


    Lemma AppL_ordertyping_repeated k Gamma s T n A:
      Gamma ⊢₊(n) T: repeat (A → A) k -> Gamma ⊢(n) s : A -> Gamma ⊢(n) AppL T s : A.
    Proof.
      induction T in k |-*; (eauto 1); cbn.
      intros; inv H; intuition.
      destruct k; try discriminate.
      cbn in H3; injection H3 as ??; subst.  
      econstructor; (eauto 2).
    Qed.



    Lemma AppR_typing Gamma L s T B:
      Gamma ⊢₊ T : L -> Gamma ⊢ s : Arr (rev L) B -> Gamma ⊢ AppR s T : B.
    Proof.
      induction 1 in s, B |-*; cbn; (eauto 1); rewrite Arr_app; cbn; (eauto 3).  
    Qed.

    Lemma AppR_ordertyping n Gamma T s L B:
      Gamma ⊢₊(n) T : L -> Gamma ⊢(n) s : Arr (rev L) B -> Gamma ⊢(n) AppR s T : B.
    Proof.
      induction 1 in s, B |-*; cbn; (eauto 1); rewrite Arr_app; cbn; (eauto 3).  
    Qed.

    Lemma Lambda_typing_inv Gamma s k B:
      Gamma ⊢ Lambda k s : B ->
          exists L A, rev L ++ Gamma ⊢ s : A /\
          B = Arr L A /\ length L = k.
    Proof.
      induction k in Gamma, B |-*; cbn.
      - exists nil. exists B. intuition.
      - intros H; inv H.
        edestruct IHk as (? & ? & ?); (eauto 2).
        intuition. exists (A :: x). exists x0.
        intuition; cbn; try congruence.
        now rewrite <-app_assoc.
    Qed.

    Lemma Lambda_ordertyping_inv n Gamma s k B:
      Gamma ⊢(n) Lambda k s : B ->
      exists L A, rev L ++ Gamma ⊢(n) s : A /\
        B = Arr L A /\ length L = k.
    Proof.
      induction k in Gamma, B |-*; cbn.
      - exists nil. exists B. cbn in *; intuition.
      - intros H; inv H.
        edestruct IHk as (? & ? & ?); (eauto 2).
        intuition. exists (A :: x). exists x0.
        intuition; cbn; try congruence.
        now rewrite <-app_assoc.
    Qed.


    Lemma AppL_typing_inv Gamma T B t:
      Gamma ⊢ AppL T t : B -> exists L A, Gamma ⊢₊ T : L /\ Gamma ⊢ t : A.
    Proof.
      induction T in B |-*; cbn.
      - exists nil. exists B. intuition.
      - intros H; inv H.
        edestruct IHT as (? & ? & ?); (eauto 2).
        do 2 eexists; intuition; (eauto 2).
    Qed.

    Lemma AppL_ordertyping_inv n Gamma T B t:
      Gamma ⊢(n) AppL T t : B -> exists L A, Gamma ⊢₊(n) T : L /\ Gamma ⊢(n) t : A.
    Proof.
      induction T in B |-*; cbn.
      - exists nil. exists B. intuition.
      - intros H; inv H.
        edestruct IHT as (? & ? & ?); (eauto 2).
        do 2 eexists; intuition; (eauto 2).
    Qed.

    Lemma AppR_typing_inv Gamma T B t:
      Gamma ⊢ AppR t T : B -> exists L, Gamma ⊢₊ T : L /\ Gamma ⊢ t : Arr (rev L) B.
    Proof.
      induction T in Gamma, B, t |-*; cbn; intros.
      - exists nil; intuition.
      - inv H. destruct (IHT _ _ _ H2) as [L]; intuition.
        exists (A :: L). intuition; cbn; rewrite Arr_app; (eauto 2). 
    Qed.


    Lemma AppR_ordertyping_inv n Gamma T B t:
      Gamma ⊢(n) AppR t T : B -> exists L, Gamma ⊢₊(n) T : L /\ Gamma ⊢(n) t : Arr (rev L) B.
    Proof.
      induction T in Gamma, B, t |-*; cbn; intros.
      - exists nil; intuition.
      - inv H. destruct (IHT _ _ _ H2) as [L]; intuition.
        exists (A :: L). intuition; cbn; rewrite Arr_app; (eauto 2). 
    Qed.

  End ListOperatorsTyping.


  (* ** Utilities *)
  Section Utilities.

    Inductive nf: exp X -> Type :=
      nfc k s t T:
      (forall t, t ∈ T -> nf t) ->
      isAtom s ->
      t = Lambda k (AppR s T) ->
      nf t.

    Lemma normal_nf s:
      normal s -> nf s.
    Proof.
      induction s.
      + intros. exists 0 (var f) nil; cbn; intuition.
      + intros. exists 0 (const c) nil; cbn; intuition.
      + intros H; mp IHs; eauto using normal_lam_elim;
          destruct IHs as [k s' t' T H1].
        exists (S k) s' T; (eauto 1); cbn; congruence.
      + intros H; eapply normal_app_r in H as Ns1;
        eapply normal_app_l in H as Ns2.  
        mp IHs1; (eauto 1); mp IHs2; (eauto 2).
        destruct IHs1. subst t.
        destruct k; [|exfalso; eapply H; cbn; eauto].
        exists 0 s (s2 :: T); (eauto 1); cbn; simplify.
        intros t. destruct (s2 == t); subst; intuition.
        destruct (t el T); intuition.
        exfalso; intuition.
    Qed.


    Lemma AppL_largest (P: exp X -> Prop) (s: exp X):
      Dec1 P ->
      { S & { t | (forall s, s ∈ S -> P s) /\
                  s = AppL S t /\
                  forall (u v: exp X), t = u v -> ~ P u}}.
    Proof.
      intros D. induction s.
      - exists nil. exists (var f). cbn; intuition; discriminate.
      - exists nil. exists (const c). cbn; intuition; discriminate.
      - exists nil. exists (lambda s). cbn; intuition; discriminate.
      - destruct IHs2 as (S & t & ? & -> & ?).
        destruct (D s1).
        + exists (s1 :: S). exists t; cbn; intuition; subst; (eauto 2).
        + exists nil. exists (s1 (AppL S t)). cbn; intuition.
          injection H1 as ??;subst; intuition.
    Qed.


    Lemma head_decompose s: exists T, s = AppR (head s) T.
    Proof.
      induction s; try solve [exists nil; eauto].
      destruct IHs1 as [T]; cbn.
      exists (s2 :: T); cbn. congruence. 
    Qed.



  End Utilities.
  
End TermsExtension.





#[export] Hint Constructors listtyping : core. 
#[export] Hint Constructors orderlisttyping : core. 
Global Hint Rewrite ord'_app ord_Arr ord_repeated : simplify.
Global Hint Rewrite ord_Arr : simplify.
#[export] Hint Resolve 
     normal_Lambda normal_AppR_left normal_AppR_right : core.
Global Hint Rewrite @Lambda_ren @Lambda_subst @AppL_ren @AppL_subst @AppR_ren @AppR_subst : asimpl.

Global Hint Rewrite @AppR_head : simplify.
  

Global Hint Rewrite target_Arr target_ord: simplify.
Global Hint Rewrite arity_Arr : simplify.

Notation "S >₊ T" := (lstep step S T) (at level 60).
Notation "S >₊* T" := (star (lstep step) S T) (at level 60).
Notation "S ≡₊ T" := (equiv (lstep step) S T) (at level 60).
Notation "Gamma ⊢₊ A : L" := (listtyping Gamma A L) (at level 80, A at level 99).
Notation "Gamma ⊢₊( n ) A : L" := (orderlisttyping n Gamma A L) (at level 80, A at level 99).
