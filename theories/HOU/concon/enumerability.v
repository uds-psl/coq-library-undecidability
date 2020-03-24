Set Implicit Arguments.
Require Import List Omega.
From Undecidability.HOU Require Import std.std calculus.calculus concon.conservativity unification.unification.

(** * Enumerability from Conservativity *)

(** ** Nth-Order Unification  *)
Section ListEnumerabilityOrdered.

  Variable (X: Const).  
  Hypothesis (enumX: enumT X).


  Fixpoint L_le n: list ({ '(p, q) | p <= q}) :=
    match n with
    | 0 => nil
    | S n => L_le n
                 ++ [exist _ (p, p) (le_n p) | p ∈ L_T n]
                 ++ [exist _ (p, S q) (le_S p q H) | (exist _ (p, q) H) ∈ L_le n ]
    end.


  Scheme le_strong_ind := Induction for le Sort Prop.
  
  Global Instance enumT_sig_le: enumT ({ '(p, q) | p <= q}).
  Proof.
    exists L_le; eauto.
    intros [[n m] H]; induction H using le_strong_ind.
    - destruct (el_T n) as [x1]; exists (S x1); cbn; in_app 2.
      in_collect n; eauto.
    - destruct IHle as [x1]; exists (S x1); cbn; in_app 3.
      now in_collect (@exist _ (fun '(n, m) => n <= m) (n, m) H).
  Qed.

  Global Instance enumT_le a b: enumT (a <= b).
  Proof.
    exists (fix L n := match n with
                 | 0 => nil
                 | S n => L n ++ [cast H E | (exist _ (p, q) H) ∈ (@L_T { '(p, q) | p <= q} _ n) where E: (p, q) = (a, b)]        
                 end).
    eauto.
    intros H; destruct (el_T (exist (fun '(n, m) => n <= m) (a, b) H)) as [x]; exists (S x); cbn.
    in_app 2.
    eapply in_flat_map. exists (exist (fun '(n, m) => n <= m) (a, b) H). split; eauto.
    destruct dec; intuition. left; cbn. unfold cast.
    symmetry. rewrite <-Eqdep_dec.eq_rect_eq_dec; eauto; eapply eq_dec.
  Qed. 



  Fixpoint L_ordertypingT Gamma n s A m : list (Gamma ⊢(n) (s: exp X) : A) :=
    match m with
    | 0 => nil
    | S m => L_ordertypingT Gamma n s A m ++
                           match s as s return list (Gamma ⊢(n) s : A) with
                           | var i => [@ordertypingVar X n Gamma i A H1 H2 | H1 ∈ L_T m where H2: nth Gamma i = Some A]
                           | const c => [cast (@ordertypingConst X n Gamma c H1) H2 | H1 ∈ L_T m where H2: ctype X c = A]
                           | lambda s => match A with
                                   | typevar beta => nil
                                   | A → B => [ ordertypingLam H | H ∈ L_ordertypingT (A :: Gamma) n s B m]
                                   end
                           | app s t => [ordertypingApp H1 H2 | (H1, H2) ∈ (L_ordertypingT Gamma n s (A1 → A) m × L_ordertypingT Gamma n t A1 m) & A1 ∈ L_T m]
                           end
    end.



  Scheme ordertyping_strong_ind := Induction for ordertyping Sort Prop.
  
  Global Instance enumT_ordertyping Gamma n s A: enumT (Gamma ⊢(n) (s: exp X) : A).
  Proof.
    exists (L_ordertypingT Gamma n s A); eauto.
    intros H. induction H using ordertyping_strong_ind.
    - destruct (el_T l) as [x1]; exists (S x1); cbn; in_app 2.
      eapply in_flat_map. exists l. split; eauto.
      destruct dec; intuition. left. f_equal.
      eapply Eqdep_dec.inj_pair2_eq_dec. eapply eq_dec. now destruct e, e0.
    - destruct (el_T l) as [x1]; exists (S x1); cbn; in_app 3.
      eapply in_flat_map. exists l. split; eauto.
      destruct dec; intuition. left.
      unfold cast; rewrite <-Eqdep_dec.eq_rect_eq_dec; eauto. eapply eq_dec.  
    - destruct IHordertyping as [x1]; exists (S x1); cbn; in_app 4; now in_collect H.
    - edestruct IHordertyping1 as [x1'], IHordertyping2 as [x2'], (el_T A) as [x3'].
      exists (S (x1' + x2' + x3')); cbn; in_app 5.
      eapply in_flat_map. exists A. split.
      2: in_collect (H, H0).
      all: eauto using cum_ge'.
  Qed.


  Fixpoint L_orduni k (n: nat) : list (orduni k X) :=
    match n with
    | 0 => nil
    | S n => L_orduni k n ++ flat_map (fun '(Gamma, s, t, A) => [@Build_orduni k _ Gamma s t A H1 H2 | (H1, H2) ∈ (L_T n × L_T n)])
                  [(Gamma, s, t, A) | (Gamma, s, t, A) ∈ (L_T n × L_T n × L_T n × L_T n)]
    end.

  Global Instance enumT_orduni n:
    enumT (orduni n X).
  Proof with eauto using cum_ge'.
    exists (L_orduni n).
    - eauto.
    - intros [Gamma s t A H1 H2].
      destruct (el_T Gamma) as [x1], (el_T s) as [x2], (el_T t) as [x3], (el_T A) as [x4], (el_T H1) as [x5], (el_T H2) as [x6].
      exists (S (x1 + x2 + x3 + x4 + x5 + x6)); cbn. in_app 2.
      eapply in_flat_map. exists (Gamma, s, t, A). intuition.
      + in_collect (Gamma, s, t, A); eapply cum_ge'; eauto;omega.
      + in_collect (H1, H2)...
  Qed.


End ListEnumerabilityOrdered.


Theorem enumerable_orderdunification n (X: Const): 1 <= n -> enumerable__T X -> enumerable (OU n X).
Proof.
  intros Leq; rewrite enum_enumT. intros [EX].
  eapply enumerable_red2 with (g := fun (I: uni X) => (Gammaᵤ, sᵤ, tᵤ, Aᵤ)).
  eapply unification_conserve; eauto.
  eapply enum_enumT, inhabits, enumT_orduni, EX.
  typeclasses eauto.
  2: eapply enumerable_unification, enum_enumT, inhabits, EX.
  intros [][]; unfold U; cbn. now intros [= -> -> ->].
Qed.


(** ** System Unification *)
From Undecidability.HOU Require Import unification.systemunification.

Section ListEnumerabilitySystems.

  Variable (X: Const).
  Hypothesis (enumX: enumT X).



  Fixpoint L_sys (n: nat) : list (sysuni X) := 
    match n with
    | 0 => nil
    | S n => L_sys n
                  ++ [Build_sysuni (eqs_typing_nil X Gamma) | Gamma ∈ L_T n]
                  ++ [Build_sysuni (eqs_typing_cons H1 H2 (@cast _ (fun f => eqs_typing f E L) Gamma Gamma' H EQ)) |
                     (@Build_sysuni _ Gamma E L H, @Build_uni _ Gamma' s t A H1 H2)
                       ∈ (L_sys n × L_T n) where EQ: Gamma = Gamma']
    end.


  
  Scheme eqs_typing_strong_ind := Induction for eqs_typing Sort Prop.
    
  Global Instance enumT_sys:
    enumT (sysuni X).
  Proof with eauto using cum_ge'.
    exists L_sys.
    - eauto.
    - intros [Gamma E L H]. induction H using eqs_typing_strong_ind.
      + destruct (el_T Gamma) as [x]; exists (S x); cbn; in_app 2.
        now in_collect Gamma.
      + destruct (el_T (Build_uni Gamma s t A t0 t1)) as [x1].
        destruct IHeqs_typing as [x2]. exists (1 + x1 + x2).
        cbn; in_app 3. eapply in_flat_map. exists (Build_sysuni H, Build_uni Gamma s t A t0 t1).
        split. eapply in_prod...
        destruct dec; intuition.
        subst. left. f_equal. f_equal.
        unfold cast. rewrite <-Eqdep_dec.eq_rect_eq_dec; eauto.
        eapply eq_dec.
  Qed.
End ListEnumerabilitySystems.



Theorem enumerable_systemunification (X: Const): enumerable__T X -> enumerable (@SU X).
Proof.
  rewrite enum_enumT. intros [EX].
  eapply enumerable_red2 with (g := fun (I: uni X) => (Gammaᵤ, sᵤ, tᵤ, Aᵤ)).
  eapply SU_U; eauto.
  eapply enum_enumT, inhabits, enumT_sys, EX.
  typeclasses eauto.
  2: eapply enumerable_unification, enum_enumT, inhabits, EX.
  intros [][]; unfold U; cbn. now intros [= -> -> ->].
Qed.


(** ** Nth-Order System Unification *)
Section ListEnumerabilityOrderedSystems.

  Variable (X: Const).
  Hypothesis (enumX: enumT X).



  Fixpoint L_ordsys k (n: nat) : list (ordsysuni X k) := 
    match n with
    | 0 => nil
    | S n => L_ordsys k n
                  ++ [Build_ordsysuni _ _ _ _ _ (eqs_ordertyping_nil X Gamma k) | Gamma ∈ L_T n]
                  ++ [Build_ordsysuni _ _ _ _ _ 
                    (eqs_ordertyping_cons _ _ _ _ _ _ _ _ H1 H2 (@cast _ (fun f => eqs_ordertyping  _ f _ E L) Gamma Gamma' H EQ)) |
                     (@Build_ordsysuni _ _ Gamma E L H, @Build_orduni _ _ Gamma' s t A H1 H2)
                       ∈ (L_ordsys k n × L_T n) where EQ: Gamma = Gamma']
    end.


  
  Scheme eqs_ordertyping_strong_ind := Induction for eqs_ordertyping Sort Prop.
    
  Instance enumT_ordsys n:
    enumT (ordsysuni X n).
  Proof with eauto using cum_ge'.
    exists (L_ordsys n).
    - eauto.
    - intros [Gamma E L H]. induction H using eqs_ordertyping_strong_ind.
      + destruct (el_T Gamma) as [x]; exists (S x); cbn; in_app 2.
        now in_collect Gamma.
      + destruct (el_T (Build_orduni Gamma s t A o o0)) as [x1].
        destruct IHeqs_ordertyping as [x2]. exists (1 + x1 + x2).
        cbn; in_app 3. eapply in_flat_map. exists (Build_ordsysuni _ _ _ _ _ H, Build_orduni Gamma s t A o o0).
        split. eapply in_prod...
        destruct dec; intuition.
        subst. left. f_equal. f_equal.
        unfold cast. rewrite <-Eqdep_dec.eq_rect_eq_dec; eauto.
        eapply eq_dec.
  Qed.

End ListEnumerabilityOrderedSystems.



Theorem enumerable_orderedsystemunification n (X: Const): 1 <= n -> enumerable__T X -> enumerable (@SOU X n).
Proof.
  rewrite enum_enumT. intros Leq [EX].
  eapply enumerable_red2 with (g := fun (I: sysuni X) => (@Gammaᵤ' _ I, @Eᵤ' _ I, @Lᵤ' _ I)).
  eapply systemunification_conserve; eauto.
  eapply enum_enumT, inhabits, enumT_ordsys, EX.
  typeclasses eauto.
  2: eapply enumerable_systemunification, enum_enumT, inhabits, EX.
  intros [][]; unfold U; cbn. now intros [= -> -> ->].
Qed.
