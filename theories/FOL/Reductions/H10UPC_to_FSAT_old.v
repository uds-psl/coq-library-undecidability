(* * FOL Reductions *)
From Undecidability.DiophantineConstraints Require Import H10UPC H10UPC_undec.
From Undecidability.FOL Require Import Util.Syntax Util.FullDeduction Util.FullTarski Util.Syntax Util.Syntax_facts.
From Undecidability.Shared Require Import Dec.
From Undecidability.Shared.Libs.PSL Require Import Numbers.
From Coq Require Import Arith Lia List.
From Equations Require Import Equations.
From Undecidability.Shared.Libs.DLW.Wf Require Import wf_finite.
From Undecidability.FOL Require Import FSAT.
From Undecidability.Synthetic Require Import Definitions.
Require Export Relation_Definitions.
Require Export Setoid.
Require Export Relation_Definitions.
Set Equations With UIP.

(* ** Validity *)

(**
Idea: The special star (#) has the following properties:
n ~ p: n is left component of p
p ~ n: p is right component of p
p ~ p: the special relationship of H10UPC
n ~ m: n = m. Special case n=0, m=1: 
          The instance h10 of H10UPC is a yes-instance.
          This is to facilitate Friedman translation
*)


(*Set Default Proof Using "Type".*)
Set Default Goal Selector "!".
Inductive syms_func : Type := .

Instance sig_func : funcs_signature :=
  {| syms := syms_func; ar_syms := fun f => match f with end|}.

Inductive syms_pred := sPr.

Instance sig_pred : preds_signature :=
  {| preds := syms_pred; ar_preds := fun P => 2 |}.
(*Notation Pr t t' := (@atom _ sig_pred _ _ sPr (Vector.cons _ t _ (Vector.cons _ t' _ (Vector.nil _)))).*)


Section Utils.

  Definition c2_full (x:nat) : {y:nat | x * S x = y+y}.
  Proof. 
    induction x as [|x [y' IH]].
    - exists 0. lia.
    - exists (y'+x+1). nia.
  Defined.

  Definition c2 (x:nat) := match (c2_full x) with exist _ y _ => y end.

  Definition c2_descr (x:nat) : x * S x = c2 x + c2 x.
  Proof.
  unfold c2. now destruct (c2_full x).
  Qed. 

  Definition h10upc_sem_direct (c : h10upc) :=
    match c with 
      | ((x, y), (z1, z2)) => 
          1 + x + y = z1 /\ y * (1 + y) = z2 + z2
    end.

  Lemma h10upc_inv (a b c d : nat) : h10upc_sem_direct ((a,S b),(c,d)) -> 
           {c':nat & {d':nat & h10upc_sem_direct ((a,b),(c',d')) 
                               /\ S c' = c /\ d' + b + 1 = d}}.
  Proof.
  intros [Hl Hr].
  exists (a + S b). exists (c2 b).
  repeat split.
  - lia.
  - apply c2_descr.
  - lia.
  - enough (2*(c2 b + b + 1) = d+d) by nia. rewrite <- Hr.
    cbn. rewrite Nat.mul_comm. cbn. symmetry.
    pose (c2_descr b) as Hb. nia.
  Qed.

  Lemma h10_rel_irref (p:nat*nat) : ~ (h10upc_sem_direct (p,p)).
  Proof.
  intros H. destruct p as [a b]. cbn in H. lia.
  Qed.

  Definition highest_var (x:h10upc) := match x with ((a,b),(c,d)) => Nat.max a (Nat.max b (Nat.max c d)) end.
  Lemma highest_var_descr (x:h10upc) : let hv := highest_var x in match x with ((a,b),(c,d)) => a <= hv /\ b <= hv /\ c <= hv /\ d <= hv end.
  Proof.
  destruct x as [[a b] [c d]]. cbn. repeat split; lia.
  Qed.

  Fixpoint highest_var_list (x:list h10upc) := match x with nil => 0 | x::xr => Nat.max (highest_var x) (highest_var_list xr) end.
  Lemma highest_var_list_descr (x:list h10upc) (h:h10upc) : In h x ->  highest_var h <= highest_var_list x.
  Proof.
  induction x as [|hh x IH].
  - intros [].
  - intros [hhh|hx].
    + cbn. rewrite hhh. lia.
    + cbn. specialize (IH hx). lia.
  Qed.

  Fixpoint highest_num (env: nat -> nat) (n:nat) : nat := match n with 0 => env 0 | S n => Nat.max (env (S n)) (highest_num env n) end.
  Lemma highest_num_descr (env:nat -> nat) (n:nat) (m:nat) : m <= n -> env m <= highest_num env n.
  Proof.
  induction n as [|n IH].
  - intros Hm. assert (m=0) as Hm0. 1:lia. cbn. rewrite Hm0. lia.
  - intros HmSn. cbn. destruct (Nat.eq_dec (S n) m) as [Heq|Hneq].
    + rewrite <- Heq. lia.
    + assert (m <= n) as Hmn. 1:lia. specialize (IH Hmn). lia.
  Qed.

  Lemma it_shift (X:Type) (f:X->X) v n : it f (S n) v = it f n (f v).
  Proof.
  induction n as [|n IH].
  - easy.
  - cbn. f_equal. apply IH.
  Qed.

  Lemma it_add (X:Type) (f:X->X) v n m : it f n (it f m v) = it f (n+m) v.
  Proof.
  induction n as [|n IH].
  - easy.
  - cbn. f_equal. apply IH.
  Qed.
End Utils.

Section Fsat. (*
  Import FullSyntax.
  Open Scope syn.
  Context {h10 : list h10upc}.
  Definition N a := Pr $a $a. 
  Definition leq a b := N a ∧ N b ∧ Pr $a $b.
  Definition P' a := ¬ N a.
  Definition P p a b := P' p ∧ N a ∧ N b ∧ Pr $a $p ∧ Pr $p $b.
  Definition deq a b := ∀ (Pr $0 $(S a) <~> Pr $0 $(S b)) ∧ (Pr $(S a) $0 <~> Pr $(S b) $0).
  Definition less a b := leq a b ∧ ¬ (deq a b).
  Definition rel a b c d :=  ∃∃ P 1 (2+a) (2+b) ∧ P 0 (2+c) (2+d) ∧ Pr $1 $0.
  Definition succ l r z := rel l z r z.

  Definition aTrans := ∀∀∀ N 0 ~> N 1 ~> N 2 ~> Pr $0 $1 ~> Pr $1 $2 ~> Pr $0 $2.
  Definition aTotal := ∀∀ N 0 ~> N 1 ~> (Pr $0 $1 ∨ Pr $1 $0).
  Definition aOrder := ∀∀ N 0 ~> N 1 ~> Pr $0 $1 ~> Pr $1 $0 ~> deq 0 1.
  Definition aPred z:= ∀ N 0 ~> (¬(deq 0 (S z)) ~> ∃ succ 0 1 (2+z)).
  Definition aSucc z:= ∀∀ N 0 ~> N 1 ~> rel 0 (2+z) 1 (2+z) ~> 
                        less 0 1 ∧ ∀ less 1 0 ~> less 0 2 ~> ⊥.
  Definition aZero z := N z.

  (*Context ( aDescr : forall a b c d, N a -> N b -> N c -> N d
               -> ~(d0 == b)
               -> rel a b c d
               -> exists b' c' d', isSucc b' b /\ isSucc c' c /\ rel d' b' d d' /\ rel a b' c' d' /\ d' <<= d).
Context ( aDescr2 : forall a b c d, N a -> N b -> N c -> N d -> rel a b c d -> b == d0 -> d == d0).
*)
  Definition emplace_exists (n:nat) (f:form) := it (fun k => ∃ k) n f.
  Definition translate_single (h:h10upc) := match h with
     ((a,b),(c,d)) => rel a b c d 
  end.
  Fixpoint translate_list (h10:list h10upc) := match h10 with
     nil   => ⊥ ~> ⊥
   | x::xr => translate_single x ∧ translate_list xr
  end.
  Definition F := ∃
    aTrans ~> aTotal ~> aOrder ~> aPred 0 ~> aSucc 0 ~> aZero 0 ~>
    emplace_exists (highest_var_list h10)
    (translate_list h10).

  Section inverseTransport. 
    Definition finite (T:Type) := {l:list T & forall (x:T), In x l}.
    (*Class model := {
      D : Type;
      I : interp D;
      rho : env D;
      decP : forall a b, dec ((a .: b.: rho) ⊨ Pr $0 $1);
      fini : finite D;
      zero : D; 
      vaTrans : (zero .: rho) ⊨ aTrans;
      vaTotal : (zero .: rho) ⊨ aTotal;
      vaOrder : (zero .: rho) ⊨ aOrder;
      vaPred : (zero .: rho) ⊨ aPred 0;
      vaSucc : (zero .: rho) ⊨ aSucc 0;
      vaZero : (zero .: rho) ⊨ aZero 0;
    }.
    Context {M:model}.
    Instance II : interp D. Proof. apply I. Defined. *)
    Context (D:Type).
    Context (I:interp D).
    Context (rho : env D).
    Context (decP : forall a b, dec ((a .: b.: rho) ⊨ Pr $0 $1)).
    Context (fini : finite D).
    Context (zero : D).
    Context (vaTrans : (zero .: rho) ⊨ aTrans).
    Context (vaTotal : (zero .: rho) ⊨ aTotal).
    Context (vaOrder : (zero .: rho) ⊨ aOrder).
    Context (vaPred : (zero .: rho) ⊨ aPred 0).
    Context (vaSucc : (zero .: rho) ⊨ aSucc 0).
    Context (vaZero : (zero .: rho) ⊨ aZero 0).
    
    Notation iPr t t' := (@i_atom sig_func sig_pred D _ sPr (Vector.cons _ t _ (Vector.cons _ t' _ (Vector.nil _)))).
    
    Definition iN a := (a .: rho) ⊨ N 0.
    Definition ileq a b := (a .: b .: rho) ⊨ leq 0 1.
    Definition iP' a := (a .: rho) ⊨ P' 0.
    Definition iP p a b := (p .: a .: b .: rho) ⊨ P 0 1 2.
    Definition ideq a b := (a .: b .: rho) ⊨ deq 0 1.
    Definition iless a b := ileq a b /\ ~ ideq a b.
    Definition irel a b c d := (a.:b.:c.:d.:rho) ⊨ rel 0 1 2 3.
    Definition isucc l r := (l .: r .: zero .: rho) ⊨ succ 0 1 2.

    Lemma to_N e i : e ⊨ N i = iN (e i). Proof. easy. Qed.
    Lemma to_leq e a b : e ⊨ leq a b = ileq (e a) (e b). Proof. easy. Qed.
    Lemma to_P' e i : e ⊨ P' i = iP' (e i). Proof. easy. Qed.
    Lemma to_P e p a b : e ⊨ P p a b <-> iP (e p) (e a) (e b). Proof. easy. Qed.
    Lemma to_deq e a b : e ⊨ deq a b <-> ideq (e a) (e b). Proof. easy. Qed.
    Lemma to_less e a b : e ⊨ less a b <-> iless (e a) (e b). Proof. easy. Qed.
    Lemma to_rel e a b c d : e ⊨ rel a b c d <-> irel (e a) (e b) (e c) (e d). Proof. easy. Qed.
    Lemma to_succ e a b z : (e z = zero) -> e ⊨ succ a b z <-> isucc (e a) (e b). Proof. intros H. cbn; rewrite H. easy. Qed.

    Notation "a == b" := (ideq a b) (at level 51).
    Notation "a << b" := (iless a b) (at level 51).
    Notation "a <<= b" := (ileq a b) (at level 52).
    Instance decPr (d1 d2 :D) : dec (iPr d1 d2).
    Proof. apply decP. Defined.
    
    Lemma fin_dec (P:D->Prop) : (forall k, dec (P k)) -> dec (forall k, P k).
    Proof.
    intros HPr. assert (forall (l:list D), dec (forall k0, In k0 l -> P k0)) as H.
    - intros l. induction l as [|lx lr [IHt|IHf]].
      + left. intros v [].
      + destruct (HPr lx) as [Ht|Hf].
        * left. intros h. intros [l|r]. 1:congruence. now apply IHt.
        * right. intros Hc. apply Hf, Hc. now left.
      + right. intros Hc. apply IHf. intros k Hk. apply Hc. now right.
    - destruct fini as [l Hl]. destruct (H l) as [Ht|Hf].
      + left. intros k. apply Ht, Hl.
      + right. intros Hc. apply Hf. intros k Hk. apply Hc.
    Defined.

    Instance eqDec (d1 d2 : D) : dec (d1 == d2).
    Proof. apply fin_dec. intros k. apply and_dec; apply and_dec; apply impl_dec; apply decPr. Defined.

    Ltac firstorder' := clear vaTrans vaTotal vaOrder vaPred vaSucc; firstorder.
    Ltac recsplit n := let rec f n := match n with 0 => idtac | S ?nn => split; [idtac|f nn] end in f n.
    
    Lemma dEqRefl (d:D) : d == d.
    Proof. cbn. auto. Qed.
    Lemma dEqSymm (d1 d2:D) : d1 == d2 -> d2 == d1.
    Proof. cbn. firstorder'. Qed.
    Lemma dEqTrans (d1 d2 d3:D) : d1 == d2 -> d2 == d3 -> d1 == d3.
    Proof. cbn. intros H1 H2 d; split; split; specialize (H1 d); specialize (H2 d); firstorder'. Qed.
    
    Add Parametric Relation : D ideq
      reflexivity proved by dEqRefl
      symmetry proved by dEqSymm
      transitivity proved by dEqTrans
    as eq_rel.

    Lemma rewrite_iPr (a b a' b' : D) : iPr a b -> a==a' -> b==b'-> iPr a' b'.
    Proof. firstorder'. Qed.

    Add Parametric Morphism : ileq
      with signature ideq ==> ideq ==> iff as leq_morph.
    Proof. cbn. firstorder'. Qed.
    Add Parametric Morphism : iless
      with signature ideq ==> ideq ==> iff as less_morph.
    Proof. intros d1 d1' H1 d2 d2' H2. split; intros [Hl Hr]; split.
    - rewrite <- H1, <- H2. firstorder'.
    - intros Hc. apply Hr. now rewrite H1,H2.
    - rewrite H1, H2; firstorder.
    - intros Hc. apply Hr. now rewrite <-H1,<-H2.
    Qed.
    Add Parametric Morphism : iN
      with signature ideq ==> iff as N_morph.
    Proof. intros d1 d1' H. firstorder'. Qed.

    
    Opaque iN.
    Lemma helper_iP (a b c a' b' c':D) : iP a b c -> a==a'->b==b'->c==c' -> iP a' b' c'.
    Proof. intros [[[[Hpa Hnb] Hnc] Hpl] Hpr] Ha Hb Hc. rewrite to_N in *. rewrite to_P' in *. cbn in Hpa,Hnb,Hnc,Hpl,Hpr. split. 1:split. 1:split. 1:split.
    - rewrite to_P'. intros Hcc. apply Hpa. cbn in Hcc. now apply (rewrite_iPr Hcc).
    - rewrite to_N. cbn. now rewrite <- Hb.
    - rewrite to_N. cbn. now rewrite <- Hc.
    - now apply (rewrite_iPr Hpl).
    - now apply (rewrite_iPr Hpr).
    Qed.
    
    Add Parametric Morphism : iP
       with signature ideq ==> ideq ==> ideq ==> iff as P_morph.
    Proof.
    intros a a' Ha b b' Hb c c' Hc. split; intros H; apply (helper_iP H). all: easy.
    Qed.

    Opaque iP.
    
    Add Parametric Morphism : irel
       with signature ideq ==> ideq ==> ideq ==> ideq ==> iff as rel_morph.
    Proof.
    intros a a' Ha b b' Hb c c' Hc d d' Hd. split; intros [pl [pr [[Hl%to_P Hr%to_P] Hlr]]]; exists pl,pr; cbn in Hl,Hr; (split; [split |]). 1,2,4,5: rewrite to_P. all:cbn.
    - now rewrite <- Ha, <- Hb.
    - now rewrite <- Hc, <- Hd.
    - now rewrite Ha, Hb.
    - now rewrite Hc, Hd.
    - easy.
    - easy.
    Qed.

    Lemma eqDec_solve (d1 d2 : D) (T:Type) (X Y : T) : d1 == d2 -> (if eqDec d1 d2 then X else Y) = X.
    Proof. intros H. destruct (eqDec d1 d2); firstorder'. Qed.

    Lemma leq_deq (d1 d2 : D) : d1 == d2 -> (iN d1 \/ iN d2) -> d1 <<= d2.
    Proof. intros H [Hl|Hr]; firstorder'. Qed.

    Lemma leqTrans (d1 d2 d3 : D) : d1 <<= d2 -> d2 <<= d3 -> d1 <<= d3.
    Proof. intros H1 H2. clear vaTotal vaOrder vaPred vaSucc.
           specialize (@vaTrans d3 d2 d1). firstorder. Qed.

    Lemma lessTrans (d1 d2 d3 : D) : d1 << d2 -> d2 << d3 -> d1 << d3.
    Proof. intros [H1l H1e] [H2l H2e]. split.
    - eauto using leqTrans.
    - intros H. cbn. cbn -[deq leq] in H1e,H2e,vaOrder. apply H1e. 
      eapply vaOrder. 1-3:firstorder'. rewrite <- H in H2l. firstorder'.
    Qed.

    Lemma lessIrref (d1 : D) : ~(d1 << d1). Proof. firstorder'. Qed.

    Lemma less_wf : well_founded (fun a b => a << b).
    Proof.
    destruct fini as [l Hl]. apply wf_strict_order_list with l.
    - apply lessIrref.
    - apply lessTrans.
    - intros x y H. apply Hl.
    Qed.

    Lemma leqLessTrans (d1 d2 d3 : D) : d1 << d2 -> d2 <<= d3 -> d1 << d3.
    Proof.
    intros [H1l H1r] H2. split.
    - eauto using leqTrans.
    - cbn -[deq]. intros H3. cbn -[deq] in H1r. apply H1r.
      cbn -[deq leq] in vaOrder. apply (@vaOrder d2 d1). 1-3:firstorder'.
      rewrite <- H3 in H2. firstorder'.
    Qed.

    Lemma lessLeqTrans (d1 d2 d3 : D) : d1 <<= d2 -> d2 << d3 -> d1 << d3.
    Proof.
    intros H1 [H2l H2r]. split.
    - eauto using leqTrans.
    - cbn -[deq]. intros H3. cbn -[deq] in H2r. apply H2r.
      cbn -[deq leq] in vaOrder. apply (@vaOrder d3 d2). 1-3:firstorder'.
      rewrite H3 in H1. firstorder'.
    Qed.

    Lemma zeroNoPred (d:D) : ~ (d << zero).
    Proof.
    induction d as [d IH] using (well_founded_induction less_wf).
    destruct (Dec (d == zero)) as [Ht|Hf].
    - intros [_ Hc]. cbn -[deq] in Hc. easy.
    - intros Hc. cbn -[deq rel leq less N] in vaPred. specialize (@vaPred d).
      destruct vaPred as [d' Hd'].
      + firstorder.
      + easy.
      + unfold succ in Hd'. cbn -[deq rel leq less N] in vaSucc. specialize (@vaSucc d d').
        destruct vaSucc as [Hcc _]. 1-2:firstorder'. 1:easy. apply (IH d'). 1: exact Hcc.
        eapply lessTrans. 2: exact Hc. 1:exact Hcc.
    Qed.
    Context ( aTrans : forall x y z, N x -> N y -> N z -> x#y -> y#z -> x#z).
Context ( aTotal : forall x y, N x -> N y -> x#y \/ y#x).
Context ( aOrder : forall x y, N x -> N y -> x#y -> y#x -> deq x y).

Context ( aPred : forall r, N r -> (~(d0 == r)) -> exists l, isSucc l r).
Context ( aDescr : forall a b c d, N a -> N b -> N c -> N d
               -> ~(d0 == b)
               -> rel a b c d
               -> exists b' c' d', isSucc b' b /\ isSucc c' c /\ rel d' b' d d' /\ rel a b' c' d' /\ d' <<= d).
Context ( aDescr2 : forall a b c d, N a -> N b -> N c -> N d -> rel a b c d -> b == d0 -> d == d0).
Context ( aSucc : forall l r, N l -> N r -> rel l d0 r d0 -> isSucc l r).
    Definition chain (m:D) (mN:nat) (f:D->option nat) := 
       (forall d, d <<= m <-> f d <> None)
    /\ (forall n, (exists d, d <<= m /\ f d = Some n) -> n <= mN)
    /\ (f m = Some mN)
    /\ (f zero = Some 0)
    /\ (forall dl dh l h, f dl = Some l -> f dh = Some h -> S l = h <-> isucc dl dh)
    /\ (forall d1 d2, f d1 <> None -> f d1 = f d2 <-> d1 == d2).

    Lemma predLess l r k : isucc l r -> k << r -> k <<= l.
    Proof.
    intros Hsucc Hkr. split. 1:split; destruct Hsucc; unfold P; firstorder'. cbn.
    specialize (@vaSucc r l). fold sat in vaSucc. destruct vaSucc as [Hless Hclosed]; fold sat in *.
    1-2:firstorder'. 1: easy.
    destruct (@vaTotal k l) as [Hkl|Hlk]; fold sat in *. 1-2:firstorder'. 2:easy.
    cbn in Hkl.
    destruct (eqDec l k) as [Heq﻿@Leonard Niemann#‍1884|Neq].
    - apply rewrite_iPr with l k; easy.
    - exfalso. apply (Hclosed k); firstorder'.
    Qed. 

    Lemma chainZero : exists f, chain zero 0 f.
    Proof.
    exists (fun k => if Dec(k == zero) then Some 0 else None). recsplit 5.
    - intros k. split.
      + intros H. destruct Dec. 1:easy. exfalso. eapply zeroNoPred with k. now split.
      + destruct Dec. 2: intros H﻿@Leonard Niemann#‍1884; congruence. intros _. rewrite i. firstorder.
    - intros n [d [dZ Hd]]. destruct Dec. 2:congruence. 1:assert (n=0) by congruence; lia.
    - destruct Dec; firstorder'.
    - destruct Dec; firstorder'.
    - intros dl dh l h H1 H2. destruct Dec as [Hi1|Hi2]; destruct Dec as [Hi3|Hi4]; split; intros H.
      3-8:congruence.
      + assert (l = h) by congruence. lia.
      + exfalso. destruct (@vaSucc dh dl) as [[_ Hl] Hr]; fold sat. 1-2: firstorder'.
        1: exact H. fold sat in *. apply Hl. rewrite to_deq. cbn -[ideq]. now rewrite Hi1,Hi3.
    - intros d1 d2. destruct (Dec (d1 == zero)) as [H isSucc l rl|Hr]. 2:congruence.
      destruct (Dec (d2 == zero)) as [Hl2|Hr2]; intros _; split.
      + intros _. now rewrite Hl, Hl2.
      + easy.
      + intros H. rewrite Hl. symmetry. easy.
      + intros H. rewrite H in Hl. easy. 
    Qed. isSucc l r

    Lemma chainSucc (d:D) (n:nat) f (c:chain d n f) (d' : D) : isucc d d' -> exists f', chain d' (S n) f'.
    Proof.
    intros Hsucc. destruct c as [Hc1 [Hc2 [Hc3 [Hc4 Hc5]]]].
    assert (d << d' /\ forall k, d << k -> k << d' -> False) as [Hless Hclosed].
    1: specialize (@vaSucc d' d); apply vaSucc; fold sat in *; firstorder'.
    exists (fun k => if (Dec (k == d')) then Some (S n) else f k). recsplit 5.
    - intros k. destruct (Dec (k == d')); split.
      + easy.
      + intros _. rewrite i. firstorder'.
      + intros H. rewrite <- Hc1. apply (predLess Hsucc). now split.
      + intros H. apply leqTrans with d. 2:firstorder'. now rewrite Hc1.
    - intros n0 [d0 [dl de]]. destruct Dec as [Hl|Hr].
      + assert (n0 = S n) by congruence; lia.
      + enough (n0 <= n) by lia. apply Hc2. exists d0. split. 2:easy. apply (predLess Hsucc). now split.
    - now rewrite eqDec_solve.
    - destruct Dec as [Hl|Hr]. 2:easy. exfalso.
      eapply zeroNoPred with d. now rewrite Hl.
    - intros dl dh l h. destruct Dec as [Hl1|Hr1], Dec as [Hl2|Hr2]; intros H1 H2; split; intros H3.
      + assert (l = h) by congruence; lia.
      + exfalso. rewrite <- Hl2 in Hl1. contradict Hl1. specialize (@vaSucc dh dl); destruct (vaSucc) as [[_ Hs] Hr]; fold sat in *. 1-3:firstorder'. intros Hc. apply Hs, Hc.
      + assert (l = S n) as -> by congruence. subst h. enough (S (S n) <= n) by lia. apply Hc2. exists dh. split. 2:easy. rewrite Hc1. congruence.
      + assert (l = S n) as -> by congruence. exfalso. apply Hr2. rewrite <- Hl1. apply (vaOrder); fold sat. 1-2:firstorder. 1-2:cbn.
        * assert (dh <<= d) as Hdhd by (apply Hc1; congruence). assert (dh <<= dl) as H. 2:apply H. eapply leqTrans with d. 1:easy. rewrite Hl1; apply Hless.
        * specialize (@vaSucc dh dl); destruct vaSucc as [[H _] _2]; fold sat. 1-3:firstorder. apply H.
      + 
*)
Context {D:Type}.
Context (P : D -> D -> Prop).
Context (d0 : D).
Context (ePr : forall x y, dec (P x y)).
Notation "a # b" := (P a b) (at level 50).
    Definition finite (T:Type) := {l:list T & forall (x:T), In x l}.
Context (Dfin : finite D).

Definition N a := a # a.
Definition leq a b := N a /\ N b /\ a # b.
Notation "a <<= b" := (leq a b) (at level 51). 
Definition Pr' a := ~ N a. 
Definition Pr p a b := Pr' p /\ N a /\ N b /\ a # p /\ p # b. 
Definition deq a b := forall x, (a # x <-> b # x) /\ (x # a <-> x # b). 
Notation "a == b" := (deq a b) (at level 52). 
Definition less a b  := a <<= b /\ ~ (a == b). 
Notation "a << b" := (less a b) (at level 51). 
Definition rel a b c d  := (exists p q, Pr p a b /\ Pr q c d /\ p # q).
Definition isSucc l r := rel l d0 r d0 /\ l << r /\ forall k, k << r -> k <<= l.
Definition wIsSucc l r := rel l d0 r d0.

Context ( aTrans : forall x y z, N x -> N y -> N z -> x << y -> y << z -> x << z).
Context ( aPred : forall r, N r -> (~(d0 == r)) -> exists l, wIsSucc l r).
Context ( aDescr : forall a b c d, N a -> N b -> N c -> N d
               -> ~(d0 == b)
               -> rel a b c d
               -> exists b' c' d', wIsSucc b' b /\ wIsSucc c' c /\ rel d' b' d d' /\ rel a b' c' d' /\ d' <<= d).
Context ( aDescr2 : forall a b c d, N a -> N b -> N c -> N d -> rel a b c d -> b == d0 -> d == d0).
Context ( aSucc : forall l r, N l -> N r -> wIsSucc l r -> isSucc l r).
 
Definition chain (m:D) (mN:nat) (f:D->option nat) := 
   (forall d, d <<= m <-> f d <> None)
/\ (forall n, (exists d, d <<= m /\ f d = Some n) -> n <= mN)
/\ (f m = Some mN)
/\ (f d0 = Some 0)
/\ (forall dl dh l h, f dl = Some l -> f dh = Some h -> S l = h <-> isSucc dl dh)
/\ (forall d1 d2, f d1 <> None -> f d1 = f d2 <-> d1 == d2).

    Lemma fin_dec (Q:D->Prop) : (forall k, dec (Q k)) -> dec (forall k, Q k).
    Proof.
    intros HPr. assert (forall (l:list D), dec (forall k0, In k0 l -> Q k0)) as H.
    - intros l. induction l as [|lx lr [IHt|IHf]].
      + left. intros v [].
      + destruct (HPr lx) as [Ht|Hf].
        * left. intros h. intros [l|r]. 1:congruence. now apply IHt.
        * right. intros Hc. apply Hf, Hc. now left.
      + right. intros Hc. apply IHf. intros k Hk. apply Hc. now right.
    - destruct Dfin as [l Hl]. destruct (H l) as [Ht|Hf].
      + left. intros k. apply Ht, Hl.
      + right. intros Hc. apply Hf. intros k Hk. apply Hc.
    Defined.

    Instance eqDec (d1 d2 : D) : dec (d1 == d2).
    Proof. apply fin_dec. intros k. apply and_dec; apply and_dec; apply impl_dec; apply ePr. Defined.


Ltac firstorder' := clear aTrans aPred aDescr aDescr2 aSucc; firstorder.

Lemma deqRefl : reflexive D deq.
Proof. firstorder'. Qed.
Lemma deqSymm : symmetric D deq.
Proof. firstorder'. Qed.
Lemma deqTrans : transitive D deq.
Proof. firstorder'. Qed.
Ltac recsplit n := let rec f n := match n with 0 => idtac | S ?nn => split; [idtac|f nn] end in f n.

Lemma strongSucc l r : isSucc l r <-> wIsSucc l r.
Proof.
split.
* intros [H _]. easy. 
* intros H. apply aSucc. 1-3:firstorder'.
Qed.

Lemma leq_rewrite a b c d : a == b -> c == d -> a <<= c -> b <<= d.
Proof. firstorder'. Qed.

Lemma less_rewrite a b c d : a == b -> c == d -> a << c -> b << d.
Proof. intros H1 H2 [Hl1 Hl2]. split.
- eapply leq_rewrite. 3: exact Hl1. all:easy.
- intros Hc. apply Hl2. eapply deqTrans, deqTrans, deqSymm, H2. 1:exact H1. exact Hc.
Qed.

Lemma N_rewrite (d dd : D) : N d -> d == dd -> N dd.
Proof. intros H1 H2. firstorder'. Qed.

Lemma eqDec_eq d1 d2 T (X Y : T) : d1 == d2 -> (if eqDec d1 d2 then X else Y) = X.
Proof. intros H.
destruct (eqDec d1 d2) as [Ht|Hf].
- easy.
- exfalso;easy.
Qed.

Lemma eq_leq a b : deq a b -> (N a \/ N b) -> leq a b.
Proof. intros H H2. assert (N a) as Na.
- destruct H2 as [Hl|Hr]. 1:easy. firstorder'.
- recsplit 2.
  + easy.
  + firstorder'.
  + firstorder'.
Qed.

Lemma Pr'_rewrite (a a' : D) : a == a' -> Pr' a -> Pr' a'.
Proof. intros H Ha Hc. eapply Ha, N_rewrite. 1:apply Hc. apply deqSymm, H.
Qed.

Lemma Pr_rewrite (p p' l l' r r' : D) : p == p' -> l == l' -> r == r' -> Pr p l r -> Pr p' l' r'.
Proof.
intros Hp Hl Hr [H1 [H2 [H3 [H4 H5]]]]. recsplit 4.
- now eapply Pr'_rewrite.
- now eapply N_rewrite with l.
- now eapply N_rewrite with r.
- firstorder'.
- firstorder'.
Qed.

Lemma rel_rewrite (a b c d a' b' c' d' :D) : a==a' -> b==b' -> c==c' -> d==d' -> rel a b c d -> rel a' b' c' d'.
Proof.
intros Ha Hb Hc Hd [p [q [Hp [Hq Hpq]]]]. exists p, q. recsplit 2.
- eapply Pr_rewrite. 4:exact Hp. 1-3:easy.
- eapply Pr_rewrite. 4:exact Hq. all:easy.
- firstorder'.
Qed.


Lemma isSuccCongr l1 r1 l2 r2 : isSucc l1 r1 -> l1 == l2 -> r1 == r2 -> isSucc l2 r2.
Proof.
intros [HS1 [HS2 HS3]] Hl Hr. recsplit 2.
- apply (@rel_rewrite l1 d0 r1 d0 l2 d0 r2 d0); firstorder'.
- eapply less_rewrite. 3:exact HS2. all:firstorder'.
- intros k H1. eapply leq_rewrite. 1:easy. 2:apply HS3. 1:easy.
  eapply less_rewrite. 3:exact H1. 1:easy. now apply deqSymm.
Qed.


Lemma less_irref (x : D) : ~ (x << x).
Proof.
intros [H1 H2]. apply H2. firstorder'.
Qed.


Lemma less_trans (x y z : D) : x << y -> y << z -> x << z.
Proof.
intros H1 H2. eapply aTrans with y. all:firstorder'.
 (*intros [Hxy Nxy] [Hyz Nyz]. split.
- recsplit 2. 1-2:firstorder'. eapply aTrans with y. 1-3:firstorder'. 1-2:firstorder'.
- intros H. apply Nxy. eapply less_trans_help. 1:easy. eapply leq_rewrite. 3: exact Hyz. 1:easy. apply deqSymm. easy.*)
Qed.


Lemma leq_trans a b c : N a -> N b -> N c -> leq a b -> leq b c -> leq a c.
Proof.
intros Na Nb Nc H1 H2. recsplit 2. 1-2:firstorder'.
destruct (eqDec a b) as [Hab|Hnab], (eqDec b c) as [Hbc|Hnbc].
- eapply leq_rewrite. 3:exact H1. all:easy.
- eapply leq_rewrite. 3:exact H2. 1:now apply deqSymm. easy.
- eapply leq_rewrite. 3:exact H1. all:easy.
- assert (a << c) as Hless.
  + eapply less_trans with b; now split.
  + firstorder'.
Qed.


Lemma leq_less (a b c : D) :  a <<= b -> b << c -> a << c.
Proof.
intros H1 H2. destruct (eqDec a b) as [Heq|Hneq].
- eapply less_rewrite. 2:easy. 2:exact H2. apply deqSymm. easy.
- eapply less_trans with b. 2:easy. split; easy.
Qed.

Lemma leq_less2 (a b c : D) :  a << b -> b <<= c -> a << c.
Proof.
intros H1 H2. destruct (eqDec b c) as [Heq|Hneq].
- eapply less_rewrite. 1:easy. 1:exact Heq. easy.
- eapply less_trans with b. 1:easy. split; easy.
Qed.

Lemma less_wf : well_founded less.
Proof. 
destruct Dfin as [l Hl]. apply wf_strict_order_list with l.
- apply less_irref.
- apply less_trans.
- intros x y H. apply Hl.
Qed.

Lemma aZeroS : forall k, ~ (k << d0).
Proof.
induction k using (well_founded_ind less_wf).
intros [Hc1 Hc2]. destruct (eqDec d0 k) as [Heq|Hneq].
- apply Hc2, deqSymm, Heq.
- destruct (@aPred k) as [k' [Hk'1 [Hk'2 Hk'3]]%strongSucc ]. 1-2:firstorder'. apply (H k').
  + easy.
  + eapply leq_less2. 1:exact Hk'2. easy.
Qed.

Lemma aZero2 : forall k, N k -> d0 <<= k.
Proof.
induction k as [k IH] using (well_founded_ind less_wf).
intros Nk. destruct (eqDec d0 k) as [Heq|Hneq].
- firstorder'.
- destruct (@aPred k) as [k' [Hk'1 [Hk'2 Hk'3]]%strongSucc]. 1-2:firstorder'. eapply leq_less with k'. 2:easy.
  apply IH. 2:firstorder'. easy.
Qed.


Lemma antiSym (a b : D) : a <<= b -> b <<= a -> a == b.
Proof.
intros Ha Hb. destruct (eqDec a b) as [t|Hf]. 1:easy. 
assert (a << a) as Hc.
- eapply leq_less with b. 1:easy. split. 1:easy. now intros HHc%deqSymm.
- exfalso. destruct Hc. firstorder'.
Qed.


Lemma leqDec (a b : D) : dec (a <<= b).
Proof.
unfold leq. apply and_dec. 2:apply and_dec. 1-2:unfold N. all: apply ePr.
Defined.

(*
Lemma lessStep (a a' b b' : D) : isSucc a a' -> isSucc b b' -> a <<= b -> a' <<= b'.
Proof.
induction b as [bi IH] in a,a',b'|-* using (well_founded_ind less_wf).
destruct (eqDec d0 bi) as [Heq|Hneq].
* intros [_ [Ha1 Ha2]]. intros [_ [Hb1 Hb2]] Habi. assert (a == d0) as Ha0.
  - destruct (eqDec a d0) as [Ht|Hf]. 1:easy. exfalso. apply aZeroS with a. split. 2:easy. eapply leq_rewrite. 3:exact Habi. 2:apply deqSymm. all:easy.
  - destruct (leqDec a' b') as [Halb|Hbla]. 1:easy.
    destruct (eqDec a' b') as [Haeb|Hanb].
    + eapply leq_rewrite. 1:easy. 1:exact Haeb. firstorder'.
    + *)
(* intros H. exfalso. destruct H. eapply aZeroS with a. eapply less_rewrite. 1:easy. 1:apply deqSymm, Heq. easy.
* 
*) (*
Lemma orderNeg (a b : D) : N a -> N b -> (~(a <<= b)) -> b <<= a.
Proof.
intros Na. induction b as [bb IH] in a,Na|-* using (well_founded_ind less_wf). intros Nb.
destruct (eqDec d0 bb) as [H0|HS].
- intros H. eapply leq_rewrite. 3: apply aZero2. 1-2:easy. firstorder'.
- intros Hc. destruct (eqDec d0 a) as [Ha0|HaS]. 1: {exfalso. apply Hc. eapply leq_rewrite. 3:apply aZero2. all:easy. }
  destruct (@aPred a) as [a' Ha']. 1-2:easy. destruct (@aPred bb) as [bb' Hbb']. 1-2:easy.
  specialize (IH bb' (ltac:(firstorder'))).
  enough (bb' << a) as Hl.
  + unfold isSucc in Hbb'.
Lemma proveOrder (a b : D) : N a -> N b -> (a <<= b \/ b <<= a).
Proof.
intros Na. induction a as [k IH] in b,Na|-* using (well_founded_ind less_wf). intros Nb.
destruct (eqDec d0 k) as [Heq|Hneq].
- left. eapply leq_rewrite. 1:exact Heq. 1:easy. apply aZero2. easy.
- induction b as [bb IHb] using (well_founded_ind less_wf).
  destruct (eqDec d0 bb) as [Heqb|Hneqb].
  + right. eapply leq_rewrite. 1:exact Heqb. 1:easy. apply aZero2. easy.
  + destruct (@aPred k) as [k' Hk']. 1-2:easy. destruct (@aPred bb) as [bb' Hbb']. 1-2:easy.
    specialize (IH k'). assert (k' << k) as Hk'k by now destruct Hk'. specialize (IH Hk'k bb').
    destruct IH as [IHl|IHr]. 1-2:firstorder'. 
    * left. unfold isSucc in Hbb',Hk'. 


Lemma thing (d d' l : D) : N d -> N d' -> N l -> isSucc d d' -> l << d' -> l <<= d.
Proof.
induction l as [ll IH] in d,d'|-* using (well_founded_ind less_wf).
intros Nd Nd' Nl [H1 [H2 H3]] H4.
destruct (eqDec ll d0) as [H0|HS].
- eapply leq_rewrite. 1:apply deqSymm, H0. 1:easy. apply aZero2. easy.
-  
*)

Lemma mkchain (d:D) : N d -> exists n f, chain d n f.
Proof. induction d as [dd IH] using (well_founded_ind less_wf).
intros H. destruct (eqDec dd d0) as [H0|HS].
- exists 0, (fun k => if eqDec k dd then Some 0 else None).
  recsplit 5.
  + intros d. split. 
    * intros dl. destruct (eqDec d dd). 1:easy.
      intros _. eapply aZeroS with d. split. 1: now eapply leq_rewrite with d dd. intros HH; apply n. now eapply deqTrans with d0, deqSymm.
    * destruct (eqDec d dd) as [Hl|Hr]. 2: easy. intros _. apply eq_leq. 1:easy. left. eapply N_rewrite with dd. 1:easy. now apply deqSymm.
  + intros n.
    intros [d [ddd Hdd]]. destruct (eqDec d dd). 1: assert (n=0) by congruence;lia. easy.
  + rewrite eqDec_eq; easy.
  + rewrite eqDec_eq. 1:easy. now apply deqSymm.
  + intros dl dh l h H1 H2; split; intros H3; destruct (eqDec dl dd), (eqDec dh dd). 1-4: congruence.
    all: destruct H3 as [H31 [[H321 H322] H33]]; exfalso; apply H322; eapply deqTrans with dd, deqSymm; easy.
  + intros d1 d2. intros H1. split; intros H2; destruct (eqDec d1 dd), (eqDec d2 dd) as [Ht|Hf]. 2-5,7-8:easy.
    -- intros. now eapply deqTrans with dd, deqSymm.
    -- exfalso. apply Hf, deqSymm, deqTrans with d1. 1:now apply deqSymm. easy.
- destruct (@aPred dd) as [p Hp%strongSucc]. 1-2:firstorder'. pose proof Hp as Hpred. destruct Hp as [Hrel [Hless Hclose]].
  destruct (IH p) as [n [f Hnf]]. 1:firstorder'. 1: { firstorder'. } 
  exists (S n). exists (fun v => if eqDec v dd then Some (S n) else f v). 
  destruct Hnf as [H1 [H2 [H3 [H4 [H5 H6]]]]].
  recsplit 5.
  + intros d. split.
    * intros Hdd. destruct (eqDec d dd) as [Heq|Neq].
      -- easy.
      -- apply H1. destruct Hpred as [Hp1 [Hp2 Hp3]]. apply Hp3. now split.
    * destruct (eqDec d dd) as [Heq|Neq].
      -- intros; apply eq_leq. 1:easy. right. unfold less in Hless. unfold leq in Hless. firstorder'.
      -- intros HN. eapply leq_trans with p. 2,5:firstorder'.
        ++ rewrite <- H1 in HN. unfold leq in HN. easy.
        ++ unfold less, leq in Hless. easy.
        ++ rewrite <- H1 in HN. easy.
  + intros n0. 
    intros [d [Hddd HSome]]. destruct (eqDec d dd). 1: assert (S n = n0) by congruence;lia.
    enough (n0 <= n) by lia. apply (H2 n0). exists d. split. 2:easy. destruct Hpred as [Hp1 [Hp2 Hp3]]. apply Hp3. easy.
  + rewrite (eqDec_eq). 1:easy. firstorder'.
  + destruct (eqDec d0 dd) as [H0|Hn0]. 2: apply H4. exfalso. apply HS, deqSymm. easy.
  + intros dl dh l h HH1 HH2; split; intros HH3; destruct (eqDec dl dd) as [Hl1|Hh1], (eqDec dh dd) as [Hl2|Hh2].
    * exfalso. assert (S l = l) by congruence. lia.
    * assert (h = S (S n)) as Hc by congruence. enough (h <= n) by lia. apply H2. exists dh. split. 2:easy. apply H1. intros Hh; congruence.
    * assert (l = n) as Hc by congruence. eapply isSuccCongr with p dd. 1:easy.
      -- apply H6. 1: intros;congruence. congruence.
      -- apply deqSymm; easy.
    * apply H5 with l h; easy.
    * destruct HH3 as [H31 [[H321 H322] H33]]; exfalso; apply H322; eapply deqTrans with dd, deqSymm; easy.
    * exfalso. apply less_irref with dd. eapply less_trans with dh.
      -- eapply less_rewrite. 1:exact Hl1. 1:easy. now destruct HH3.
      -- eapply leq_less with p. 2:easy. rewrite H1. congruence.
    * eapply isSuccCongr in HH3. 2:easy. 2:exact Hl2.
      assert (dl == p) as Hdlp. 
      -- destruct Hpred as [Hp1 [Hp2 Hp3]], HH3 as [H31 [H32 H33]].
         apply antiSym.
         ++ apply Hp3. easy.
         ++ apply H33. easy.
      -- assert (f p = f dl) as Heq.
         ++  apply H6. 1:congruence. now apply deqSymm.
         ++ assert (n = l) by congruence. subst n. congruence.
    * erewrite H5. 1:exact HH3. all:easy.
  + intros d1 d2. intros HSome. split; intros Heq; destruct (eqDec d1 dd) as [Htt|Hff], (eqDec d2 dd) as [Ht|Hf].
    -- now apply deqTrans with dd, deqSymm.
    -- exfalso. enough (S n <= n) by lia. apply H2. exists d2. split. 2:easy. apply H1. congruence.
    -- exfalso. enough (S n <= n) by lia. apply H2. exists d1. split. 2:easy. apply H1. congruence.
    -- now apply H6.
    -- easy.
    -- exfalso. apply Hf, deqSymm, deqTrans with d1. 1:now apply deqSymm. easy.
    -- exfalso. apply Hff, deqTrans with d2; easy.
    -- apply H6; easy.
Qed.

Lemma chain_proves (a b c d m: D) (nm : nat) (f:D->option nat): chain m nm f -> b <<= m -> rel a b c d 
             -> a <<= m -> c <<= m -> d <<= m
             -> exists a' b' c' d', h10upc_sem_direct ((a',b'),(c',d')) /\ 
                   f a = Some a' /\ f b = Some b' /\ f c = Some c' /\ f d = Some d'.
Proof.
intros Hf. pose Hf as HHf. destruct HHf as [Hf1 [Hf2 [Hf3 [Hf4 [Hf5 Hf6]]]]].
induction b as [b IH] in a,c,d|-* using (well_founded_ind less_wf); intros Hb Habcd Ha Hc Hd.
destruct (eqDec b d0).
- destruct (f a) as [na|] eqn:Heqfa. 2: exfalso; apply (Hf1 a); easy.
  exists na, 0, (S na), 0. recsplit 4. 1:easy.
  + easy.
  + rewrite <- Hf4. apply Hf6. 1:firstorder'. easy.
  + assert (isSucc a c) as Hsucc.
    * apply aSucc. 1-2:firstorder'. eapply (rel_rewrite). 5:exact Habcd. 1-3:easy. eapply aDescr2. 5:exact Habcd. 1-4:firstorder'. easy.   
    * destruct (f c) as [Sna|] eqn:Hfc.
      -- f_equal. symmetry. erewrite (Hf5 a c); easy.
      -- exfalso. contradict Hfc. rewrite <- Hf1. easy.
  + assert (d == d0) as Hdd0. 1: eapply aDescr2. 5: exact Habcd. 1-4:firstorder'. 1:easy. rewrite <- Hf4. symmetry. rewrite Hf6. 1: now apply deqSymm. congruence.
- destruct (@aDescr a b c d) as [b' [c' [d' [[Hb'1 [Hb'2 Hb'3]]%strongSucc [[Hc'1 [Hc'2 Hc'3]]%strongSucc [Hr1 [Hr2 Hdd']]]]]]]. 1-6:firstorder'.
  specialize (IH b' (ltac:(firstorder)) ). pose proof ((proj1 (leq_less2 Hb'2 Hb))) as Hbb.
  edestruct (IH _ _ _ Hbb Hr1) as [nd' [nb' [nd [nd'2 Hdbdd]]]]. 4:
  edestruct (IH _ _ _ Hbb Hr2) as [na [nb'2 [nc' [nd'3 Habcd2]]]].
  2,4:easy. 3: apply leq_less2 with c; easy. 1-3: apply leq_trans with d;firstorder'.
  exists na, (S nb'), (S nc'), (1+nb'+nd'). recsplit 4.
  + destruct (Hdbdd) as [Hdbdd1 Hdbdd2], Habcd2 as [Habcd21 Habcd22]. cbn in Habcd21, Hdbdd1. 
    assert (nd'2 = nd') as ->.
    1: {destruct Hdbdd2 as [Heq1 [Heq2 [Heq3 Heq4]]]; congruence. }
    assert (nd'3 = nd') as ->.
    1: {destruct Hdbdd2 as [Heq1 [Heq2 [Heq3 Heq4]]], Habcd22 as [Heq5 [Heq6 [Heq7 Heq8]]]; congruence. }
    assert (nb'2 = nb') as ->.
    1: {destruct Hdbdd2 as [Heq1 [Heq2 [Heq3 Heq4]]], Habcd22 as [Heq5 [Heq6 [Heq7 Heq8]]]; congruence. }
    cbn; split; lia.
  + firstorder'.
  + destruct (f b) as [nb|] eqn:Hfb. 2: now apply Hf1 in Hfb.
    f_equal. symmetry. rewrite (Hf5 b' b). 3:easy. 2:firstorder'. recsplit 2; easy.
  + destruct (f c) as [nc|] eqn:Hfc. 2: now apply Hf1 in Hfc.
    f_equal. symmetry. rewrite (Hf5 c' c). 3:easy. 2:firstorder'. recsplit 2; easy.
  + assert (f d = Some nd) as -> by firstorder congruence. f_equal. cbn in *. lia.
Qed.

Context {h10 : list h10upc}.

Definition translate_single (env : nat -> D) (m:D) '(((a,b),(c,d)) : h10upc) := 
  rel (env a) (env b) (env c) (env d) /\ (env a) <<= m /\ (env b) <<= m /\ (env c) <<= m /\ (env d) <<= m.
Fixpoint translate_all (k:list h10upc) m (env : nat -> D) := match k with nil => True 
| (x::xr) => translate_single env m x /\ translate_all xr m env end.
Fixpoint emplace_exists (n:nat) (f:(nat->D)->Prop) := match n with 0 => f  (fun _ => d0)
| S n => emplace_exists n (fun k => exists dd, f (fun v => match v with 0 => dd | S vv => k vv end)) end.
Definition FF (h10:list h10upc) := exists m, N m /\ emplace_exists (S (highest_var_list h10)) (translate_all h10 m).

Lemma destruct_exists n f : emplace_exists n f -> exists (env:nat -> D), f env.
Proof.
induction n as [|n IH] in f|-*.
- intros H. exists (fun _ => d0). exact H.
- cbn. intros [env [d Henv]]%IH.
  eexists. exact Henv.
Qed.

Lemma translate_all_in h m e : translate_all h m e -> forall k, In k h -> translate_single e m k.
Proof.
induction h as [|hx hr IH].
- easy.
- intros [Hhx Hhr] k [Hkx|Hkr].
  + congruence.
  + now apply IH.
Qed.

Lemma reduction : FF h10 -> H10UPC_SAT h10.
Proof.
intros [m [Nm [env HFF]%destruct_exists]].
destruct (@mkchain m Nm) as [n [f Hchain]].
pose (fun n => match f (env n) with Some v => v | _ => 0 end) as ff.
exists ff.
intros [[a b][c d]] Hc.
destruct (translate_all_in HFF Hc) as [Hrel [Ham [Hbm [Hcm Hdm]]]].
destruct (@chain_proves (env a) (env b) (env c) (env d) m n f) as 
   [ffa [ffb [ffc [ffd [Hsem [Hffa [Hffb [Hffc Hffd]]]]]]]]. 1-6:easy.
cbn. unfold ff. rewrite Hffa, Hffb, Hffc, Hffd. apply Hsem.
Qed.





Lemma blackhole : True.
Proof.
pose chain_proves.
pose mkchain.
easy.
Qed. 

End Fsat.

Section model.

Context (max:nat).
Context (Hmax : max > 0).

Lemma le0 (n:nat) : 0 <= n. Proof. lia. Qed.
Lemma leS {n m : nat} : n <= m -> S n <= S m. Proof. lia. Qed.
Inductive finNum (m:nat) : Type := fN : forall n, n <= m -> finNum m.

Inductive model (m:nat) : Type := 
  Number (n : finNum m)
|   Pair (a b : finNum m).


Lemma finiteNat m : finite (finNum m).
Proof.
induction m as [|m [l Hl]].
- eexists ((fN (le0 0)) :: nil). intros [n H]. assert (n=0) as ->.  
  + lia.
  + cbn. left. f_equal. apply le_unique.
- hnf. exists ((fN (le0 (S m))) :: map (fun k => match k with @fN _ n Hn => fN (leS Hn) end) l).
  intros [[|n] Hn].
  + cbn. left. f_equal. apply le_unique.
  + cbn. right. apply in_map_iff. assert (n <= m) as Hn' by lia.
    exists (fN Hn'). split. 2:easy. f_equal. apply le_unique.
Qed.

Lemma finiteModel m : finite (model m).
Proof.
destruct (finiteNat m) as [l Hl].
exists (map (@Number m) l ++ flat_map (fun a => map (@Pair m a) l) l).
intros [n|a b]; apply in_or_app.
* left. now apply in_map.
* right. apply in_flat_map_Exists, Exists_exists. exists a. split. 1:easy.
  apply in_map. easy.
Qed.

Definition model_rel (m:nat) (a b : model m) : Prop := match (a,b) with
  (Number (@fN _ n1 _), Number (@fN _ n2 _)) => n1 <= n2
| (Pair _ (@fN _ r _), Number (@fN _ n _)) => r = n
| (Number (@fN _ n _), Pair (@fN _ l _) _) => n = l
| (Pair (@fN _ a _) (@fN _ b _), Pair (@fN _ c _) (@fN _ d _)) => h10upc_sem_direct ((a,b),(c,d)) end.

Definition my0 (m:nat) := Number (fN (le0 m)).

Lemma Nelim x : N (model_rel (m:=max)) x <-> exists (n:nat) (u:n<=max), x = Number (fN u).
Proof. split.
* intros H. destruct x as [[n Hn]|[a b] [c d]].
  - now exists n, Hn.
  - cbn in H. exfalso. lia.
* intros [n [u H]]. rewrite H. cbn. lia.
Qed.

Lemma differentNums (base:finNum max) : exists (m1 m2 : finNum max), m1 <> m2 /\ (
  (model_rel (Number m1) (Number base) /\ model_rel (Number m2) (Number base))
\/(model_rel (Number base) (Number m1) /\ model_rel (Number base) (Number m2))
).
Proof.
destruct base as [[|n] Hn].
* eexists (@fN max 0 _).
  eexists (@fN max 1 _).
  split.
  - intros H. congruence.
  - right. cbn. lia.
* eexists (@fN max 0 _).
  eexists (@fN max 1 _).
  split.
  - intros H. congruence.
  - left. cbn. lia.
Unshelve. all: lia.
Qed.


Lemma deqElim l r : deq (model_rel (m:=max)) l r <-> l = r.
Proof. destruct l as [[n1 Hn1]|[a Ha] [b Hb]], r as [[n2 Hn2]|[c Hc] [d Hd]]; split.
* unfold deq. intros H. specialize (H (Pair (fN Hn1) (fN Hn1))). cbn in H. assert (n1 = n2) as -> by firstorder congruence. do 2 f_equal. apply le_unique.
* intros ->.  unfold deq. firstorder.
* intros H. destruct (differentNums (fN Hn1)) as [m1 [m2 [Hm12 [[Hm2a1 Hm2a2]|[Hm2b1 Hm2b2]]]]];
  pose proof (H (Number m1)) as [Hl1 Hl2]; pose proof (H (Number m2)) as [Hh1 Hh2]; destruct m1 as [nm1 Hm1], m2 as [nm2 Hm2].
  - cbn in Hl2,Hh2,Hm2a1,Hm2a2. rewrite Hl2 in Hm2a1. rewrite Hh2 in Hm2a2. contradict Hm12. assert (nm1 = nm2) as -> by congruence. f_equal. apply le_unique.
  - cbn in Hl1,Hh1,Hm2b1,Hm2b2. rewrite Hl1 in Hm2b1. rewrite Hh1 in Hm2b2. contradict Hm12. assert (nm1 = nm2) as -> by congruence. f_equal. apply le_unique.
* intros H. discriminate.
* intros H. destruct (differentNums (fN Hn2)) as [m1 [m2 [Hm12 [[Hm2a1 Hm2a2]|[Hm2b1 Hm2b2]]]]];
  pose proof (H (Number m1)) as [Hl1 Hl2]; pose proof (H (Number m2)) as [Hh1 Hh2]; destruct m1 as [nm1 Hm1], m2 as [nm2 Hm2].
  - cbn in Hl2,Hh2,Hm2a1,Hm2a2. rewrite <- Hl2 in Hm2a1. rewrite <- Hh2 in Hm2a2. contradict Hm12. assert (nm1 = nm2) as -> by congruence. f_equal. apply le_unique.
  - cbn in Hl1,Hh1,Hm2b1,Hm2b2. rewrite <- Hl1 in Hm2b1. rewrite <- Hh1 in Hm2b2. contradict Hm12. assert (nm1 = nm2) as -> by congruence. f_equal. apply le_unique.
* intros H. discriminate.
* intros H. pose proof (H (Number (fN Ha))) as HHa. pose proof (H (Number (fN Hb))) as HHb.
  cbn in H, HHa, HHb. cbn. f_equal.
  - assert (a = c) as -> by firstorder congruence. f_equal. apply le_unique.
  - assert (d = b) as -> by firstorder congruence. f_equal. apply le_unique.
* intros ->. firstorder.
Qed.

Lemma elimPr (p l r : model max) : Pr (model_rel (m:=max)) p l r <-> exists (nl nr : finNum max), l = Number nl /\ r = Number nr /\ p = Pair nl nr.
Proof.
split.
- unfold Pr, Pr'. rewrite ! Nelim. intros [Hp [[nl [ul ->]] [[nr [ur ->]] [H1 H2]]]]. destruct p as [nn|nnl nnr].
  + contradict Hp. destruct nn as [nn Hnn]. exists nn, Hnn. f_equal.
  + clear Hp. exists (@fN max nl ul). exists ((@fN max nr ur)). split. 1:easy. split. 1:easy.
    destruct nnl as [nnl Hnnl], nnr as [nnr Hnnr]; f_equal; cbn in *. all: revert ul ur.
    * rewrite H1. intros ul _. f_equal. apply le_unique.
    * rewrite <- H2. intros _ ur. f_equal. apply le_unique.
- intros [nl [nr [-> [-> ->]]]]. destruct nl as [nl Hnl], nr as [nr Hnr]. unfold Pr, Pr'. rewrite !Nelim. split. 2:split. 3:split. 4:split.
  + intros [n [u H]]. congruence.
  + exists nl, Hnl. easy.
  + exists nr, Hnr. easy.
  + easy.
  + easy.
Qed.

Lemma leqElim a b : leq (model_rel (m:=max)) a b <-> exists na Ha nb Hb, a = Number (@fN max na Ha) /\ b = Number (@fN max nb Hb) /\ na <= nb.
Proof. split.
* unfold leq. rewrite !Nelim. intros [[na [ua ->]] [[nb [ub ->]] H]]. exists na, ua, nb, ub.
  cbn in H. easy.
* intros [na [ua [nb [ub [-> [-> H]]]]]]. unfold leq. cbn. lia.
Qed.

Lemma lessElim a b : less (model_rel (m:=max)) a b <-> exists na Ha nb Hb, a = Number (@fN max na Ha) /\ b = Number (@fN max nb Hb) /\ na < nb.
Proof. split.
* unfold less. rewrite !deqElim, !leqElim. intros [[na [ua [nb [ub [-> [-> H]]]]]]Nab]. exists na,ua,nb,ub. split. 2:split. 1-2: easy. assert (na <> nb) as Heq.
  - intros Hh. contradict Nab. f_equal. revert ub. rewrite <- Hh. intros ub. f_equal. apply le_unique.
  - lia.
* intros [na [ua [nb [ub [-> [-> H]]]]]]. unfold less.  rewrite !deqElim, !leqElim. split.
  - exists na,ua,nb,ub. firstorder lia.
  - intros HH. contradict H. assert (na = nb) by congruence. lia.
Qed.

Lemma relElim (a b c d : nat) ua ub uc ud: rel (model_rel (m:=max)) (Number (@fN max a ua)) (Number (@fN max b ub)) (Number (@fN max c uc))
  (Number (@fN max d ud)) <-> h10upc_sem_direct((a,b),(c,d)).
Proof. split.
* intros [p [q Hpq]]. rewrite !elimPr in Hpq.
  destruct Hpq as [[nl [nr H1]] [[nl2 [nr2 H2]] Hpq]].
  assert (nl = fN ua) as Hnl by firstorder congruence.
  assert (nr = fN ub) as Hnr by firstorder congruence.
  assert (nl2 = fN uc) as Hnl2 by firstorder congruence.
  assert (nr2 = fN ud) as Hnr2 by firstorder congruence.
  subst nl nr nl2 nr2. destruct H1 as [H11 [H12 H13]], H2 as [H21 [H22 H23]].
  subst p q. cbn in Hpq. cbn. lia.
* intros H. exists (Pair (fN ua) (fN ub)), (Pair (fN uc) (fN ud)). rewrite ! elimPr. split. 2:split. 3:easy.
  - exists (fN ua), (fN ub). easy.
  - exists (fN uc), (fN ud). easy.
Qed.

Lemma proveSucc (n:nat) (Hn : n <= max) (Hn' : (S n) <= max) : isSucc (model_rel (m:=max)) (my0 max) (Number (fN Hn)) (Number (fN Hn')).
Proof.
unfold isSucc, rel. split. 2:split. 
* exists (Pair ((fN Hn)) (fN (le0 max))), (Pair ((fN Hn')) (fN (le0 max))). rewrite ! elimPr. split. 2:split.
  + exists (fN Hn), (fN (le0 max)). easy.
  + exists (fN Hn'), (fN (le0 max)). easy.
  + cbn. lia.
* rewrite lessElim. exists n, Hn, (S n), Hn'. firstorder lia.
* intros [[nn un]|l r].
  + rewrite ! lessElim. intros [na [Ha [nb [Hb [HHa [HHb Hab]]]]]].
    rewrite ! leqElim. exists nn,un,n,Hn. split. 2:split. 1-2:easy.
    assert (nn = na) as -> by congruence.
    assert (S n = nb) as HSn by congruence. lia.
  + rewrite ! lessElim. intros [na [Ha [nb [Hb [HHa [HHb Hab]]]]]].
    rewrite ! leqElim. congruence.
Qed.

Lemma check : True.
Proof.
apply (@blackhole (model max) (@model_rel max) (my0 max)).
* intros [[n Hn]|[a Ha] [b Hb]] [[n2 Hn2]|[c Hc] [d Hd]].
  + unfold dec. cbn. destruct (Nat.leb n n2) eqn:H; [left|right].
    -- now apply leb_complete in H.
    -- apply leb_complete_conv in H. lia.
  + cbn. unfold dec. decide equality.
  + cbn. unfold dec. decide equality.
  + cbn. apply and_dec; unfold dec; decide equality.
* apply finiteModel.
* intros x y z. rewrite ! Nelim. intros [x' [Hx' ->]] [y' [Hy' ->]] [z' [Hz' ->]].
  rewrite ! lessElim. intros [na [ua [nb [ub [H1 [H2 H3]]]]]] [nb' [ub' [nc [uc [H4 [H5 H6]]]]]].
  exists na,ua,nc,uc. split. 1:congruence. split. 1:congruence. assert (nb = nb') by congruence. lia.
 (*intros x y. rewrite ! Nelim. intros [x' [Hx' ->]] [y' [Hy' ->]]. cbn. intros H1 H2. 
  rewrite deqElim. f_equal. assert (x' = y') as -> by lia. f_equal. apply le_unique. *)
* intros k. rewrite deqElim, Nelim. intros [[|n] [u ->]] Hn0.
  - contradict Hn0. cbv. f_equal. f_equal. apply le_unique.
  - eexists (Number (@fN max n _)). apply proveSucc.
    Unshelve. lia.
* intros a b c d. rewrite ! Nelim. intros [na [ua ->]] [nb [ub ->]] [nc [uc ->]] [nd [ud ->]].
  rewrite ! deqElim. intros Hb0.
  intros Hrel%relElim.
  assert (nb <> 0) as Hb0'.
  1: { intros H. subst nb. apply Hb0. cbv. f_equal. f_equal. apply le_unique. }
  destruct nb as [|nb']. 1:easy.
  destruct (h10upc_inv  Hrel) as [nc' [nd' HH]].
  assert (nb' <= max) as ub' by lia.
  assert (nc' <= max) as uc' by lia.
  assert (nd' <= max) as ud' by lia.
  exists (Number (fN ub')), (Number (fN uc')), (Number (fN ud')).
  rewrite ! relElim. split. 2:split. 3:split. 4:split.
  - apply proveSucc.
  - assert (S nc' = nc) as <- by lia. apply proveSucc.
  - cbn. cbn in HH. nia.
  - cbn. cbn in HH. nia.
  - rewrite leqElim. exists nd', ud', nd, ud. split. 2:split. 1-2:easy. lia.
* intros a b c d. rewrite ! Nelim. intros [na [ua ->]] [nb [ub ->]] [nc [uc ->]] [nd [ud ->]].
  rewrite ! deqElim. 
  intros Hrel%relElim. intros H. cbn in Hrel. cbv in H. assert (nb = 0) as -> by firstorder congruence.
  assert (nd = 0) as -> by lia. cbv. f_equal. f_equal. apply le_unique.
* intros l r. rewrite !Nelim. intros [nl [ul ->]] [nr [ur ->]].
  intros Hrel%relElim. cbn in Hrel. assert (nr = S nl) as -> by lia. apply proveSucc.
Qed.

End model.




