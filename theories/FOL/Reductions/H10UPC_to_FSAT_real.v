(* * FOL Reductions *)
Require Import Vector.
From Undecidability.DiophantineConstraints Require Import H10UPC H10UPC_undec.
From Undecidability.FOL Require Import Util.Syntax Util.FullDeduction Util.FullTarski Util.Syntax Util.Syntax_facts Util.FullTarski_facts.
From Undecidability.Shared Require Import Dec.
From Undecidability.Shared.Libs.PSL Require Import Numbers.
From Coq Require Import Arith Lia List.
From Equations Require Import Equations.
From Undecidability.Shared.Libs.DLW.Wf Require Import wf_finite.
From Undecidability.FOL Require Import FSAT DoubleNegation.
From Undecidability.Synthetic Require Import Definitions.
Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Datatypes.
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
n ~ m: n <= m. Special case n=0, m=1: 
          The instance h10 of H10UPC is a yes-instance.
          This is to facilitate Friedman translation
*)


Set Default Proof Using "Type".
Set Default Goal Selector "!".
Set Mangle Names.
Inductive syms_func : Type := .

Instance sig_func : funcs_signature :=
  {| syms := syms_func; ar_syms := fun f => match f with end|}.

Inductive syms_pred := sPr.

Instance sig_pred : preds_signature :=
  {| preds := syms_pred; ar_preds := fun P => 2 |}.
Notation "t ## t'" := (@atom _ sig_pred _ _ sPr (Vector.cons _ t _ (Vector.cons _ t' _ (Vector.nil _)))) (at level 30).
Definition Pr t t' := t ## t'.
Derive Signature for t.

Section Utils.

  Definition proj_vec2 D : t D 2 -> D*D.
  Proof.
    intros k. refine (match k with Vector.nil _ => _ | Vector.cons _ x n xr => _ end). 1:easy.
    destruct n as [|[|n]]. 1,3:easy.
    refine (match xr with Vector.nil _ => _ | Vector.cons _ y n yr => _ end). 1:easy.
    destruct n as [|n]. 2:easy.
    exact (x,y).
  Defined. 

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

  Fixpoint highest_var_list (x:list h10upc) := match x with Datatypes.nil => 0 | x::xr => Nat.max (highest_var x) (highest_var_list xr) end.
  Lemma highest_var_list_descr (x:list h10upc) (h:h10upc) : List.In h x ->  highest_var h <= highest_var_list x.
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

Section Fsat. 
  Import FullSyntax.
  Open Scope syn.
  Context {h10 : list h10upc}.
  Definition N a := $a ## $a. 
  Definition leq a b := N a ∧ N b ∧ $a ## $b.
  Definition P' a := ¬ N a.
  Definition P p a b := P' p ∧ N a ∧ N b ∧ $a ## $p ∧ $p ## $b.
  Definition deq a b := ∀ ($0 ## $(S a) <~> $0 ## $(S b)) ∧ ( $(S a) ## $0 <~> $(S b) ## $0). 
  Definition less a b := leq a b ∧ ¬ (deq a b). 
  Definition rel a b c d := ∃∃ P 1 (2+a) (2+b) ∧ P 0 (2+c) (2+d) ∧ $1 ## $0.
  Definition succ l r z := rel l z r z.

  Definition aTrans := ∀∀∀ less 2 1 ~> less 1 0 ~> less 2 0.
  Definition aPred z:= ∀ N 0 ~> (¬(deq (S z) 0) ~> ∃ succ 0 1 (2+z)).
  Definition aSucc z:= ∀∀ N 1 ~> N 0 ~> rel 1 (2+z) 0 (2+z) ~> 
                        less 1 0 ∧ ∀ less 0 1 ~> leq 0 2.
  Definition aDescr z := ∀∀∀∀ N 3 ~> N 2 ~> N 1 ~> N 0
                           ~> (¬(deq (4+z) 2))
                           ~> rel 3 2 1 0
                       ~> ∃∃∃ succ 2 5 (7+z) ∧ succ 1 4 (7+z) ∧ rel 0 2 3 0 ∧ rel 6 2 1 0 ∧ less 0 3.
  Definition aDescr2 z := ∀∀∀∀ N 3 ~> N 2 ~> N 1 ~> N 0 ~> rel 3 2 1 0 ~> deq 2 (4+z) ~> deq 0 (4+z).

  Definition emplace_exists (n:nat) (f:form) := it (fun k => ∃ k) n f.
  Definition translate_single (h:h10upc) m := match h with
     ((a,b),(c,d)) => rel a b c d
                    ∧ leq a m ∧ leq b m ∧ leq c m ∧ leq d m
  end.
  Fixpoint translate_list m (h10:list h10upc) := match h10 with
     nil   => ⊥ ~> ⊥
   | x::xr => translate_single x m ∧ translate_list m xr
  end.
  Definition F := ∃∃
    aTrans ∧ aPred 1 ∧ aSucc 1 ∧ aDescr 1 ∧ aDescr2 1 ∧ 
    emplace_exists (S (highest_var_list h10))
    (translate_list (S (highest_var_list h10)) h10).

  Section inverseTransport. 
    Definition finite (T:Type) := {l:list T & forall (x:T), In x l}.
    Context (D:Type).
    Context (I:interp D).
    Context (rho : env D).
    Context (decP : forall a b, dec ((a .: b.: rho) ⊨ Pr $0 $1)).
    Context (fini : finite D).
    
    Notation iPr t t' := (@i_atom sig_func sig_pred D _ sPr (Vector.cons _ t _ (Vector.cons _ t' _ (Vector.nil _)))).
    Notation "a # b" := (iPr a b) (at level 50).
    Definition iN a := a # a.
    Definition ileq a b := iN a /\ iN b /\ a # b.
    Definition iP' a := ~iN a.
    Definition iP p a b := iP' p /\ iN a /\ iN b /\ a # p /\ p # b.
    Definition ideq a b := forall x, (x # a <-> x # b) /\ ( a # x <-> b # x).
    Definition iless a b := ileq a b /\ ~ (ideq a b).
    Definition irel a b c d := exists pl pr, iP pl a b /\ iP pr c d /\ pl # pr.
    Definition isucc l r z := irel l z r z.

    Lemma to_N e i : e ⊨ N i = iN (e i). Proof. easy. Qed.
    Lemma to_leq e a b : e ⊨ leq a b <-> ileq (e a) (e b). Proof. clear fini. cbn. unfold ileq,iN. firstorder. Qed.
    Lemma to_P' e i : e ⊨ P' i <-> iP' (e i). Proof. clear fini. firstorder. Qed.
    Lemma to_P e p a b : e ⊨ P p a b <-> iP (e p) (e a) (e b). Proof. clear fini. firstorder. Qed.
    Lemma to_deq e a b : e ⊨ deq a b <-> ideq (e a) (e b). Proof. clear fini. firstorder. Qed.
    Lemma to_less e a b : e ⊨ less a b <-> iless (e a) (e b). Proof. clear fini. firstorder. Qed.
    Lemma to_rel e a b c d : e ⊨ rel a b c d <-> irel (e a) (e b) (e c) (e d). Proof. clear fini. 
    split.
    - intros [p [q [[Hp Hq] Hpq]]]. exists p,q. firstorder.
    - intros [p [q [Hp [Hq Hpr]]]]. exists p,q. firstorder.
    Qed.
    Lemma to_succ e a b z : e ⊨ succ a b z <-> isucc (e a) (e b) (e z). Proof.
    clear fini. unfold succ, isucc. now rewrite to_rel. Qed.

    Notation "a == b" := (ideq a b) (at level 51).
    Notation "a << b" := (iless a b) (at level 51).
    Notation "a <<= b" := (ileq a b) (at level 52).
    Instance decPr (d1 d2 :D) : dec (iPr d1 d2).
    Proof using decP. apply decP. Defined.
    
    Lemma fin_dec (P:D->Prop) : (forall k, dec (P k)) -> dec (forall k, P k).
    Proof using fini.
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
    Proof using fini decP.
    apply fin_dec. intros k. apply and_dec; apply and_dec; apply impl_dec; apply decPr.
    Defined.
   
    Lemma dEqRefl (d:D) : d == d.
    Proof. cbn. clear fini. firstorder. Qed.
    Lemma dEqSymm (d1 d2:D) : d1 == d2 -> d2 == d1.
    Proof. cbn. clear fini. firstorder. Qed.
    Lemma dEqTrans (d1 d2 d3:D) : d1 == d2 -> d2 == d3 -> d1 == d3.
    Proof. cbn. clear fini. intros H1 H2 d; split; split; specialize (H1 d); specialize (H2 d); firstorder. Qed.
    
    Add Parametric Relation : D ideq
      reflexivity proved by dEqRefl
      symmetry proved by dEqSymm
      transitivity proved by dEqTrans
    as eq_rel.

    Lemma rewrite_iPr (a b a' b' : D) : iPr a b -> a==a' -> b==b'-> iPr a' b'.
    Proof. clear fini. firstorder. Qed.

    Add Parametric Morphism : ileq
      with signature ideq ==> ideq ==> iff as leq_morph.
    Proof. cbn. clear fini.  firstorder. Qed.
    Add Parametric Morphism : iless
      with signature ideq ==> ideq ==> iff as less_morph.
    Proof. intros d1 d1' H1 d2 d2' H2. split; intros [Hl Hr]; clear fini; split.
    - rewrite <- H1, <- H2. firstorder.
    - intros Hc. apply Hr. now rewrite H1,H2.
    - rewrite H1, H2; firstorder.
    - intros Hc. apply Hr. now rewrite <-H1,<-H2.
    Qed.
    Add Parametric Morphism : iN
      with signature ideq ==> iff as N_morph.
    Proof. intros d1 d1' H. clear fini.  firstorder. Qed.

    
    Opaque iN.
    Lemma helper_iP (a b c a' b' c':D) : iP a b c -> a==a'->b==b'->c==c' -> iP a' b' c'.
    Proof. intros [Hpa [Hnb [Hnc [Hpl Hpr]]]] Ha Hb Hc. cbn in Hpa,Hnb,Hnc,Hpl,Hpr. split. 2:split. 3:split. 4:split.
    - intros Hcc. apply Hpa. cbn in Hcc. now rewrite Ha.
    - now rewrite <- Hb.
    - now rewrite <- Hc.
    - now apply (rewrite_iPr Hpl).
    - now apply (rewrite_iPr Hpr).
    Qed.
    
    Add Parametric Morphism : iP
       with signature ideq ==> ideq ==> ideq ==> iff as P_morph.
    Proof.
    intros a a' Ha b b' Hb c c' Hc. split; intros H; apply (helper_iP H). all: easy.
    Qed.
    
    Add Parametric Morphism : irel
       with signature ideq ==> ideq ==> ideq ==> ideq ==> iff as rel_morph.
    Proof.
    intros a a' Ha b b' Hb c c' Hc d d' Hd. split; intros [pl [pr [Hl [Hr Hlr]]]]; exists pl,pr; cbn in Hl,Hr; (split; [|split]).
    - now rewrite <- Ha, <- Hb.
    - now rewrite <- Hc, <- Hd.
    - easy.
    - now rewrite Ha, Hb.
    - now rewrite Hc, Hd.
    - easy.
    Qed.

    Add Parametric Morphism : isucc
      with signature ideq ==> ideq ==> ideq ==> iff as succ_morph.
    Proof.
    intros l l' Hl r r' Hr z z' Hz. unfold isucc. now rewrite Hl,Hr,Hz.
    Qed.

    Lemma leq_eq a b : iN b -> a == b -> a <<= b.
    Proof.
    intros H ->. split. 1:easy. split. 1:easy. easy.
    Qed.

    Opaque N leq P' P deq less rel succ.

    Section withAxioms.

      Context {m z : D}.
      Context {rho' : env D}.
      Context {Hrho : rho' = (m.:z.:rho)}.
      Context {vTrans : rho' ⊨ aTrans}.
      Context {vPred  : rho' ⊨ aPred 1}.
      Context {vSucc  : rho' ⊨ aSucc 1}.
      Context {vDescr : rho' ⊨ aDescr 1}.
      Context {vDescr2: rho' ⊨ aDescr2 1}.
      
      Definition chain (m:D) (mN:nat) (f:D->option nat) := 
         (forall d, d <<= m <-> f d <> None)
      /\ (forall n, (exists d, d <<= m /\ f d = Some n) -> n <= mN)
      /\ (f m = Some mN)
      /\ (f z = Some 0)
      /\ (forall dl dh l h, f dl = Some l -> f dh = Some h -> S l = h <-> isucc dl dh z)
      /\ (forall d1 d2, f d1 <> None -> f d1 = f d2 <-> d1 == d2).

      Definition vpTrans a b c : a << b -> b << c -> a << c.
      Proof using vTrans rho'.
      intros Ha Hb. specialize (@vTrans a b c). fold sat in vTrans. cbn in vTrans.
      rewrite ! to_less in vTrans. cbn in vTrans. now apply vTrans.
      Qed.

      Definition vpPred x : iN x -> ~(x == z) -> exists p, isucc p x z.
      Proof using vPred rho m Hrho.
      intros Nx Hxz. specialize (@vPred x). fold sat in vPred. cbn in vPred. destruct vPred as [d Hd].
      - now rewrite to_N.
      - rewrite to_deq. cbn. rewrite Hrho. cbn. intros H. apply Hxz. now rewrite H.
      - exists d. rewrite to_succ in Hd. cbn in Hd. rewrite Hrho in Hd. cbn in Hd. easy.
      Qed.

      Definition vpSucc l r : isucc l r z -> (l << r) /\ forall k, k << r -> k <<= l.
      Proof using vSucc rho' rho m Hrho.
      intros Hsucc. specialize (@vSucc l r). fold sat in vSucc. cbn in vSucc.
      rewrite ! to_N, to_rel, to_less in vSucc. cbn in vSucc.
      destruct vSucc as [Hl Hr]. 1-2:destruct Hsucc as [p [q [Hs1 [Hs2 Hs3]]]]; firstorder. 1:rewrite Hrho; exact Hsucc. split.
      * easy.
      * intros k Hk. specialize (@Hr k). rewrite to_less, to_leq in Hr. cbn in Hr. now apply Hr.
      Qed.

      Ltac firstorder' := clear vTrans vPred vSucc fini; firstorder.
      Ltac recsplit n := let rec f n := match n with 0 => idtac | S ?nn => split; [idtac|f nn] end in f n.

      Add Parametric Relation : D iless
        transitivity proved by vpTrans
      as less_rel.

      Lemma less_irref (x : D) : ~ (iless x x).
      Proof.
      intros [H1 H2]. apply H2. firstorder'.
      Qed.
      Lemma less_wf : well_founded iless.
      Proof using fini vTrans. 
      destruct fini as [l Hl]. apply wf_strict_order_list with l.
      - apply less_irref.
      - intros a b c Hab Hbc. eapply vpTrans. 1-2:intuition.
      - intros x y H. now apply Hl.
      Qed.

      Lemma less_leq a b c : a << b -> b <<= c -> a << c.
      Proof using vTrans rho' rho fini decP.
      intros H1 H2. destruct (eqDec b c) as [Heq|Hneq].
      - now rewrite ! Heq in *.
      - transitivity b. 1:easy. now split.
      Qed.

      Lemma leq_less a b c : a <<= b -> b << c -> a << c.
      Proof using vTrans rho' rho fini decP.
      intros H1 H2. destruct (eqDec a b) as [Heq|Hneq].
      - now rewrite ! Heq in *.
      - transitivity b. 2:easy. now split.
      Qed.


      Lemma leq_trans a b c : a <<= b -> b <<= c -> a <<= c.
      Proof  using vTrans rho' rho fini decP.
      destruct (eqDec a b) as [->|Hn1].
      - easy.
      - intros H1 H2. enough (a << c) as H by apply H.
        now eapply less_leq with b.
      Qed.

      Lemma aZeroS k : ~ (k << z).
      Proof using vTrans vSucc vPred rho' rho m fini decP Hrho.
      induction k as [k IH] using (well_founded_ind less_wf).
      intros [Hc1 Hc2]. destruct (@vpPred k) as [k' [Hk'1 Hk'2]%vpSucc]. 1-2:firstorder.
      eapply (IH k'). 1:easy. eapply less_leq. 1:exact Hk'1. easy.
      Qed.

      Lemma aZero2 k : iN k -> z <<= k.
      Proof using vTrans vSucc vPred vDescr2 rho' rho m fini decP Hrho.
      induction k as [k IH] using (well_founded_ind less_wf).
      intros Nk. destruct (eqDec z k) as [Heq|Hneq].
      - now apply leq_eq.
      - destruct (@vpPred k) as [k' [Hk'1 Hk'2]%vpSucc]. 1-2:firstorder'. eapply leq_less with k'. 2:easy.
        apply IH. 2:firstorder'. easy.
      Qed.

      Lemma antiSym (a b : D) : a <<= b -> b <<= a -> a == b.
      Proof using vTrans rho' rho fini decP.
      intros Ha Hb. destruct (eqDec a b) as [t|Hf]. 1:easy. 
      assert (a << a) as Hc.
      - eapply leq_less with b. 1:easy. split. 1:easy. intros H. apply Hf. now rewrite H.
      - exfalso. destruct Hc. firstorder'.
      Qed.

      Lemma eqDec_eq d1 d2 T (X Y : T) : d1 == d2 -> (if eqDec d1 d2 then X else Y) = X.
      Proof. intros H.
      destruct (eqDec d1 d2) as [Ht|Hf].
      - easy.
      - exfalso;easy.
      Qed.

      Lemma mkchain (d:D) : iN d -> exists n f, chain d n f.
      Proof using vTrans vSucc vPred rho rho' m fini decP Hrho.
      induction d as [dd IH] using (well_founded_ind less_wf).
      intros H. destruct (eqDec dd z) as [H0|HS].
      - exists 0, (fun k => if eqDec k dd then Some 0 else None).
        recsplit 5.
        + intros d. split. 
          * intros dl. destruct (eqDec d dd) as [Ht|Hf]. 1:easy.
            intros _. eapply aZeroS with d. split. 1: now rewrite <- H0. intros HH; apply Hf. transitivity z. 1:easy. now symmetry.
          * destruct (eqDec d dd) as [Hl|Hr]. 2: easy. intros _. apply leq_eq. all: easy.
        + intros n.
          intros [d [ddd Hdd]]. destruct (eqDec d dd). 1: assert (n=0) by congruence;lia. easy.
        + rewrite eqDec_eq; easy.
        + rewrite eqDec_eq. 1:easy. now symmetry.
        + intros dl dh l h H1 H2; split; intros H3; destruct (eqDec dl dd), (eqDec dh dd). 1-4: congruence.
          all: destruct (vpSucc H3) as [[H321 H322] H33]; exfalso; apply H322; transitivity dd; [easy|now symmetry].
        + intros d1 d2. intros H1. split; intros H2; destruct (eqDec d1 dd), (eqDec d2 dd) as [Ht|Hf]. 2-5,7-8:easy.
          -- intros. transitivity dd; [easy|now symmetry].
          -- exfalso. apply Hf. transitivity d1; [now symmetry|easy].
      - destruct (@vpPred dd) as [p Hp]. 1-2:firstorder'. destruct (vpSucc Hp) as [Hless Hclose].
        destruct (IH p) as [n [f Hnf]]. 1-2: firstorder'. 
        exists (S n). exists (fun v => if eqDec v dd then Some (S n) else f v). 
        destruct Hnf as [H1 [H2 [H3 [H4 [H5 H6]]]]].
        recsplit 5.
        + intros d. split.
          * intros Hdd. destruct (eqDec d dd) as [Heq|Neq].
            -- easy.
            -- apply H1, Hclose. now split.
          * destruct (eqDec d dd) as [Heq|Neq].
            -- intros; now apply leq_eq.
            -- intros HN. eapply leq_trans with p. 
              ++ rewrite <- H1 in HN. easy.
              ++ apply Hless.
        + intros n0. 
          intros [d [Hddd HSome]]. destruct (eqDec d dd). 1: assert (S n = n0) by congruence;lia.
          enough (n0 <= n) by lia. apply (H2 n0). exists d. split. 2:easy. apply Hclose. easy.
        + rewrite (eqDec_eq). 1:easy. firstorder'.
        + destruct (eqDec z dd) as [H0|Hn0]. 2: apply H4. exfalso. apply HS. now symmetry.
        + intros dl dh l h HH1 HH2; split; intros HH3; destruct (eqDec dl dd) as [Hl1|Hh1], (eqDec dh dd) as [Hl2|Hh2].
          * exfalso. assert (S l = l) by congruence. lia.
          * assert (h = S (S n)) as Hc by congruence. enough (h <= n) by lia. apply H2. exists dh. split. 2:easy. apply H1. intros Hh; congruence.
          * assert (l = n) as Hc by congruence. rewrite Hl2. enough (dl == p) as -> by easy.
            apply H6; congruence.
          * apply H5 with l h; easy.
          * destruct (vpSucc HH3) as [[H321 H322] H33]; exfalso; apply H322. now rewrite <- Hl2 in Hl1.
          * exfalso. apply less_irref with dd. eapply vpTrans with dh.
            -- rewrite <- Hl1. now destruct (vpSucc HH3).
            -- eapply leq_less with p. 2:easy. rewrite H1. congruence.
          * rewrite Hl2 in HH3.
            assert (dl == p) as Hdlp. 
            -- apply antiSym.
               ++ apply Hclose. destruct (vpSucc HH3) as [H32 H33]. apply H32.
               ++ destruct (vpSucc HH3) as [[H321 H322] H33]. apply H33. easy.
            -- assert (f p = f dl) as Heq.
               ++  apply H6. 1:congruence. now symmetry.
               ++ assert (n = l) by congruence. subst n. congruence.
          * erewrite H5. 1:exact HH3. all:easy.
        + intros d1 d2. intros HSome. split; intros Heq; destruct (eqDec d1 dd) as [Htt|Hff], (eqDec d2 dd) as [Ht|Hf].
          -- now rewrite Htt,Ht.
          -- exfalso. enough (S n <= n) by lia. apply H2. exists d2. split. 2:easy. apply H1. congruence.
          -- exfalso. enough (S n <= n) by lia. apply H2. exists d1. split. 2:easy. apply H1. congruence.
          -- now apply H6.
          -- easy.
          -- exfalso. apply Hf. rewrite <- Htt. now symmetry.
          -- exfalso. apply Hff. now rewrite Heq.
          -- apply H6; easy.
      Qed.


      Lemma chain_proves (a b c d: D) (nm : nat) (f:D->option nat): chain m nm f -> b <<= m -> irel a b c d 
                   -> a <<= m -> c <<= m -> d <<= m
                   -> exists a' b' c' d', h10upc_sem_direct ((a',b'),(c',d')) /\ 
                         f a = Some a' /\ f b = Some b' /\ f c = Some c' /\ f d = Some d'.
      Proof using vTrans vSucc vDescr2 vDescr rho' rho fini decP Hrho.
      intros Hf. pose Hf as HHf. destruct HHf as [Hf1 [Hf2 [Hf3 [Hf4 [Hf5 Hf6]]]]].
      induction b as [b IH] in a,c,d|-* using (well_founded_ind less_wf); intros Hb Habcd Ha Hc Hd.
      destruct (eqDec b z) as [Hbz|Hnbz].
      - destruct (f a) as [na|] eqn:Heqfa. 2: exfalso; apply (Hf1 a); easy.
        exists na, 0, (S na), 0. assert (d == z) as Hdd0. 2: recsplit 4. 2:easy.
        + specialize (@vDescr2 a b c d). fold sat in vDescr2. cbn in vDescr2.
          rewrite ! to_N, to_rel, ! to_deq, Hrho in vDescr2. cbn in vDescr2.
          apply vDescr2. 1-4:firstorder'. all:easy.
        + easy.
        + rewrite <- Hf4. apply Hf6. 1: now apply Hf1. easy.
        + assert (isucc a c z) as Hsucc.
          * unfold isucc. rewrite <- Hbz at 1. now rewrite <- Hdd0.
          * destruct (f c) as [Sna|] eqn:Hfc.
            -- f_equal. symmetry. erewrite (Hf5 a c); easy.
            -- exfalso. contradict Hfc. rewrite <- Hf1. easy.
        + symmetry. rewrite <- Hf4, Hf6. 2:congruence. now symmetry.
      - specialize (@vDescr a b c d). fold sat in vDescr. cbn in vDescr.
        setoid_rewrite Hrho in vDescr. cbn in vDescr.
        setoid_rewrite to_N in vDescr. cbn in vDescr.
        setoid_rewrite to_rel in vDescr. cbn in vDescr.
        setoid_rewrite to_deq in vDescr. cbn in vDescr.
        setoid_rewrite to_less in vDescr. cbn in vDescr.
        destruct vDescr as [b' [c' [d' [[[[Hb' Hc'] Hd'1] Hd'2] Hd'3]]]]. 1-4,6:firstorder'. 1: intros H; rewrite H in Hnbz; firstorder'.
        destruct (vpSucc Hb') as [Hb'1 Hb'2].
        destruct (vpSucc Hc') as [Hc'1 Hc'2].
        edestruct (IH b' (ltac:(firstorder')) d' d d') as [nd' [nb' [nd [nd'2 [HIH1 [Hnd' [Hnb2 [Hnd2 Hnd'2]]]]]]]].
        2:easy. 3:easy. 2: apply leq_trans with d; firstorder. 1: eapply leq_trans with b; firstorder. 1: eapply leq_trans with d; firstorder. 
        edestruct (IH b' (ltac:(firstorder')) a c' d') as [na [nb'3 [nc' [nd'3 [HIH2 [Hna [Hnb3 [Hnc' Hnd'3]]]]]]]].
        2-3:easy. 1: apply leq_trans with b; firstorder. 1: eapply leq_trans with c; firstorder. 1: eapply leq_trans with d; firstorder.
        exists na, (S nb'), (S nc'), (1+nb'+nd').
        recsplit 4.
        + cbn. cbn in HIH1, HIH2.
          assert (nd'2 = nd') as -> by congruence.
          assert (nd'3 = nd') as -> by congruence.
          assert (nb'3 = nb') as -> by congruence.
          split;nia.
        + easy.
        + destruct (f b) as [nb|] eqn:Hfb. 2: exfalso;now eapply Hf1 with b.
          f_equal. symmetry. erewrite Hf5. 1: exact Hb'. all:easy.
        + destruct (f c) as [nc|] eqn:Hfc. 2: exfalso;now eapply Hf1 with c.
          f_equal. symmetry. erewrite Hf5. 1: exact Hc'. all:easy.
        + assert (f d = Some nd) as -> by easy.
          f_equal. cbn in *; nia.
      Qed.

      Definition chain_env (f:D -> option nat) : D -> nat := fun k => match f k with Some l => l | None => 0 end.

      Lemma translate_single_correct (e:env D) (h10v : h10upc) zz n f : zz > highest_var h10v
      -> chain m n f -> (forall k, rho' k = e (k+zz))
      -> e ⊨ translate_single h10v zz
      -> h10upc_sem (fun k => chain_env f (e k)) h10v.
      Proof using vTrans vSucc vDescr2 vDescr rho fini decP Hrho.
      destruct h10v as [[a b][c d]].
      intros Hv ch Hrhok [[[[Hrel Ha] Hb] Hc] Hd]. rewrite ! to_leq in Ha,Hb,Hc,Hd.
      pose proof Hrhok 0 as Hrho0. cbn in Hrho0. rewrite <- Hrho0 in Ha,Hb,Hc,Hd.
      rewrite Hrho in Ha,Hb,Hc,Hd. cbn in Ha,Hb,Hc,Hd.
      rewrite to_rel in Hrel.
      destruct (chain_proves ch Hb Hrel) as [na [nb [nc [nd [Hsem [Hna [Hnb [Hnc Hnd]]]]]]]].
      1-3: easy.
      unfold h10upc_sem, chain_env. rewrite !Hna,!Hnb,!Hnc,!Hnd. cbn in Hsem. nia.
      Qed.

      Lemma translate_list_correct (e:env D) zz n f : zz > highest_var_list h10
      -> chain m n f -> (forall k, rho' k = e (k+zz))
      -> e ⊨ translate_list zz h10
      -> forall h10v, In h10v h10 -> h10upc_sem (fun k => chain_env f (e k)) h10v.
      Proof using vTrans vSucc vDescr2 vDescr rho fini decP Hrho.
      intros Hv ch Hrhok Hl h10v. induction h10 as [|h10x h10r IH] in Hl,Hrhok,ch,Hv|-*.
      - intros [].
      - destruct Hl as [Hl1 Hl2]. intros [Hin|Hr].
        + subst h10x. apply (@translate_single_correct e h10v zz n f). 2-4:easy. cbn in Hv. lia.
        + apply IH. 2-5:easy. cbn in Hv. lia.
      Qed.

    End withAxioms.

    Lemma remove_emplace_exists r frm n : r ⊨ emplace_exists n frm
    -> exists rr, rr ⊨ frm /\ forall k, r k = rr (k+n).
    Proof.
    unfold emplace_exists. intros H. induction n as [|n IH] in H,frm|-*.
    - exists r. split. 1:easy. intros k. now rewrite Nat.add_0_r.
    - rewrite it_shift in H. destruct (IH _ H) as [rr [[d Hd] Hrrr]].
      exists (d .: rr). split. 1:easy.
      intros k. rewrite Nat.add_succ_r. cbn. now apply Hrrr.
    Qed.

    Lemma F_correct : rho ⊨ F -> H10UPC_SAT h10.
    Proof using fini decP.
    intros [z [m [[[[[vpTrans vpPred] vpSucc] vpDescr] vpDescr2] [rho2 [Hlist Hrho]]%remove_emplace_exists]]].
    assert (H10UPC_SAT h10 \/ iN m) as [Hl|Nm].
    - destruct h10 as [|h10v h10r]. 1:left;exists (fun _ => 0); intros k [].
      right. destruct Hlist as [Hr _]. destruct h10v as [[ha hb][hc hd]]. cbn in Hr.
      rewrite ! to_leq in Hr. destruct Hr as [_ [_ [Hr _]]]. specialize (Hrho 0). cbn in Hrho. congruence.
    - easy.
    - destruct (@mkchain m z (m.:z.:rho) eq_refl vpTrans vpPred vpSucc m Nm) as [n [f c]].
      exists (fun k => chain_env f (rho2 k)).
      apply (@translate_list_correct m z (m.:z.:rho) eq_refl vpTrans vpSucc vpDescr vpDescr2 rho2 (S(highest_var_list h10)) n f ltac:(lia)). all:easy.
    Qed.
  End inverseTransport.

  Section transport.
  Context {rho:nat -> nat}.
  Context {H10sat : forall k, In k h10 -> h10upc_sem rho k}.
  Inductive finNum (m:nat) : Type := fN : forall n, n <= m -> finNum m.
  
  Lemma le0 {m} : 0 <= m. Proof. lia. Qed.
  Lemma leS {n m} : n <= m -> S n <= S m. Proof. lia. Qed.

  Lemma finNum_fin m : listable (finNum m).
  Proof.
  induction m as [|m [l IHl]].
  - exists ((fN le0)::nil). intros [n u]. assert (n=0) as -> by lia. left. f_equal. apply le_unique.
  - exists ((fN le0)::map (fun k => match k with @fN _ n u => fN (leS u) end) l).
    intros [[|n] u].
    + left. f_equal. apply le_unique.
    + right. rewrite in_map_iff. assert (n <= m) as Hu by lia. exists (fN Hu). split.
      * f_equal. apply le_unique.
      * apply IHl.
  Qed.

  Inductive model (m:nat) : Type := Num : finNum m -> model m | Pair : finNum m -> finNum m -> model m.
  
  Lemma model_fin m : listable (model m).
  Proof.
  destruct (finNum_fin m) as [l Hl].
  exists (map (@Num m) l ++ flat_map (fun v => map (Pair v) l) l).
  intros [n|a b].
  - apply in_or_app. left. apply in_map, Hl.
  - apply in_or_app. right. rewrite in_flat_map. exists a. split. 1:apply Hl.
    apply in_map, Hl.
  Qed.

  Definition model_rel (m:nat) (a b : model m) : Prop := match (a,b) with
  (Num (@fN _ n1 _), Num (@fN _ n2 _)) => n1 <= n2
| (Pair _ (@fN _ r _), Num (@fN _ n _)) => r = n
| (Num (@fN _ n _), Pair (@fN _ l _) _) => n = l
| (Pair (@fN _ a _) (@fN _ b _), Pair (@fN _ c _) (@fN _ d _)) => h10upc_sem_direct ((a,b),(c,d)) end.

  Instance model_interp m : interp (model m). 
  Proof. split.
  - intros [].
  - intros []. cbn. intros [l r]%proj_vec2.
    exact (@model_rel m l r).
  Defined.

  Lemma leq_dec a b : sum (a<=b) (a <= b -> False).
  Proof.
  induction a as [|a IH] in b|-*.
  - left. lia.
  - destruct b as [|b].
    + right. lia.
    + destruct (IH b) as [IHl|IHr]; [left|right]; lia.
  Defined.

  Definition into_fin m k := match leq_dec k m with inl u => fN u | _ => fN le0 end.

  Definition m := S (highest_num rho (highest_var_list h10)).
  Definition myenv k := Num (into_fin m (rho k)).

  Lemma myenv_desc i : i <= highest_var_list h10 -> exists (H:rho i <= m), myenv i = Num (fN H).
  Proof.
  intros H. unfold myenv, into_fin, m. pose proof (highest_num_descr rho H) as Hpr.
  assert (rho i <= S (highest_num rho (highest_var_list h10))) as HH2 by lia.
  exists HH2. destruct leq_dec as [Hl|Hr].
  - f_equal. f_equal. apply le_unique.
  - exfalso. now apply Hr, HH2.
  Qed.
  
  Notation "a # b" := (@model_rel m a b) (at level 50).


  Ltac solve_m := (unfold m;lia).

  Lemma m_N m (e : env (model m)) (a : nat) : e ⊨ N a <-> exists n1 u1, (e a) = Num (@fN _ n1 u1).
  Proof. split.
  - cbn -[model_rel]. destruct (e a) as [[n1 u1]|l r]. 
    + exists n1, u1. easy.
    + destruct l as [nl ul], r as [nr ur]. unfold model_rel. intros H. exfalso. apply (h10_rel_irref H).
  - intros [n1 [u1 Heq]]. cbn. rewrite Heq. lia.
  Qed.

  Lemma m_P' m (e : env (model m)) (a : nat) : e ⊨ P' a <-> exists nl ul nr ur, (e a) = Pair (@fN _ nl ul) (@fN _ nr ur).
  Proof. split.
  - cbn -[model_rel]. destruct (e a) as [[n1 u1]|[nl ul] [nr ur]]. 
    + intros H. exfalso. unfold model_rel in H. apply H. lia.
    + unfold model_rel. intros H. exists nl, ul, nr, ur. easy.
  - intros [nl [ul [nr [ur Heq]]]]. cbn. rewrite Heq. lia.
  Qed.

  Lemma m_P m (e : env (model m)) (p a b : nat) : e ⊨ P p a b <-> exists n1 u1 n2 u2, (e a) = Num (@fN _ n1 u1) /\ (e b) = Num (@fN _ n2 u2) /\ (e p) = Pair (@fN _ n1 u1) (@fN _ n2 u2).
  Proof. split.
  - intros [[[[[nl' [ul' [nr' [ur' H1]]]]%m_P' [nl [ul Hl]]%m_N] [nr [ur Hr]]%m_N] H4] H5]. exists nl, ul, nr, ur. split. 2:split. 1-2:easy.
    rewrite H1. cbn in H4, H5. rewrite H1, Hl in H4. rewrite H1, Hr in H5. subst nl'. subst nr'. f_equal; f_equal; apply le_unique.
  - intros [nl [ul [nr [ur [Hl [Hr Hp]]]]]]. cbn -[model_rel]. split. 1:split. 1:split. 1:split.
    + change (e ⊨ P' p). rewrite m_P'. eauto.
    + change (e ⊨ N a). rewrite m_N. eauto.
    + change (e ⊨ N b). rewrite m_N. eauto.
    + cbn. rewrite Hl, Hp. easy.
    + cbn. rewrite Hr, Hp. easy.
  Qed.

  Lemma differentNums (m:nat) (base:finNum m) : m > 0 -> exists (m1 m2 : finNum m), m1 <> m2 /\ (
    (model_rel (Num m1) (Num base) /\ model_rel (Num m2) (Num base))
  \/(model_rel (Num base) (Num m1) /\ model_rel (Num base) (Num m2))
  ).
  Proof.
  intros Hm0.
  destruct base as [[|n] Hn].
  * eexists (@fN m 0 _).
    eexists (@fN m 1 _).
    split.
    - intros H. congruence.
    - right. cbn. lia.
  * eexists (@fN m 0 _).
    eexists (@fN m 1 _).
    split.
    - intros H. congruence.
    - left. cbn. lia.
  Unshelve. all: lia.
  Qed.

  Lemma m_deq (m:nat) (e : env (model m)) (l r : nat) : m > 0 -> e ⊨ deq l r <-> e l = e r.
  Proof. intros Hm0.
  destruct (e l) as [[n1 Hn1]|[a Ha] [b Hb]] eqn:Hel, (e r) as [[n2 Hn2]|[c Hc] [d Hd]] eqn:Her; split.
  * unfold deq. intros H. specialize (H (Pair (fN Hn1) (fN Hn1))). cbn in H. rewrite Hel, Her in H. assert (n1 = n2) as -> by firstorder congruence. do 2 f_equal. apply le_unique.
  * cbn -[model_rel]. intros H d. unfold model_rel. rewrite Hel,Her. cbn. assert (n1 = n2) as -> by firstorder congruence. firstorder.
  * intros H. change H with (forall d : model m, ((d # e l <-> d # e r)) /\ (e l # d <-> e r # d)). destruct (differentNums (fN Hn1) Hm0) as [m1 [m2 [Hm12 [[Hm2a1 Hm2a2]|[Hm2b1 Hm2b2]]]]];
    pose proof (H (Num m1)) as [Hl1 Hl2]; pose proof (H (Num m2)) as [Hh1 Hh2]; destruct m1 as [nm1 Hm1], m2 as [nm2 Hm2]; cbn -[model_rel] in *; rewrite Hel in *; rewrite Her in *.
    - contradict Hm12. apply (proj1 Hl1) in Hm2a1. apply (proj1 Hh1) in Hm2a2. assert (nm1 = nm2) as -> by congruence. f_equal. apply le_unique.
    - contradict Hm12. apply (proj1 Hl2) in Hm2b1. apply (proj1 Hh2) in Hm2b2. assert (nm1 = nm2) as -> by congruence. f_equal. apply le_unique.
  * intros H. discriminate.
  * intros H. destruct (differentNums (fN Hn2) Hm0) as [m1 [m2 [Hm12 [[Hm2a1 Hm2a2]|[Hm2b1 Hm2b2]]]]];
    pose proof (H (Num m1)) as [Hl1 Hl2]; pose proof (H (Num m2)) as [Hh1 Hh2]; destruct m1 as [nm1 Hm1], m2 as [nm2 Hm2]; cbn -[model_rel] in *; rewrite Hel in *; rewrite Her in *.
    - contradict Hm12. apply (proj2 Hl1) in Hm2a1. apply (proj2 Hh1) in Hm2a2. assert (nm1 = nm2) as -> by congruence. f_equal. apply le_unique.
    - contradict Hm12. apply (proj2 Hl2) in Hm2b1. apply (proj2 Hh2) in Hm2b2. assert (nm1 = nm2) as -> by congruence. f_equal. apply le_unique.
  * intros H. discriminate.
  * intros H. pose proof (H (Num (fN Ha))) as HHa. pose proof (H (Num (fN Hb))) as HHb.
    cbn in H, HHa, HHb. cbn. f_equal. all: rewrite Hel in *; rewrite Her in *.
    - assert (a = c) as -> by firstorder congruence. f_equal. apply le_unique.
    - assert (d = b) as -> by firstorder congruence. f_equal. apply le_unique.
  * cbn -[model_rel]. rewrite !Hel,! Her. intros ->. firstorder.
  Qed.

  Lemma m_leq (m:nat)  (e : env (model m)) (l r : nat) : m > 0 -> e ⊨ leq l r <-> exists n1 u1 n2 u2, (e l) = Num (@fN _ n1 u1) /\ (e r) = Num (@fN _ n2 u2) /\ n1 <= n2.
  Proof. split.
  - intros [[[nl [ul Hl]]%m_N [nr [ur Hr]]%m_N]Hlr]. exists nl,ul,nr,ur. split. 2:split. 1-2:easy.
    cbn in Hlr. rewrite Hl, Hr in Hlr. easy.
  - intros [nl [ul [nr [ur [Hl [Hr Hlr]]]]]]. cbn -[model_rel]. rewrite Hl, Hr. cbn. repeat split; lia.
  Qed.

  Lemma m_less (m:nat)  (e : env (model m)) (l r : nat) : m > 0 -> e ⊨ less l r <-> exists n1 u1 n2 u2, (e l) = Num (@fN _ n1 u1) /\ (e r) = Num (@fN _ n2 u2) /\ n1 < n2.
  Proof. split.
  - intros [[nl [ul [nr [ur [Hl [Hr Hlr]]]]]]%m_leq Hneq]. 2:easy. exists nl,ul,nr,ur. split. 2:split. 1-2:easy. enough (nl <> nr) by lia. 
    intros Hc. cbn -[deq] in Hneq. apply Hneq. erewrite -> m_deq. 2:easy. rewrite Hl, Hr. f_equal. subst nl. f_equal. apply le_unique.
  - intros [nl [ul [nr [ur [Hl [Hr Hlr]]]]]]. cbn -[deq leq]. split.
    + apply m_leq. 1:easy. exists nl,ul,nr,ur. split. 1:easy. split. 1:easy. lia.
    + intros Hc. enough (nl = nr) by lia. rewrite m_deq in Hc. 2:easy. rewrite Hl,Hr in Hc. congruence.
  Qed.

  Lemma m_rel (m:nat) (e : env (model m)) (a b c d : nat) : m > 0 -> e ⊨ rel a b c d <-> exists na ua nb ub nc uc nd ud, 
   (e a) = Num (@fN _ na ua) /\ (e b) = Num (@fN _ nb ub) /\ (e c) = Num (@fN _ nc uc) /\ (e d) = Num (@fN _ nd ud) /\ h10upc_sem_direct ((na,nb),(nc,nd)).
  Proof. intros Hm0. split.
  - cbn -[model_rel P]. intros [pl [pr [[[na [ua [nb [ub [Ha [Hb Hpl]]]]]]%m_P [nc [uc [nd [ud [Hc [Hd Hpr]]]]]]%m_P] Hpp]]].
    exists na,ua,nb,ub,nc,uc,nd,ud. split. 2: split. 3:split. 4:split. 1-4:easy.
    cbn in Hpl,Hpr,Ha,Hb,Hc,Hd. rewrite Hpr,Hpl in Hpp. apply Hpp.
  - intros [na [ua [nb [ub [nc [uc [nd [ud [Ha [Hb [Hc [Hd Hrel]]]]]]]]]]]]. cbn -[model_rel P].
    exists (Pair (fN ua) (fN ub)), (Pair (fN uc) (fN ud)). split. 1:split. 3:easy.
    + rewrite m_P. exists na,ua,nb,ub. tauto.
    + rewrite m_P. exists nc,uc,nd,ud. tauto.
  Qed.
    
  Opaque N leq P' P deq less rel.

  Lemma prove_exists m (e:env (model m)) frm n ee : (fun k => if leq_dec (S k) n then ee k else e (k-n)) ⊨  frm -> e ⊨ emplace_exists n frm.
  Proof.
  unfold emplace_exists. induction n as [|n IH] in frm,e,ee|-*.
  - cbn. intros H. eapply sat_ext. 2:exact H. intros x. cbn. f_equal. lia.
  - cbn -[leq_dec]. intros H. exists (ee n). apply IH with ee.
    eapply sat_ext. 2:exact H. intros x. cbn -[leq_dec].
    destruct (leq_dec (S x) n) as [Hl|Hr], (leq_dec (S x) (S n)) as [Hl2|Hr2].
    + easy.
    + lia.
    + assert (x=n) as -> by lia. assert (n-n=0) as -> by lia. easy.
    + assert (S x > n) as Hxn by lia. assert (x-n = S (x-S n)) as -> by lia. easy.
  Qed.

  
  Lemma valid (e:env (model m)) : e ⊨ F.
  Proof using H10sat.
  exists (Num (fN le0)). exists (Num(into_fin m m)). split. 1:split. 1:split. 1:split. 1:split.
  - cbn. intros x y z. rewrite ! m_less; cbn. 2-4: solve_m. intros [n1 [u1 [n2 [u2 [Hx [Hy Hr]]]]]] [n2' [u2' [n3 [u3 [Hy' [Hz Hr2]]]]]]. exists n1,u1,n3,u3. split. 2:split. 1-2:easy. enough (n2 = n2') by lia. rewrite Hy in Hy'. congruence.
  - cbn. unfold succ. intros k. rewrite m_N, m_deq. 2:solve_m. cbn.
    intros [n1 [u1 ->]] Hn0. assert (n1 <> 0) as Hn0'.
    + intros Hc. apply Hn0. subst n1. f_equal. f_equal. apply le_unique.
    + destruct n1 as [|n1]. 1:lia. assert (n1 <= m) as Hn1 by lia. exists (Num (fN Hn1)). rewrite m_rel.
      2:solve_m. exists n1,Hn1,0,le0,(S n1),u1,0,le0. cbn. repeat split. lia.
  - cbn. intros l r. rewrite !m_N, m_rel, m_less. 2-3:solve_m. cbn.
    intros [nl [ul ->]] [nr [ur ->]] [na [ua [nb [ub [nc [uc [nd [ud [-> [Hnb [-> [-> H]]]]]]]]]]]]. split.
    + exists na,ua,nc,uc. repeat split. lia.
    + intros k. rewrite ! m_less, ! m_leq. 2-3:solve_m. cbn.
      intros [nk [uk [nc' [uc' [Hk1 [Hk2 Hk3]]]]]].
      exists nk,uk,na,ua. repeat split. 1:easy. assert (nc = nc') as -> by congruence.
      enough (nb = 0) by lia. congruence.
  - unfold aDescr. intros a b c d [na [ua Ha]]%m_N [nb [ub Hb]]%m_N [nc [uc Hc]]%m_N [nd [ud Hd]]%m_N.
    cbn in Ha,Hb,Hc,Hd. cbn. rewrite !m_deq. 2:solve_m. unfold succ. 
    cbn. intros Hnz. rewrite !m_rel. 2:solve_m. rewrite Ha,Hb,Hc,Hd. cbn.
    intros [na' [ua' [nb' [ub' [nc' [uc' [nd' [ud' [Ha' [Hb' [Hc' [Hd' H]]]]]]]]]]]].
    assert (na = na') as -> by congruence.
    assert (nb = nb') as -> by congruence.
    assert (nc = nc') as -> by congruence.
    assert (nd = nd') as -> by congruence.
    assert (nb' <> 0) as Hb0. 1: { intros Hcc. apply Hnz. rewrite Hb. f_equal. subst nb'. f_equal. apply le_unique. }
    destruct nb' as [|nb']. 1:lia.
    assert (nc' <> 0) as Hc0 by lia.
    destruct nc' as [|nc']. 1:lia.
    assert (nb' <= m) as Hnb' by lia.
    assert (nc' <= m) as Hnc' by lia.
    assert (nd'-nb'-1 <= m) as Hnd' by lia.
    exists (Num (fN Hnb')), (Num (fN Hnc')), (Num (fN Hnd')).
    rewrite !m_rel. 2-5:solve_m. cbn -[h10upc_sem_direct].
    split. 1:split. 1:split. 1:split.
    + exists nb',Hnb',0,le0,(S nb'),ub,0,le0. repeat split; lia.
    + exists nc',Hnc',0,le0,(S nc'),uc,0,le0. repeat split; lia.
    + exists (nd'-nb'-1),Hnd',nb',Hnb',nd',ud,(nd'-nb'-1),Hnd'. repeat split; lia.
    + exists na',ua,nb',Hnb',nc',Hnc',(nd'-nb'-1),Hnd'. repeat split; lia.
    + rewrite ! m_less. 2:solve_m. cbn. exists (nd' - nb' - 1), Hnd',nd',ud. split. 1:easy. split. 1:easy. lia.
  - unfold aDescr2. intros a b c d [na [ua Ha]]%m_N [nb [ub Hb]]%m_N [nc [uc Hc]]%m_N [nd [ud Hd]]%m_N.
    intros [na' [ua' [nb' [ub' [nc' [uc' [nd' [ud' [Ha' [Hb' [Hc' [Hd' H]]]]]]]]]]]]%m_rel.
    2:solve_m. cbn in *. rewrite ! m_deq. 2-3:solve_m. cbn. intros ->. rewrite Hd'. assert (nb' = 0) as -> by congruence.
    assert (nd' = 0) as Hnd' by lia. subst nd'. f_equal. f_equal. apply le_unique.
  - eapply prove_exists with myenv.
    pose (highest_var_list h10) as lh10. fold lh10.
    assert (highest_var_list h10 <= lh10) as Hvl by easy.
    induction h10 as [|h10v h10r IH] in H10sat,Hvl|-*.
    + cbn. tauto.
    + cbn -[leq_dec]. split.
      * destruct h10v as [[a b][c d]]. unfold translate_single.
        cbn in Hvl.
        destruct (@myenv_desc a) as [ua Ha]. 1:lia.
        destruct (@myenv_desc b) as [ub Hb]. 1:lia. 
        destruct (@myenv_desc c) as [uc Hc]. 1:lia.
        destruct (@myenv_desc d) as [ud Hd]. 1:lia.
        split. 1:split. 1:split. 1:split.
        -- rewrite m_rel. 2:solve_m. 
           exists (rho a). exists ua.
           exists (rho b). exists ub.
           exists (rho c). exists uc.
           exists (rho d). exists ud.
           repeat destruct leq_dec. 2-16:lia.
           split. 2:split. 3:split. 4:split. 1-4:easy.
           apply (@H10sat ((a,b),(c,d))). now left.
        -- rewrite m_leq. 2:solve_m. unfold into_fin. destruct (leq_dec m m) as [Hml|Hmnl]; repeat destruct leq_dec.
           1,3,5,7,6,4:lia. 2:lia.
           exists (rho a), ua, m, Hml. split. 1:easy. split. 1: assert (forall k,k-k=0) as -> by lia. 2:lia. cbn. easy. 
        -- rewrite m_leq. 2:solve_m. unfold into_fin. destruct (leq_dec m m) as [Hml|Hmnl]; repeat destruct leq_dec.
           1,3,5,7,6,4:lia. 2:lia.
           exists (rho b), ub, m, Hml. split. 1:easy. split. 1: assert (forall k,k-k=0) as -> by lia. 2:lia. cbn. easy. 
        -- rewrite m_leq. 2:solve_m. unfold into_fin. destruct (leq_dec m m) as [Hml|Hmnl]; repeat destruct leq_dec.
           1,3,5,7,6,4:lia. 2:lia.
           exists (rho c), uc, m, Hml. split. 1:easy. split. 1: assert (forall k,k-k=0) as -> by lia. 2:lia. cbn. easy. 
        -- rewrite m_leq. 2:solve_m. unfold into_fin. destruct (leq_dec m m) as [Hml|Hmnl]; repeat destruct leq_dec.
           1,3,5,7,6,4:lia. 2:lia.
           exists (rho d), ud, m, Hml. split. 1:easy. split. 1: assert (forall k,k-k=0) as -> by lia. 2:lia. cbn. easy. 
        
      * apply IH.
        -- intros k Hk. apply H10sat. now right.
        -- cbn in Hvl. lia.
  Qed.

  Lemma rel_decider m (a b : model m) : dec (model_rel a b).
  Proof.
  destruct a as [[an al]|la ra], b as [[bn bl]|lb rb].
  - cbn. unfold dec. destruct (leq_dec an bn); auto.
  - cbn. unfold dec. destruct lb; decide equality.
  - cbn. destruct la,ra; unfold dec. decide equality.
  - cbn. destruct la,ra,lb,rb. apply and_dec; unfold dec; decide equality.
  Qed.

  Lemma decider_of_annoying_type : t (model m) (ar_preds sPr) -> bool.
  Proof.
  intros [x y]%proj_vec2.
  destruct (rel_decider x y ) as [Hl|Hr].
  - exact true.
  - exact false.
  Defined.


  End transport.

End Fsat.


Section result.

  Definition FSAT (phi : form) :=
  exists D (I : interp D) rho, listable D /\ decidable (fun v => i_atom (P:=sPr) v) /\ rho ⊨ phi.

  

  Lemma reduction : H10UPC_SAT ⪯ FSAT.
  Proof.
  exists @F. intros Hl. split.
  - intros [rho H]. pose (@m Hl rho) as m. exists (model m). exists (model_interp m). exists (fun _ => Num (fN le0)). split. 2:split.
    + apply (model_fin m).
    + exists decider_of_annoying_type. unfold m. intros v. unfold decider_of_annoying_type. cbn. destruct (proj_vec2 ) as [l r]. destruct (rel_decider l r) as [Ht|Hf] eqn:Heq.
      * unfold reflects. tauto.
      * unfold reflects. split. 1:intros k;exfalso;apply Hf;easy. intros Hc. congruence.
    + apply (@valid Hl rho H).
  - intros [D [I [rho [lst [tdec H]]]]]. destruct lst as [l Hlst].  destruct tdec as [f Hf].
    apply (@F_correct Hl D I rho).
    + intros a b. cbn. destruct (f (Vector.cons D a 1 (Vector.cons D b 0 (Vector.nil D)))) as [|] eqn:Hdec.
      * left. now apply Hf.
      * right. intros Hc. apply Hf in Hc. congruence.
    + exists l. exact Hlst.
    + exact H.
  Qed.

  Lemma foo : undecidable FSAT.
  Proof.
  apply (undecidability_from_reducibility H10UPC_SAT_undec).
  exact reduction.
  Qed.

  Print Assumptions foo.

End result.


