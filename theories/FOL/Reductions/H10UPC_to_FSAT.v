(* * FOL Reductions *)
From Undecidability.DiophantineConstraints Require Import H10UPC H10UPC_undec.
From Undecidability.FOL Require Import Util.Syntax Util.Deduction Util.Tarski Util.Kripke Util.Syntax_facts.
From Undecidability.Shared Require Import Dec.
From Undecidability.Shared.Libs.PSL Require Import Numbers.
From Coq Require Import Arith Lia List.
From Equations Require Import Equations.
From Undecidability.Shared.Libs.DLW.Wf Require Import wf_finite.
From Undecidability.FOL Require Import FSAT.
From Undecidability.Synthetic Require Import Definitions.
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

Notation Pr t t' := (@atom _ sig_pred _ _ sPr (Vector.cons _ t _ (Vector.cons _ t' _ (Vector.nil _)))).


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

Section fsat.

Context {D:Type}.
Context {I:interp D}.
Context (P : D -> D -> Prop).
Context (ePr : forall x y, dec (P x y)).
Notation "a # b" := (P a b) (at level 50).
Context (Dfin : finite D).

Definition N a := a # a.
Definition leq a b := N a /\ N b /\ a # b.
Notation "a <<= b" := (leq a b) (at level 51).
Definition Pr' a := ~ N a.
Definition Pr p a b := Pr' a /\ N a /\ N b /\ a # p /\ p # b.
Definition deq a b := forall x, (a # x <-> b # x) /\ (x # a <-> x # b).
Notation "a == b" := (deq a b) (at level 52).
Definition less a b  := a <<= b /\ ~ (a == b).
Notation "a << b" := (less a b) (at level 51).
Definition rel a b c d  := (exists p q, Pr p a b /\ Pr q c d /\ p # q).
Context (d0 : D).
Definition isSucc l r := rel l d0 r d0 /\ l << r /\ forall k, ~(l << k /\ k << r).

Axiom aTrans : forall x y z, N x -> N y -> N z -> x#y -> y#z -> x#z.
Axiom aTotal : forall x y, N x -> N y -> x#y \/ y#x.
Axiom aOrder : forall x y, N x -> N y -> x#y -> y#x -> deq x y.
Axiom aZeroS : forall k, ~ (k << d0).
Axiom aPred : forall r, N r -> (~(d0 == r)) -> exists l, isSucc l r.
Axiom aDescr : forall a b c d, N a -> N b -> N c -> N d
               -> ~(d0 == b)
               -> rel a b c d
               -> exists b' c' d', isSucc b' b /\ isSucc c' c /\ rel d' b' d d' /\ rel a b' c' d' /\ d' <<= d.
Axiom aDescr2 : forall a b c d, N a -> N b -> N c -> N d -> rel a b c d -> b == d0 -> d == d0.
Axiom aSucc : forall l r, N l -> N r -> rel l d0 r d0 -> isSucc l r.


Definition chain (m:D) (mN:nat) (f:D->option nat) := 
   (forall d, d <<= m <-> f d <> None)
/\ (forall n, n <= mN <-> exists d, d <<= m /\ f d = Some n)
/\ (f m = Some mN)
/\ (f d0 = Some 0)
/\ (forall dl dh l h, f dl = Some l -> f dh = Some h -> S l = h <-> isSucc dl dh)
/\ (forall d1 d2, f d1 <> None -> f d1 = f d2 <-> d1 == d2).

Lemma fin_dec (Pr:D->Prop) : (forall k, dec (Pr k)) -> dec (forall k, Pr k).
Proof.
intros HPr. assert (forall (l:list D), dec (forall k0, In k0 l -> Pr k0)) as H.
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

Lemma eqDec a b : dec (a == b).
Proof. apply fin_dec. intros k. apply and_dec; apply and_dec; apply impl_dec; apply ePr. Qed.

Lemma deqRefl : reflexive D deq.
Proof. firstorder. Qed.
Lemma deqSymm : symmetric D deq.
Proof. firstorder. Qed.
Lemma deqTrans : transitive D deq.
Proof. firstorder. Qed.

Ltac recsplit n := let rec f n := match n with 0 => idtac | S ?nn => split; [idtac|f nn] end in f n.

Lemma leq_rewrite a b c d : a == b -> c == d -> a <<= c -> b <<= d.
Proof. firstorder. Qed.

Lemma less_rewrite a b c d : a == b -> c == d -> a << c -> b << d.
Proof. intros H1 H2 [Hl1 Hl2]. split.
- eapply leq_rewrite. 3: exact Hl1. all:easy.
- intros Hc. apply Hl2. eapply deqTrans, deqTrans, deqSymm, H2. 1:exact H1. exact Hc.
Qed.

Lemma N_rewrite (d dd : D) : N d -> d == dd -> N dd.
Proof. intros H1 H2. firstorder. Qed.

Lemma eqDec_eq d1 d2 T (X Y : T) : d1 == d2 -> (if eqDec d1 d2 then X else Y) = X.
Proof. intros H.
destruct (eqDec d1 d2) as [Ht|Hf].
- easy.
- exfalso;easy.
Qed.

Lemma eq_leq a b : deq a b -> (N a \/ N b) -> leq a b.
Proof. intros H H2. assert (N a) as Na.
- destruct H2 as [Hl|Hr]. 1:easy. firstorder.
- recsplit 2.
  + easy.
  + firstorder.
  + firstorder.
Qed.

Lemma leq_trans a b c : N a -> N b -> N c -> leq a b -> leq b c -> leq a c.
Proof.
intros Na Nb Nc H1 H2. recsplit 2. 1-2:firstorder. apply aTrans with b. 1-5:firstorder.
Qed.

Lemma predLess l r k : isSucc l r -> k << r -> k <<= l.
Proof.
intros [Hrel [Hless Hclose]] Hkr. recsplit 2. 1-2:firstorder.
destruct (ePr k l) as [Hl|Hr]. 1:easy. exfalso.
destruct (@aTotal k l) as [Hkl|Hlk]. 1-2:firstorder. 1:easy.
destruct (eqDec l k) as [Heq|Neq]. 1:firstorder. eapply Hclose with k. split.
- split. 2:easy. recsplit 2; firstorder.
- easy.
Qed. 

Lemma isSuccCongr l1 r1 l2 r2 : isSucc l1 r1 -> l1 == l2 -> r1 == r2 -> isSucc l2 r2.
Proof.
intros [HS1 [HS2 HS3]] Hl Hr. recsplit 2.
- firstorder.
- eapply less_rewrite. 3:exact HS2. all:firstorder.
- intros k [H1 H2]. apply HS3 with k. split; eapply less_rewrite. 3:apply H1. 5:apply H2. all:firstorder.
Qed.

Lemma less_irref (x : D) : ~ (x << x).
Proof.
intros [H1 H2]. apply H2. firstorder.
Qed.

Lemma less_trans (x y z : D) : x << y -> y << z -> x << z.
Proof.
intros [Hxy Nxy] [Hyz Nyz]. split.
- recsplit 2. 1-2:firstorder. eapply aTrans with y. 1-3:firstorder. 1-2:firstorder.
- intros H. apply Nxy. apply aOrder. 1-2:firstorder. 1:firstorder. eapply (@leq_rewrite y y z x) in Hyz. 1:firstorder. 1:easy. now apply deqSymm.
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

Lemma less_leq_total (a b : D) : N a -> N b -> a << b \/ a == b \/ b << a.
Proof.
intros Na Nb. destruct (eqDec a b) as [Heq|Hneq]. 1:auto.
destruct (@aTotal a b Na Nb) as [Lab|Lba].
- left. split. 2:easy. recsplit 2; easy.
- do 2 right. split. 1: recsplit 2.
  + easy.
  + easy.
  + easy.
  + intros H. apply Hneq. apply deqSymm, H.
Qed.

Lemma mkchain (d:D) : N d -> exists n f, chain d n f.
Proof. induction d as [dd IH] using (well_founded_ind less_wf).
intros H. destruct (eqDec dd d0) as [H0|HS].
- exists 0, (fun k => if eqDec k dd then Some 0 else None).
  recsplit 5.
  + intros d. split. 
    * intros dl. destruct (eqDec d dd). 1:easy.
      intros _. eapply aZeroS with d. split. 1: now eapply leq_rewrite with d dd. intros HH; apply n. now eapply deqTrans with d0, deqSymm.
    * destruct (eqDec d dd) as [Hl|Hr]. 2: easy. intros _. apply eq_leq. 1:easy. left. eapply N_rewrite with dd. 1:easy. now apply deqSymm.
  + intros n. split.
    * intros Hn0. assert (n=0) as -> by lia. exists dd. split.
      --apply eq_leq. 1:easy. left. firstorder.
      -- rewrite eqDec_eq; easy.
    * intros [d [ddd Hdd]]. destruct (eqDec d dd). 1: assert (n=0) by congruence;lia. easy.
  + rewrite eqDec_eq; easy.
  + rewrite eqDec_eq. 1:easy. now apply deqSymm.
  + intros dl dh l h H1 H2; split; intros H3; destruct (eqDec dl dd), (eqDec dh dd). 1-4: congruence.
    all: destruct H3 as [H31 [[H321 H322] H33]]; exfalso; apply H322; eapply deqTrans with dd, deqSymm; easy.
  + intros d1 d2. intros H1. split; intros H2; destruct (eqDec d1 dd), (eqDec d2 dd) as [Ht|Hf]. 2-5,7-8:easy.
    -- intros. now eapply deqTrans with dd, deqSymm.
    -- exfalso. apply Hf, deqSymm, deqTrans with d1. 1:now apply deqSymm. easy.
- destruct (@aPred dd) as [p Hp]. 1-2:firstorder. pose proof Hp as Hpred. destruct Hp as [Hrel [Hless Hclose]].
  destruct (IH p) as [n [f Hnf]]. 1:firstorder. 1: { firstorder. } 
  exists (S n). exists (fun v => if eqDec v dd then Some (S n) else f v). 
  destruct Hnf as [H1 [H2 [H3 [H4 [H5 H6]]]]].
  recsplit 5.
  + intros d. split.
    * intros Hdd. destruct (eqDec d dd) as [Heq|Neq].
      -- easy.
      -- apply H1. eapply predLess. 1:exact Hpred. easy.
    * destruct (eqDec d dd) as [Heq|Neq].
      -- intros; apply eq_leq. 1:easy. firstorder.
      -- intros HN. eapply leq_trans with p. all:firstorder.
  + intros n0. split. 
    * intros Hn0. destruct (Dec (n0=S n)) as [Heq|Neq].
      -- exists dd. split. 1:apply eq_leq;firstorder. rewrite eqDec_eq. 1:congruence. eapply deqRefl.
      -- destruct (H2 n0) as [H21 H22]. destruct H21 as [d [Hdl Hdr]]. 1:lia. exists d. split.
        ++ apply leq_trans with p; firstorder.
        ++ destruct (eqDec d dd) as [Heq1|Neq1]. 2:easy. exfalso. destruct Hless as [Hleq Hneq]. apply Hneq, aOrder.
        1-4:firstorder.
    * intros [d [Hddd HSome]]. destruct (eqDec d dd). 1: assert (S n = n0) by congruence;lia.
      enough (n0 <= n) by lia. apply (H2 n0). exists d. split. 2:easy. apply predLess with dd. 1:easy. easy.
  + rewrite (eqDec_eq). 1:easy. firstorder.
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
    * destruct (@less_leq_total dl p) as [Hlt|[Heq|Hgt]]. 1-2:firstorder.
      -- exfalso. destruct HH3 as [HH31 [HH32 HH33]]. apply (HH33 p); split. 1:easy.
         eapply less_rewrite. 1:easy. 1: apply deqSymm, Hl2. easy.
      -- assert (f dl = f p). 2:congruence.
         rewrite H6. 1:easy. congruence.
      -- exfalso. apply (Hclose dl); split. 1:easy. destruct HH3 as [HH31 [HH32 HH33]]. eapply less_rewrite. 3:exact HH32. all:firstorder.
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

Lemma rel_rewrite (a b c d a' b' c' d' : D) : rel a b c d -> (a == a') -> (b == b') -> (c == c') -> (d == d') -> rel a' b' c' d'.
Proof.
intros Ha Hb Hc Hd Habcd. firstorder. Qed.

Lemma works (a b c d m: D) (nm : nat) (f:D->option nat): chain m nm f -> b <<= m -> rel a b c d 
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
  + rewrite <- Hf4. apply Hf6. 1:firstorder. easy.
  + assert (isSucc a c) as Hsucc.
    * apply aSucc. 1-2:firstorder. eapply (rel_rewrite Habcd). 1-3:easy. eapply aDescr2. 5:exact Habcd. 1-4:firstorder. easy.   
    * destruct (f c) as [Sna|] eqn:Hfc.
      -- f_equal. symmetry. erewrite (Hf5 a c); easy.
      -- exfalso. contradict Hfc. rewrite <- Hf1. easy.
  + assert (d == d0) as Hdd0. 1: eapply aDescr2. 5: exact Habcd. all:firstorder.
- destruct (@aDescr a b c d) as [b' [c' [d' [[Hb'1 [Hb'2 Hb'3]] [[Hc'1 [Hc'2 Hc'3]] [Hr1 [Hr2 Hdd']]]]]]]. 1-6:firstorder.
  specialize (IH b' (ltac:(firstorder)) ). pose proof ((proj1 (leq_less2 Hb'2 Hb))) as Hbb.
  edestruct (IH _ _ _ Hbb Hr1) as [nd' [nb' [nd [nd'2 Hdbdd]]]]. 4:
  edestruct (IH _ _ _ Hbb Hr2) as [na [nb'2 [nc' [nd'3 Habcd2]]]].
  2,4:easy. 3: apply leq_less2 with c; easy. 1-3: apply leq_trans with d;firstorder.
  exists na, (S nb'), (S nc'), (1+nb'+nd'). recsplit 4.
  + destruct (Hdbdd) as [Hdbdd1 Hdbdd2], Habcd2 as [Habcd21 Habcd22]. cbn in Habcd21, Hdbdd1. 
    assert (nd'2 = nd') as -> by firstorder congruence.
    assert (nd'3 = nd') as -> by firstorder congruence.
    assert (nb'2 = nb') as -> by firstorder congruence.
    cbn; split; lia.
  + firstorder.
  + destruct (f b) as [nb|] eqn:Hfb. 2: now apply Hf1 in Hfb.
    f_equal. symmetry. rewrite (Hf5 b' b). 3:easy. 2:firstorder. firstorder.
  + destruct (f c) as [nc|] eqn:Hfc. 2: now apply Hf1 in Hfc.
    f_equal. symmetry. rewrite (Hf5 c' c). 3:easy. 2:firstorder. firstorder.
  + firstorder.
Qed.

Section model.

Inductive ule : nat -> nat -> Type := 
  le0 : forall n, ule 0 n
| leS : forall n m, ule n m -> ule (S n) (S m).

Lemma ule_correct (a b : nat) : ule a b -> a <= b.
Proof.
intros H. induction H; lia.
Qed.

Lemma ule_correct_2 (a b : nat) : a <= b -> ule a b.
Proof.
intros H. induction a as [|a IH] in b,H|-*.
- apply le0.
- destruct b as [|b]. 1:lia. apply leS, IH. lia.
Qed.

Lemma ule_inversion (x y : nat) (c : ule x y) : match x as x' return (ule x' y -> Type) with 
  0 => (fun k : ule 0 y => k = le0 y) | 
  S xx => match y as y' return (ule (S xx) y' -> Type) with
    0 => fun _ => False
  | S yy => (fun k : ule (S xx) (S yy) => {k' : ule xx yy | k = @leS xx yy k'}) end end c.
Proof.
destruct c as [|xx yy cc].
- easy.
- exists cc. easy.
Qed.

Lemma ule_unique (x y : nat) (c1 c2 : ule x y) : c1 = c2.
Proof.
induction c1 as [yy|xx yy cc IHcc] in c2|-*.
- now rewrite (@ule_inversion 0 yy c2).
- destruct (@ule_inversion (S xx) (S yy) c2) as [c2' ->]. now rewrite (IHcc c2').
Qed.

Inductive model (m:nat) : Type := 
  Number : forall n, ule n m -> model m
|   Pair : forall l r, ule l m -> ule r m -> model m.

