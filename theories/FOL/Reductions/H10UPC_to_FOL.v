(* * FOL Reductions *)

From Undecidability.DiophantineConstraints Require Import H10UPC H10UPC_undec.
From Undecidability.FOL Require Import Util.Syntax Util.Deduction Util.Tarski Util.Syntax_facts.
From Coq Require Import Arith Lia List.


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


Set Default Proof Using "Type".
Set Default Goal Selector "!".

Inductive syms_func : Type := .

#[local] Instance sig_func : funcs_signature :=
  {| syms := syms_func; ar_syms := fun f => match f with end|}.

Inductive syms_pred := sPr.

#[local] Instance sig_pred : preds_signature :=
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
End Utils.

Section validity.

  Context {ff : falsity_flag}. 
  Context {h10 : list h10upc}.
  (* All are placed in a context where $0 is the 0 constant and $1, $2 are arbitrary but fixed *)
  (** We do a Friedman translation, where this represents falsity *)
  Definition wFalse t:= Pr $t $(S t).
  (** We use a stronger version of falsity, which is <-> False in our standart model, to ease writing eliminators *)
  Definition sFalse := ∀ ∀ Pr $0 $1.
  (** Friedman not *)
  Definition Not k t := k --> wFalse t.
  (** $k is a number *)
  Definition N k := Pr $k $k.
  (** $k is a pair *)
  Definition P' k (_:nat):= (N k) --> sFalse.
  (** If $k is a pair ($l,$r), where $l, $r are numbers, then c. *)
  Definition P k l r t c := P' k t --> N l --> N r --> Pr $l $k --> Pr $k $r --> c.
  (** if the pairs $pl = ($a,$b), $pr = ($c,$d) are in relation, then t *)
  Definition rel pl pr a b c d tt t := P pl a b tt (P pr c d tt (Pr $pl $pr --> t)).
  (** There exist (Friedman translated) pairs relating ($a,$b) to ($c,$d) *)
  Definition erel a b c d t := Not (∀ ∀ P 0 (2+a) (2+b) (2+t) 
                                        (P 1 (2+c) (2+d) (2+t) 
                                         (Pr $0 $1 --> wFalse (2+t)))) t.
  (** Axiom 1 - zero is a number *)
  Definition F_zero := N 0.
  (** Axiom 2 - we can build (left) successors: for each pair (a,0) we have a pair (S a, 0) *)
  Definition F_succ_left := ∀ N 0 --> Not (∀ ∀ ∀ P 2 3 4 5
                                                 (P 0 1 4 5
                                                  (Pr $2 $0 --> wFalse 5))) 2.
  (** Axiom 3 - we can build right successors: (x,y)#(a,b) -> (x,S y)#(S a,S (b+y)) *)
  Definition F_succ_right := ∀ ∀ ∀ ∀ ∀ ∀ ∀ ∀         (*8 pairs *)
                             ∀ ∀ ∀ ∀ ∀ ∀ ∀           (* 0 x 1 y 2 a 3 b 4 c 5 y' 6 a' 15 zero-const*)
                             rel 7 8 0 1 2 3 16      (* (x,y) # (a,b) *)
                            (rel 9 10 3 1 4 3 16     (* (b,y) # (c,b) *)
                            (rel 11 12 1 15 5 15 16  (* (y,0) # (y',0) *)
                            (rel 13 14 2 15 6 15 16  (* (a,0) # (a'0) *)
                            (erel 0 5 6 4 16))))     (* (x,y') # (a',c) *).
  (** Generate n all quantifiers around i *)
  Fixpoint emplace_forall (n:nat) (i:form) :=
          match n with 0 => i
        | S n => ∀ (emplace_forall n i) end.
  (** Translate our formula, one relation at a time *) 
  Definition translate_single (h:h10upc) nv := 
          match h with ((a,b),(c,d)) => 
            erel a b c d nv end.
  (** Translate an entire instance of H10UPC, assuming a proper context *)
  Fixpoint translate_rec (t:form) (nv:nat) (l:list h10upc) := 
          match l with nil => t
                     | l::lr => translate_single l nv --> translate_rec t nv lr end.
  (** Actually translate the instance of H10UPC, by creating a proper context *)
  Definition translate_constraints (x:list h10upc) := 
    let nv := S (highest_var_list x)
    in (emplace_forall nv (translate_rec (Pr $(S nv) $(2+nv)) (S nv) x)) --> Pr $1 $2.

  (** The actual reduction instance. If h10 is a yes-instance of H10UPC, this formula is valid and vice-versa
      The 3 variables are the zero constant and two arbitrary values which define the atomic predicate for 
      Friedman translation. *)
  Definition F := ∀ ∀ ∀ F_zero --> F_succ_left --> F_succ_right --> translate_constraints h10.

  Section Transport.
    (** The solution to cs *)
    Context (φ: nat -> nat). 
    (** Proof that it actually is a solution *)
    Context (Hφ : forall c, In c h10 -> h10upc_sem φ c). 
    Class model := {
      D : Type;
      I : interp D;
      rho : env D;
      zero : D; cr1 : D; cr2 : D;
      vF_zero : (zero .: cr2 .: cr1 .: rho) ⊨ F_zero;
      vF_succ_left : (zero .: cr2 .: cr1 .: rho) ⊨ F_succ_left;
      vF_succ_right : (zero .: cr2 .: cr1 .: rho) ⊨ F_succ_right;
    }.
    Context (valid_in : model).
    Instance II : interp D. exact I. Defined.
    Notation i_Pr i i' :=
      (@i_atom _ _ _ I sPr (Vector.cons _ i _ (Vector.cons _ i' _ (Vector.nil _)))).
    
    Definition isNum (d:D) := i_Pr d d.
    Definition D_wFalse := i_Pr cr2 cr1.
    Definition D_Not k := k -> D_wFalse.
    Definition isPair' d := (isNum d) -> forall a b, i_Pr b a.
    Definition isPair (p l r:D) := isNum l /\ isNum r /\ isPair' p /\ i_Pr l p /\ i_Pr p r.
    
    Definition repr_nums f n := f 0 = zero /\ forall m:nat, m < n -> 
              (exists (pl pr:D), isNum (f (S m)) /\ isPair pl (f m) zero /\ isPair pr (f (S m)) zero /\ i_Pr pl pr).

    Definition constr_nums (n:nat) : D_Not (forall f:nat -> D, repr_nums f n -> D_wFalse).
    Proof.
    induction n as [|n IH]; intros H.
    - apply (H (fun _ => zero)). split. 1: easy. intros m HH. exfalso. lia.
    - apply IH. intros f [IH0 IHfs].
      apply (@vF_succ_left valid_in (f n)); fold sat.
      + change (isNum (f n)). destruct n as [|n].
        * rewrite IH0. apply vF_zero.
        * destruct (IHfs n) as [pl [pr [HH _]]]. 1:lia. easy.
      + cbn. intros pl sn pr Ppl Nfn Nz Pfnl Plz Ppr Nsn Nz' Psnr Prz Pplpr.
        pose (fun m => if m =? S n then sn else f m) as f'.
        apply (H f'). split.
        * easy.
        * intros m Hm. destruct (Nat.eq_dec n m) as [Heq|Hneq].
          -- exists pl, pr. rewrite <- Heq.
             assert (f' (S n) = sn) as ->. 1: unfold f'; assert (S n =? S n = true) as ->. 
             1:apply Nat.eqb_eq; lia. 1:easy.
             assert (f' n = f n) as  ->. 1:unfold f'; assert (n =? S n = false) as ->. 
             1:apply Nat.eqb_neq; lia. 1:easy.
             now repeat split.
          -- destruct (IHfs m) as [pl' [pr' Hplplr']]. 1:lia.
             exists pl', pr'.
             assert (f' (S m) = f (S m)) as ->. 1: unfold f'; assert (S m =? S n = false) as ->.
             1:apply Nat.eqb_neq; lia. 1:easy.
             assert (f' m = f m) as  ->. 1:unfold f'; assert (m =? S n = false) as ->.
             1:apply Nat.eqb_neq; lia. 1:easy.
             easy. 
    Qed. 

    Lemma repr_num_isNum (f:nat -> D) (n:nat) (m:nat) : repr_nums f n -> m <= n -> isNum (f m).
    Proof.
    intros [Hzero Hrepr] Hnm.
    destruct m as [|m].
    - rewrite Hzero. apply vF_zero.
    - destruct (Hrepr m Hnm) as [pl [pr [H _]]]. apply H.
    Qed.

    Lemma constr_rel (a b c d : nat) (f:nat -> D) (n:nat) : 
        repr_nums f n 
     -> b <= n -> a <= n -> c <= n -> d <= n
     -> h10upc_sem_direct ((a,b),(c,d)) 
     -> D_Not (forall pl pr, isPair pl (f a) (f b) 
                         -> isPair pr (f c) (f d) 
                         -> i_Pr pl pr -> D_wFalse).
    Proof.
    intros Hreprnums Hbn.
    pose proof Hreprnums as Hrepr_nums.
    destruct Hreprnums as [Zrepr Hrepr].
    induction b as [|b IH] in a,c,d|-*; intros Han Hcn Hdn Habcd.
    - cbn in Habcd. assert (c = S a /\ d = 0) as [Hc Hd]. 1:lia.
      rewrite Hc, Hd, !Zrepr in *.
      destruct (Hrepr a) as [pl [pr [Ha [Hpl Hpr]]]]. 1:lia. 
      intros Hcr. now apply (Hcr pl pr).
    - destruct (@h10upc_inv a b c d Habcd) as [c' [d' [Habcd' [Hc' Hd']]]].
      rewrite <- Hc', <- Hd' in *. 
      assert (h10upc_sem_direct ((d',b),(d'+b+1,d'))) as Hdb.
      + split. 1: now lia. apply Habcd'.
      + intros Hcr.
        apply (IH a c' d'). 1-3: lia. 1: easy. 
        intros pab pc'd' Hpab Hpc'd' Hpabc'd'.
        apply (IH d' (d'+b+1) d'). 1-3: lia. 1: easy. 
        intros pd'b pd'bd' Hpd'b Hpd'bd' Hpd'bd'bd'.
        destruct (Hrepr b) as [pb [pb' [Nsb [Hpb [Hpb' Hpbpb']]]]]. 1:lia.
        destruct (Hrepr c') as [pc [pc' [Nsc [Hpc [Hpc' Hpcpc']]]]]. 1:lia.
        pose proof (@vF_succ_right valid_in pc' pc pb' pb pd'bd' pd'b pc'd' pab
                    (f (S c')) (f (S b)) (f(d' + b + 1)) (f d') (f c') (f b) (f a)) as sr.
        apply sr; cbn; fold isNum.
        1-5: now destruct Hpab as [H'l [H'r [H'p [H'pl H'pr]]]].
        1-5: now destruct Hpc'd' as [H'l [H'r [H'p [H'pl H'pr]]]].
        1: easy.
        1-5: now destruct Hpd'b as [H'l [H'r [H'p [H'pl H'pr]]]].
        1-5: now destruct Hpd'bd' as [H'l [H'r [H'p [H'pl H'pr]]]].
        1: easy.
        1-5: now destruct Hpb as [H'l [H'r [H'p [H'pl H'pr]]]].
        1-5: now destruct Hpb' as [H'l [H'r [H'p [H'pl H'pr]]]].
        1: easy.
        1-5: now destruct Hpc as [H'l [H'r [H'p [H'pl H'pr]]]].
        1-5: now destruct Hpc' as [H'l [H'r [H'p [H'pl H'pr]]]].
        1: easy.
        intros pScsum paSb HpaSb H'a H'Sb HlpaSb HrpaSb HpScsum H'Sc H'dsum HlpScsum HrpScsum Hprel.
        apply (Hcr paSb pScsum). all: now repeat split.
    Qed.
    
    Lemma prove_emplace_forall (n:nat) (i:form) (r:env D) :
    r ⊨ emplace_forall n i
    -> forall f, (fun v => if v <? n then f v else r (v-n)) ⊨ i.
    Proof.
    induction n as [|n IH] in r|-*.
    - cbn. intros H f. apply (sat_ext I (rho := r) (xi:=fun v => r(v-0)) i).
      + intros x. now rewrite Nat.sub_0_r.
      + easy.
    - intros H f. cbn. cbn in H. specialize (H (f n)). specialize (IH (f n .: r) H f). 
      eapply (Tarski.sat_ext I (xi := (fun v : nat => if v <? n then f v else (f n .: r) (v - n))) i).
      + intros x. destruct (Nat.eq_dec x n) as [Hxn|Hnxn].
        * destruct (Nat.leb_le x n) as [_ Hr]. specialize (Hr ltac:(lia)). rewrite Hr. 
          destruct (Nat.ltb_ge x n) as [_ Hr2]. specialize (Hr2 ltac:(lia)). rewrite Hr2.
          assert (x-n=0) as Hxn0. 1:lia. rewrite Hxn0. cbn. now f_equal.
        * destruct (x <? n) as [|] eqn:Hxn.
          -- apply (Nat.ltb_lt) in Hxn. assert (x <=? n = true) as Hxn2. 1: apply Nat.leb_le; lia.
             rewrite Hxn2. easy.
          -- apply (Nat.ltb_ge) in Hxn. assert (x <=? n = Datatypes.false) as Hxn2. 1: apply Nat.leb_gt; lia.
             rewrite Hxn2. assert (x-n = S(x-S n))  as Hxn3. 1:lia. rewrite Hxn3. cbn. easy.
      + easy.
    Qed.

    Lemma prove_constraints : (zero .: cr2 .: cr1 .: rho) ⊨ translate_constraints h10.
    Proof using φ Hφ.
    pose (S (highest_var_list h10)) as h10vars.
    unfold translate_constraints. fold h10vars.
    pose (highest_num φ h10vars) as h10max.
    pose (@constr_nums h10max) as Hcons.
    intros HH. cbn.
    pose proof (prove_emplace_forall HH) as H. clear HH.
    apply Hcons. intros f Hrepr. specialize (H (fun t => f (φ t))).
    pose ((fun v : nat => if v <? h10vars then (fun t : nat => f (φ t)) v else (zero .: cr2 .: cr1 .: rho) (v - h10vars))) as newenv.
    assert (newenv (S h10vars) = cr2) as Hne1.
    1: {unfold newenv. assert (S h10vars <? h10vars = false) as ->. 1: apply Nat.leb_gt; now lia.
        assert (S h10vars - h10vars = 1) as ->. 1:now lia. easy. }
    assert (newenv (S (S h10vars)) = cr1) as Hne2.
    1: {unfold newenv. assert (S (S h10vars) <? h10vars = false) as ->. 1: apply Nat.leb_gt;lia.
        assert (S (S h10vars) - h10vars = 2) as ->. 1:now lia. easy. }
    fold newenv in H.
    assert (forall c:h10upc, In c h10 -> newenv ⊨ translate_single c (S h10vars)) as Hmain.
    - intros [[a b][c d]] Hin. 
      pose (@highest_var_list_descr h10 ((a,b),(c,d)) Hin) as Habcdmax.
      cbn in Habcdmax. intros HH. 
      cbn. rewrite Hne1, Hne2.
      apply (@constr_rel (φ a) (φ b) (φ c) (φ d) f h10max). 1:easy.
      1-4: eapply highest_num_descr; lia.
      1: apply (@Hφ ((a,b),(c,d)) Hin).
      intros pab pcd [Ha [Hb [Hab [Haab Hbab]]]] [Hc [Hd [Hcd [Hccd Hdcd]]]] Hpp. 
      assert (forall k:nat, k < h10vars -> newenv k = f (φ k)) as Hvars.
      1:{ unfold newenv, h10vars. intros k Hk. destruct (Nat.ltb_lt k h10vars) as [_ Hr]. 
          fold h10vars. now rewrite Hr. }
      cbn in HH. rewrite Hne1, Hne2, (Hvars a), (Hvars b), (Hvars c), (Hvars d) in HH.
      2-5: unfold h10vars;lia.
      now apply (@HH pcd pab).
    - induction h10 as [|hx hr IH] in H,Hmain|-*.
      + cbn in H. rewrite Hne1,Hne2 in H. apply H.
      + apply IH. 
        * cbn in H. apply H. apply Hmain. now left.
        * intros c Hhr. apply Hmain. now right. 
    Qed.
  End Transport.

  Lemma transport : H10UPC_SAT h10 -> valid F.
  Proof.
    intros [φ Hφ].
    intros D I rho.
    intros cr1 cr2 zero.
    intros H_zero H_succ_left H_succ_right.
    eapply (@prove_constraints φ Hφ (Build_model H_zero H_succ_left H_succ_right)).
  Qed. 

  Section InverseTransport.

    Inductive dom : Type := Num : nat -> dom | Pair : nat  -> nat -> dom.
    Definition dom_rel (a : dom) (b:dom) : Prop := match (a,b) with
    | (Num n1, Num n2) => if Nat.eqb n1 0 then if Nat.eqb n2 (S 0) then H10UPC_SAT h10 else n1 = n2 else n1 = n2
    | (Num n1, Pair x2 y2) => n1 = x2
    | (Pair x1 y1, Num n2) => n2 = y1
    | (Pair x1 y1, Pair x2 y2) => h10upc_sem_direct ((x1, y1), (x2, y2))
    end.

    Global Instance IB : interp (dom).
    Proof using h10.
      split; intros [] v.
      exact (dom_rel (Vector.hd v) (Vector.hd (Vector.tl v))).
    Defined.

    Lemma IB_sFalse rho : rho ⊨ (∀ ∀ Pr $0 $1) <-> False.
    Proof.
    split.
    * intros H. specialize (H (Num 0) (Num 1)). cbn in H. congruence.
    * intros [].
    Qed.
    Opaque sFalse.

    Lemma IB_sNot rho f : rho ⊨ (f --> sFalse) <-> ~ (rho ⊨ f).
    Proof.
    split.
    * intros H. cbn in H. now rewrite IB_sFalse in H.
    * intros H. cbn. now rewrite IB_sFalse.
    Qed.

    Lemma IB_wFalse rho t : rho ⊨ wFalse t <-> dom_rel (rho t) (rho (S t)).
    Proof.
    split.
    * intros H. apply H.
    * intros H. apply H.
    Qed.
    Opaque wFalse.

    Lemma IB_Not rho f t : rho ⊨ Not f t <-> ((rho ⊨ f) -> rho ⊨ wFalse t).
    Proof.
    split.
    * intros H. cbn in H. now rewrite IB_wFalse in H.
    * intros H. cbn. now rewrite IB_wFalse.
    Qed.
    Opaque Not.

    Definition rho_canon (rho : nat -> dom) := rho 0 = Num 0.

    Lemma IB_F_zero rho : rho_canon rho -> rho ⊨ F_zero.
    Proof.
      intros H0. cbn. now rewrite !H0.
    Qed.


    Lemma IB_N_e rho i n : rho i = n -> rho ⊨ N i -> {m:nat | Num m = n}.
    Proof.
    intros Hrho H. destruct n as [m|a b].
    * now exists m.
    * exfalso. cbn in H. rewrite Hrho in H. apply (@h10_rel_irref (a,b) H).
    Qed.

    Lemma IB_N_i rho i n : rho i = Num n -> (rho) ⊨ N i.
    Proof. cbn. intros ->. destruct (Nat.eqb n 0) eqn:H0.
    - destruct (Nat.eqb n 1) eqn:H1.
      + exfalso. pose (beq_nat_true n 0 H0) as HH0. pose (beq_nat_true n 1 H1) as HH1. congruence.
      + easy.
    - easy.
    Qed.
    Opaque N.

    Lemma IB_P'_e rho i n t : rho i = n -> rho ⊨ P' i t -> {a:nat & {b:nat & n = Pair a b}}.
    Proof.
    intros Hrho H. destruct n as [m|a b].
    * exfalso. unfold P' in H. rewrite IB_sNot in H. eapply H, IB_N_i, Hrho.
    * now exists a, b.
    Qed.

    Lemma IB_P'_i rho i a b t : rho i = (Pair a b) -> rho ⊨ P' i t.
    Proof.
    unfold P'. rewrite IB_sNot. intros Hrho H. destruct (@IB_N_e rho i (Pair a b)). 
    1-2:easy. congruence.
    Qed.
    Opaque P'.

    Lemma IB_P_e rho p l r ip il ir c t :
        rho ip = p -> rho il = l -> rho ir = r
     -> rho ⊨ P ip il ir t c -> {a:nat & {b:nat & p = Pair a b /\ l = Num a /\ r = Num b}} 
     -> rho ⊨ c.
    Proof.
    intros Hp Hl Hr H [a [b [Hp' [Hl' Hr']]]]. cbn in H. 
    rewrite Hp, Hl, Hr, Hp', Hl', Hr' in H. cbn in H. apply H.
    - eapply IB_P'_i. now rewrite Hp, Hp'.
    - eapply IB_N_i. now rewrite Hl, Hl'.
    - eapply IB_N_i. now rewrite Hr, Hr'.
    - easy.
    - easy.
    Qed.

    Lemma IB_P_i rho ip il ir c t : (forall a b, rho ip = (Pair a b) 
                                 -> rho il = (Num a) -> rho ir = (Num b) -> rho ⊨ c)
                                 -> rho ⊨ P ip il ir t c.
    Proof.
    intros Hplrc. intros [pa [pb Hp]]%(IB_P'_e (n:=rho ip))
                         [la Ha]%(IB_N_e (n:=rho il))
                         [rb Hb]%(IB_N_e (n:=rho ir)) Hpl Hpr. 2-4: easy.
    cbn in Hpl, Hpr. rewrite Hp,<-Ha,<-Hb  in *. apply (@Hplrc la rb); congruence.
    Qed.
    Opaque P.

    Lemma IB_F_succ_left rho : rho_canon rho -> rho ⊨ F_succ_left.
    Proof.
      intros H0. unfold F_succ_left. intros n [m Hnm]%(IB_N_e (n:=n)). 2:easy. 
      rewrite IB_Not. cbn. intros Hc.
      specialize (Hc (Pair m 0) (Num (S m)) (Pair (S m) 0)).
      eapply IB_P_e in Hc. 2-4:easy. 2: exists m, 0; cbn; auto.
      eapply IB_P_e in Hc. 2-4:easy. 2: exists (S m), 0; cbn; auto.
      rewrite IB_wFalse. unfold scons.
      cbn in Hc. rewrite IB_wFalse in Hc. unfold scons in Hc.
      apply Hc; split; lia.
    Qed.

    Lemma IB_rel_e rho ipl ipr ia ib ic id t tt : rho ⊨ rel ipl ipr ia ib ic id tt t 
                -> {a&{b&{c&{d|rho ipl=Pair a b
                            /\ rho ipr = Pair c d
                            /\ rho ia=Num a
                            /\ rho ib=Num b
                            /\ rho ic=Num c
                            /\ rho id=Num d
                            /\ h10upc_sem_direct ((a,b),(c,d))}}}} 
                -> rho ⊨ t.
    Proof.
    intros H [a [b [c [d [Hpl [Hpr [Ha [Hb [Hc [Hd Habcd]]]]]]]]]].
    unfold rel in H.
    eapply IB_P_e in H. 2-4: easy. 2: exists a, b; cbn; auto.
    eapply IB_P_e in H. 2-4: easy. 2: exists c, d; cbn; auto.
    apply H. cbn. rewrite Hpl, Hpr. easy.
    Qed.

    Lemma IB_rel_i rho ipl ipr ia ib ic id t tt :
                ({a&{b&{c&{d|rho ipl=Pair a b
                            /\ rho ipr = Pair c d
                            /\ rho ia=Num a
                            /\ rho ib=Num b
                            /\ rho ic=Num c
                            /\ rho id=Num d
                            /\ h10upc_sem_direct ((a,b),(c,d))}}}} -> rho ⊨ t)
             -> rho ⊨ rel ipl ipr ia ib ic id tt t.
    Proof.
    intros H.
    apply IB_P_i. intros a b Hpl Ha Hb.
    apply IB_P_i. intros c d Hpr Hc Hd.
    intros Habcd. apply H. exists a,b,c,d. cbn in Habcd. rewrite Hpl, Hpr in Habcd. now repeat split.
    Qed.

    Lemma IB_F_succ_right rho : rho_canon rho -> rho ⊨ F_succ_right.
    Proof.
      intros H0. unfold F_succ_right. intros p1 p2 p3 p4 p5 p6 p7 p8 a' y' c b a y x.
      apply IB_rel_i. cbn. intros [nx [ny [na [nb [Hp8 [Hp7 [Hx [Hy [Ha [Hb [Hr1l Hr1r]]]]]]]]]]].
      apply IB_rel_i. cbn. intros [nb' [ny' [nc [nb'' [Hp6 [Hp5 [Hb' [Hy' [Hc [Hb'' [Hr2l Hr2r]]]]]]]]]]].
      apply IB_rel_i. cbn. intros [ny'' [z [n'y [z' [Hp4 [Hp3 [Hy'' [Hz [H'y [Hz' [Hr3l Hr3r]]]]]]]]]]].
      apply IB_rel_i. cbn. intros [na' [z'' [n'a [z''' [Hp2 [Hp1 [Ha' [Hz'' [H'a [Hz''' [Hr4l Hr4r]]]]]]]]]]].
      unfold erel. cbn.
      rewrite IB_Not. intros H.
      rewrite H0 in *.
      specialize (H (Pair n'a (nc)) (Pair nx n'y)).
      eapply IB_P_e in H. 2-4: easy. 2: exists nx, n'y; cbn; firstorder.
      eapply IB_P_e in H. 2-4: easy. 2: exists n'a, nc; cbn; firstorder.
      cbn in H. rewrite IB_wFalse in H. apply H.
      assert (z=0 /\ z' = 0 /\ z'' = 0 /\ z''' = 0) as [Hz0 [Hz01 [Hz02 Hz03]]].
      1:firstorder;congruence. cbn -[dom_rel] in H.
      rewrite Hz0, Hz01, Hz02, Hz03 in *. split.
      - assert (ny'' = ny /\ na' = na) as [HHy HHa].
        1:firstorder;congruence. lia.
      - assert (nb' = nb /\ ny' = ny /\ ny'' = ny /\ na'=na) as [HHb [HHy [HHHy HHa]]].
        1:firstorder;congruence. lia.
    Qed.

    Definition rho_descr_phi rho (φ:nat->nat) n :=
         forall k, k < n -> match rho k with Num n => n = (φ k) | _ => True end.
    Lemma IB_single_constr rho φ (n:nat) (h:h10upc) : rho_descr_phi rho φ n 
                                           -> highest_var h < n
                                           -> rho ⊨ translate_single h (S n)
                                           -> (h10upc_sem φ h -> dom_rel (rho (1+n)) (rho (2+n)))
                                           -> dom_rel (rho (1+n)) (rho (2+n)).
    Proof.
      intros Hrhophi Hmaxhall. 
      destruct h as [[a b][c d]]. unfold translate_single. cbn in Hmaxhall.
      intros Htr Hcon. unfold erel in Htr. rewrite IB_Not in Htr.
      apply Htr.
      intros p2 p1.
      apply IB_P_i. cbn. intros na nb Hp1 Ha Hb.
      apply IB_P_i. cbn. intros nc nd Hp2 Hc Hd. rewrite Hp1, Hp2.
      intros Habcd.
      apply Hcon.
      assert (na = φ a) as ->. 1: pose (@Hrhophi a) as Hp; rewrite Ha in Hp; apply Hp; lia.
      assert (nb = φ b) as ->. 1: pose (@Hrhophi b) as Hp; rewrite Hb in Hp; apply Hp; lia.
      assert (nc = φ c) as ->. 1: pose (@Hrhophi c) as Hp; rewrite Hc in Hp; apply Hp; lia.
      assert (nd = φ d) as ->. 1: pose (@Hrhophi d) as Hp; rewrite Hd in Hp; apply Hp; lia.
      apply Habcd.
    Qed. 

    Lemma IB_emplace_forall rho n i : 
        (forall f, (fun k => if k <? n then f (k) else rho (k-n)) ⊨ i)
     -> rho ⊨ emplace_forall n i.
    Proof.
      intros H.
      induction n as [|n IH] in rho,H|-*.
      - cbn. eapply (sat_ext IB (rho := rho) (xi:=fun k => rho(k-0))).
        2: apply (H (fun _ => Num 0)).
        intros x. now rewrite Nat.sub_0_r.
      - intros d.
        specialize (IH (d.:rho)). apply IH. intros f.
        eapply (sat_ext IB (xi:=fun k => if k <? S n then (fun kk => if kk =? n then d else f kk) k else (rho) (k - S n))).
        2: eapply H.
        intros x.
        destruct (Nat.eq_dec x n) as [Hxn|Hnxn].
        + destruct (Nat.ltb_ge x n) as [_ Hlt]. rewrite Hlt. 2:lia. clear Hlt.
          destruct (Nat.ltb_lt x (S n)) as [_ Hlt]. rewrite Hlt. 2:lia. clear Hlt. cbn.
          assert (x-n=0) as ->. 1: lia. cbn. destruct (Nat.eqb_eq x n) as [_ HH]. now rewrite HH.
        + destruct (x <? n) eqn:Hneq.
          * destruct (Nat.ltb_lt x n) as [Hlt _]. apply Hlt in Hneq. clear Hlt.
            destruct (Nat.ltb_lt x (S n)) as [_ Hlt]. rewrite Hlt. 2:lia. clear Hlt.
            cbn. destruct (Nat.eqb_neq x n) as [_ HH]. rewrite HH. 1: easy. lia.
          * destruct (Nat.ltb_ge x n) as [Hlt _]. apply Hlt in Hneq. clear Hlt.
            destruct (Nat.ltb_ge x (S n)) as [_ Hlt]. rewrite Hlt. 2:lia. clear Hlt.
            assert (x-n=S(x-S n)) as ->. 1:lia. easy.
    Qed.
    Opaque emplace_forall. 

    Lemma IB_translate_rec rho phi f e hv : rho_descr_phi rho phi hv 
                            -> (rho ⊨ f <-> dom_rel (rho (1+hv)) (rho (2+hv)))
                            -> highest_var_list e < hv 
                            -> ((forall c, In c e -> h10upc_sem phi c) -> rho ⊨ f)
                            -> rho ⊨ translate_rec f (S hv) e.
    Proof.
    intros Hrhophi Hsat Hhv H.
    induction e as [|eh er IH] in H,Hsat,Hhv|-*.
    - apply H. intros l [].
    - cbn. intros Hts. apply IH.
      + easy.
      + cbn in Hhv. lia.
      + intros HH. rewrite Hsat. eapply (IB_single_constr (h:=eh)).
        * exact Hrhophi.
        * pose proof (@highest_var_list_descr (eh::er) eh ltac:(now left)). lia.
        * easy.
        * intros Hsem. rewrite <- Hsat. apply H. intros c [il|ir]. 2:now apply HH. congruence.
    Qed.

    Lemma IB_aux_transport rho : rho 0 = Num 0
                              -> rho 1 = Num 0
                              -> rho 2 = Num 1
                              -> rho ⊨ translate_constraints h10
                              -> H10UPC_SAT h10.
    Proof.
      intros Hrho0 Hrho1 Hrho2.
      pose ((S (highest_var_list h10))) as h10vars. 
      unfold translate_constraints. fold h10vars. intros H.
      cbn in H. rewrite Hrho1, Hrho2 in H.
      rewrite !Nat.eqb_refl in H. 
      apply H. 
      apply IB_emplace_forall. intros f.
      pose (fun n => match (f n) with (Num k) => k | _ => 0 end) as phi.
      eapply (IB_translate_rec (e:=h10) (hv:=h10vars) (phi:= phi)).
      - intros x HH. destruct (Nat.ltb_lt x h10vars) as [_ Hr]. rewrite Hr. 2:easy.
        unfold phi. now destruct (f x).
      - cbn -[dom_rel Nat.leb Nat.sub]. easy.
      - lia.
      - intros HG. cbn -[dom_rel Nat.leb Nat.sub].
        destruct (Nat.ltb_ge (S h10vars) h10vars) as [_ H1]. rewrite H1. 2:lia.
        destruct (Nat.ltb_ge (S (S h10vars)) h10vars) as [_ H2]. rewrite H2. 2:lia.
        assert (S h10vars-h10vars = 1) as ->. 1:lia. 
        assert (S(S h10vars)-h10vars = 2) as ->. 1:lia.
        rewrite Hrho1, Hrho2. cbn. exists phi. easy.
    Qed.

    Lemma IB_fulfills rho : rho ⊨ F -> H10UPC_SAT h10.
    Proof.
      intros H. unfold F in H. pose (Num 0 .: Num 0 .: Num 1 .: rho) as nrho. assert (rho_canon nrho) as nrho_canon.
      1: split; easy.
      apply (@IB_aux_transport nrho), H. 
      - easy.
      - easy.
      - easy.
      - now apply IB_F_zero.
      - now apply IB_F_succ_left.
      - now apply IB_F_succ_right.
    Qed.
  End InverseTransport.

  Lemma inverseTransport : valid F -> H10UPC_SAT h10.
  Proof.
    intros H. apply (@IB_fulfills (fun b => Num 0)). apply H.
  Qed.
End validity.
















