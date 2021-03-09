(* * FOL Reductions *)

From Undecidability.DiophantineConstraints Require Import H10UPC H10UPC_undec.
From Undecidability.FOL Require Import Util.Syntax Util.Deduction Util.FullTarski  Util.FullTarski_facts Util.Syntax_facts.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Coq Require Import Arith Lia List.

(* ** Validity *)

(**
Idea: The special star (#) has the following properties:
n ~ p: n is left component of p
p ~ n: p is right component of p
p ~ p: the special relationship of H10UPC
n ~ m: n = m
*)


(* Set Default Proof Using "Type". *)
Set Default Goal Selector "!".

Inductive syms_func : Type := .

Instance sig_func : funcs_signature :=
  {| syms := syms_func; ar_syms := fun f => match f with end|}.

Inductive syms_pred := sPr.

Instance sig_pred : preds_signature :=
  {| preds := syms_pred; ar_preds := fun P => 2 |}.

Notation Pr t t' := (@atom _ sig_pred _ _ sPr (Vector.cons _ t _ (Vector.cons _ t' _ (Vector.nil _)))).

Notation i_Pr i i' :=
  (@i_atom _ _ _ _ sPr (Vector.cons _ i _ (Vector.cons _ i' _ (Vector.nil _)))).

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
  End Utils.

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

Section validity.

  Context {ff : falsity_flag}. 
  Context {h10 : list h10upc}.
  (* All are placed in a context where $0 is the 0 constant and $1 is the star, outermostly quantified *)
  Definition F_zero := Pr $0 $1 ∧ (∀ Pr $0 $1 ~> Pr $2 $0) 
                      ∧ (∀ ∀ Pr $0 $2 ~> Pr $3 $0 ~> Pr $3 $1 ~> Pr $0 $1 ~> Pr $1 $2)
                      ∧ (∀ ∀ Pr $3 $0 ~> Pr $3 $1 ~> Pr $0 $1 ~> Pr $2 $1 ~> Pr $3 $3 ).
  Definition F_makepair := ∀ ∀ Pr $0 $3 ~> Pr $1 $3 ~> (∃ Pr $4 $0 ∧ Pr $2 $0 ∧ Pr $0 $1).
  Definition F_succ_left := ∀ ∀ Pr $0 $3 ~> Pr $3 $1 ~> Pr $0 $1 ~> Pr $1 $2 ~> ∃ ∃ Pr $0 $5 ∧ Pr $5 $1 ∧ Pr $3 $1 ∧ Pr $0 $1 ∧ Pr $1 $4.
  Definition F_succ_right := 
         ∀ ∀ ∀ ∀ ∀ ∀ ∀ ∀                                                    (* nums quantors *)
         ∀ ∀ ∀ ∀ ∀ ∀ ∀ ∀ ∀ ∀                                                (* pairs quantors *)
         Pr $19 $0 ~> Pr $19 $1 ~> Pr $19 $2 ~> Pr $19 $3 ~> Pr $19 $4      (* pairs *)
         ~> Pr $19 $5 ~> Pr $19 $6 ~> Pr $19 $7 ~> Pr $19 $8 ~> Pr $19 $9   (* are pairs *)
         ~> Pr $10 $19 ~> Pr $11 $19 ~> Pr $12 $19 ~> Pr $13 $19            (* and nums *)
         ~> Pr $14 $19 ~> Pr $15 $19 ~> Pr $16 $19 ~> Pr $17 $19            (* are nums *)
         ~> Pr $10 $0 ~> Pr $0 $11 ~> Pr $12 $1 ~> Pr $1 $13 ~> Pr $0 $1    (* (x,y)#(a,b) *)
         ~> Pr $13 $2 ~> Pr $2 $11 ~> Pr $14 $3 ~> Pr $3 $15 ~> Pr $2 $3    (* (b,y)#(c,d) *)
         ~> Pr $11 $4 ~> Pr $4 $18 ~> Pr $16 $5 ~> Pr $5 $18 ~> Pr $4 $5    (* (y,0)#(y',0) *)
         ~> Pr $12 $6 ~> Pr $6 $18 ~> Pr $17 $7 ~> Pr $7 $18 ~> Pr $6 $7    (* (a,0)#(a',0) *)
         ~> Pr $10 $8 ~> Pr $8 $16 ~> Pr $17 $9 ~> Pr $9 $14 ~> Pr $8 $9.   (* -> (x,y')#(a',c) *)

  Fixpoint emplace_exists (n:nat) (i:form) := match n with 0 => i | S n => ∃ (emplace_exists n i) end. 
  Definition translate_single (nv:nat) (h:h10upc) := 
          match h with ((a,b),(c,d)) => 
            ∃ ∃ Pr $(nv+3) $0 ∧ Pr $(nv+3) $1 
              ∧ Pr $(a+2) $(nv+3) ∧ Pr $(b+2) $(nv+3) ∧ Pr $(c+2) $(nv+3) ∧ Pr $(d+2) $(nv+3)
              ∧ Pr $(a+2) $1 ∧ Pr $1 $(b+2) ∧ Pr $(c+2) $0 ∧ Pr $0 $(d+2)
              ∧ Pr $1 $0 end.
  Fixpoint translate_rec (nv:nat)  (base:form) (l:list h10upc) := match l with nil => base
                                                                         | l::lr => translate_single nv l ∧ translate_rec nv base lr end.
  Definition translate_constraints (x:list h10upc) := 
    let nv := S (highest_var_list x)
    in emplace_exists nv (translate_rec nv (Pr $nv $(S nv)) x).


  Definition F := ∀ ∀ F_zero ~> F_makepair ~> F_succ_left ~> F_succ_right ~> translate_constraints h10.

  Section Transport.
    (* The solution to cs *)
    Context (φ: nat -> nat). 
    (* Proof that it actually is a solution *)
    Context (Hφ : forall c, In c h10 -> h10upc_sem φ c). 
    Context (D:Type).
    Context (I:interp D).
    Context (rho:env D).
    Context (zero star:D).
    Context (vF_zero : (zero .: star .: rho) ⊨ F_zero).
    Context (vF_makepair : (zero .: star .: rho) ⊨ F_makepair).
    Context (vF_succ_left : (zero .: star .: rho) ⊨ F_succ_left).
    Context (vF_succ_right : (zero .: star .: rho) ⊨ F_succ_right).
    
    Definition isNum (d:D) := i_Pr d star.
    Definition isPair (p l r:D) := isNum l /\ isNum r /\ i_Pr star p /\ i_Pr l p /\ i_Pr p r.
    
    Definition repr_nums f n := f 0 = zero /\ forall m:nat, m < n -> 
              exists (pl pr:D), isNum (f (S m)) /\ isPair pl (f m) zero /\ isPair pr (f (S m)) zero /\ i_Pr pl pr.
    Fixpoint constr_nums (n:nat) : exists f:nat -> D, repr_nums f n.
    Proof.
    induction n as [|n [f [IHfz IHfS]]].
    - exists (fun _ => zero). split. 1: easy. intros m H. exfalso. lia.
    - destruct n as [|n].
      + cbn. destruct (@vF_makepair zero zero) as [pzero Hzero]; cbn. 1-2: apply vF_zero.
        cbn in Hzero.
        destruct (@vF_succ_left pzero zero) as [pone [one Hone]]; cbn. 1: apply vF_zero. 1-3: apply Hzero.
        cbn in Hone. exists (fun m:nat => if Nat.eq_dec 1 m then one else f m).
        split. 1: apply IHfz.
        intros m Hm. assert (m=0) as Hm0. 1:lia. rewrite Hm0. cbn. rewrite IHfz. exists pzero, pone.
        repeat split.
        2,3,8: apply vF_zero. 1,5: apply Hone. 1-3: apply Hzero. all: apply Hone.
      + pose (f (S n)) as n'.
        destruct (IHfS n ltac:(lia)) as [pl' [pr' Hplr']].
        destruct (@vF_succ_left pr' n') as [p [d Hdp]]; cbn. 1-4: apply Hplr'.
        cbn in Hdp. exists (fun m:nat => if Nat.eq_dec (S (S n)) m then d else f m).
        split. 1: apply IHfz.
        intros m Hm. assert (m <> S(S n)) as Hmn. 1:lia. destruct (Nat.eq_dec (S (S n)) m). 1: exfalso; lia.
        destruct (Nat.eq_dec (S (S n)) (S m)) as [Heq|Hneq].
        * exists pr', p. assert (S n = m) as Hmneq. 1: lia. rewrite <- Hmneq. split. 2:split. 3:split.
          -- apply Hdp.
          -- apply Hplr'.
          -- repeat split. 2:apply vF_zero. all: apply Hdp.
          -- apply Hdp.
        * destruct (IHfS m (ltac:(lia))) as [pl [pr H]]. exists pl, pr. apply H.
    Qed.

    Lemma repr_num_isNum (f:nat -> D) (n:nat) (m:nat) : repr_nums f n -> m <= n -> isNum (f m).
    Proof.
    intros [Hzero Hrepr] Hnm.
    destruct m as [|m].
    - rewrite Hzero. apply vF_zero.
    - destruct (Hrepr m Hnm) as [pl [pr H]]. apply H.
    Qed.
    
    Lemma h10upc_inv (a b c d : nat) : h10upc_sem_direct ((a,S b),(c,d)) -> 
             {c':nat & {d':nat & h10upc_sem_direct ((a,b),(c',d')) /\ S c' = c /\ d' + b + 1 = d}}.
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

    Lemma make_pair (a b : nat) (f:nat -> D) (n:nat) : repr_nums f n -> a <= n -> b <= n
                                   -> exists p:D, isPair p (f a) (f b).
    Proof.
    intros [Hzero Hrepr] Han Hbn.
    assert (isNum (f a)). 1: eapply (@repr_num_isNum f n). 1: split. 1-3: easy.
    assert (isNum (f b)). 1: eapply (@repr_num_isNum f n). 1: split. 1-3: easy.
    destruct (@vF_makepair (f a) (f b)) as [p Hp]. 1-2: easy.
    cbn in Hp. exists p. repeat split. 1-2: easy. all: apply Hp.
    Qed.


    Lemma constr_rel (a b c d : nat) (f:nat -> D) (n:nat) : repr_nums f n -> b <= n -> a <= n -> c <= n -> d <= n
                                                      -> h10upc_sem_direct ((a,b),(c,d)) -> exists pl pr, isPair pl (f a) (f b) /\ isPair pr (f c) (f d) /\ i_Pr pl pr.
    Proof.
    intros Hreprnums Hbn.
    pose proof Hreprnums as Hrepr_nums.
    destruct Hreprnums as [Zrepr Hrepr].
    induction b as [|b IH] in a,c,d|-*; intros Han Hcn Hdn Habcd.
    - cbn in Habcd. assert (c = S a /\ d = 0) as [Hc Hd]. 1:lia.
      rewrite Hd in *. rewrite ! Zrepr. rewrite Hc. destruct (Hrepr a) as [pl [pr Hplr]]. 1:lia. 
      exists pl, pr. split. 2: split. all: apply Hplr.
    - destruct (@h10upc_inv a b c d Habcd) as [c' [d' [Habcd' [Hc' Hd']]]]. rewrite <- Hc' in *. rewrite <- Hd' in *.
      assert (h10upc_sem_direct ((d',b),(d'+b+1,d'))) as Hdb.
      +  split. 1: lia. apply Habcd'.
      + destruct (IH a c' d' Han ltac:(lia) ltac:(lia) Habcd') as [pab [pc'd' Hpabc'd']].
        destruct (IH d' (d'+b+1) d') as [pd'b [pd'bd' Hpd'b]]. 1-3: lia. 1: easy.
        destruct (@make_pair a (S b) f n) as [paSb HpaSb]. 1: split; easy. 1: easy. 1: lia.
        destruct (@make_pair (S c') (d' + b + 1) f n) as [pScsum HpScsum]. 1:split; easy. 1:lia. 1:lia.
        exists paSb, pScsum. split. 1:easy. split. 1:easy.
        destruct (Hrepr b) as [pb [pb' Hpb]]. 1:lia.
        destruct (Hrepr c') as [pc [pc' Hpc]]. 1:lia.
        apply (@vF_succ_right (f (S c')) (f (S b)) (f d') (f(d' + b + 1)) (f d') (f c') (f b) (f a) 
                               pScsum paSb  pc' pc pb' pb pd'bd' pd'b pc'd' pab); cbn.
        1-2: apply Hpabc'd'. 1-2: apply Hpd'b. 1-2: apply Hpb. 1-2: apply Hpc. 1: apply HpaSb. 1: apply HpScsum.
        1-8: eapply (@repr_num_isNum f n); try easy; lia.
        1-5: apply Hpabc'd'.
        1-5: apply Hpd'b.
        1-5: apply Hpb.
        1-5: apply Hpc.
        1-2: apply HpaSb.
        1-2: apply HpScsum.
    Qed.
    
    Lemma prove_emplace_exists (n:nat) (i:form) (r:env D) (f:nat->D) :
    (fun v => if v <? n then f v else r (v-n)) ⊨ i
    -> r ⊨ emplace_exists n i.
    Proof.
    induction n as [|n IH] in r|-*.
    - cbn. intros H. apply (FullTarski_facts.sat_ext I (rho := r) (xi:=fun v => r(v-0)) i).
      + intros x. rewrite Nat.sub_0_r. easy.
      + easy.
    - intros H. cbn. exists (f n). specialize (IH (f n .: r)). apply IH.
      apply (FullTarski_facts.sat_ext I (rho := (fun v : nat => if v <? S n then f v else r (v - S n))) i).
      + intros x. destruct (Nat.eq_dec x n) as [Hxn|Hnxn].
        * destruct (Nat.ltb_lt x (S n)) as [_ Hr]. specialize (Hr ltac:(lia)). rewrite Hr. 
          destruct (Nat.ltb_ge x n) as [_ Hr2]. specialize (Hr2 ltac:(lia)). rewrite Hr2.
          assert (x-n=0) as Hxn0. 1:lia. rewrite Hxn0. cbn. now f_equal.
        * destruct (x <? n) as [|] eqn:Hxn.
          -- apply (Nat.ltb_lt) in Hxn. assert (x <? S n = true) as Hxn2. 1: apply Nat.ltb_lt; lia.
             rewrite Hxn2. easy.
          -- apply (Nat.ltb_ge) in Hxn. assert (x <? S n = false) as Hxn2. 1: apply Nat.ltb_ge; lia.
             rewrite Hxn2. assert (x-n = S(x-S n))  as Hxn3. 1:lia. rewrite Hxn3. cbn. easy.
      + easy.
    Qed.

    Lemma prove_constraints : (zero .: star .: rho) ⊨ translate_constraints h10.
    Proof.
    pose (S (highest_var_list h10)) as h10vars.
    unfold translate_constraints. fold h10vars.
    pose (highest_num φ h10vars) as h10max.
    destruct (constr_nums h10max) as [f Hf].
    pose (fun n => f (φ n)) as ef.
    eapply (@prove_emplace_exists h10vars _ _ ef).
    pose (fun v : nat => if v <? h10vars then ef v else (zero .: star .: rho) (v - h10vars)) as newenv. fold newenv.
    assert (forall c:h10upc, In c h10 -> newenv ⊨ translate_single h10vars c).
    - intros [[a b][c d]] Hin. cbn.
      pose (@highest_var_list_descr h10 ((a,b),(c,d)) Hin) as Habcdmax. cbn in Habcdmax. fold h10vars in Habcdmax.
      destruct (@constr_rel (φ a) (φ b) (φ c) (φ d) f h10max Hf) as [pab [pcd [Hpab [Hpcd Hpp]]]].
      1-4: eapply highest_num_descr; lia.
      1: apply (@Hφ ((a,b),(c,d)) Hin).
      assert (newenv (S h10vars) = star) as Hstar.
      1:{ unfold newenv. destruct (Nat.ltb_ge (S h10vars) (h10vars)) as [_ ->]. 1:enough (S h10vars-h10vars=1) as ->. all: now try lia. }
      assert (forall k:nat, k < h10vars -> newenv k = f (φ k)) as Hvars.
      1:{ unfold newenv. intros k Hk. destruct (Nat.ltb_lt k h10vars) as [_ Hr]. now rewrite Hr. }
      exists pab, pcd. repeat split. 1-6: erewrite (Nat.add_comm (highest_var_list h10)); cbn. 3-10: rewrite Nat.add_comm; cbn.
      all: fold h10vars.
      1-6: rewrite Hstar.
      3-10: erewrite Hvars; [idtac|lia].
      2-4,7,8: apply Hpab. 1-5: apply Hpcd. apply Hpp.
   - induction h10 as [|hx hr IH] in H|-*. 2:split.
     + cbn. unfold newenv.
       destruct (Nat.ltb_ge h10vars h10vars) as [_ Hr]. rewrite Hr. 2:lia. clear Hr.
       destruct (Nat.ltb_ge (S h10vars) h10vars) as [_ Hr]. rewrite Hr. 2:lia.
       assert (h10vars-h10vars=0) as ->. 1:lia.
       assert (S h10vars-h10vars=1) as ->. 1:lia.
       apply vF_zero.
     + apply H. now left.
     + apply IH. intros c Hc. apply H. now right.
    Qed.
  End Transport.

  Lemma transport : H10UPC_SAT h10 -> valid F.
  Proof.
    intros [φ Hφ].
    intros D I rho.
    intros star zero.
    intros H_zero.
    intros H_makepair.
    intros H_succ_left H_succ_right. eapply prove_constraints.
    1: exact Hφ.
    1-4: easy.
  Qed.

  Section InverseTransport.

    Inductive num_pair_star : Type := Num : nat -> num_pair_star | Pair : nat  -> nat -> num_pair_star | Star.
    Definition nps_rel (a : num_pair_star) (b:num_pair_star) : Prop := match (a,b) with
      (Num n1, Num n2) => False
    | (Num n1, Star) => True
    | (Num n1, Pair x2 y2) => n1 = x2
    | (Pair x1 y1, Num n2) => n2 = y1
    | (Pair x1 y1, Pair x2 y2) => 1 + x1 + y1 = x2 /\ y1 * (1 + y1) = y2 + y2
    | (Pair x1 y1, Star) => False
    | (Star, Num n2) => False
    | (Star, Pair x2 y2) => True
    | (Star, Star) => False end.

    Global Instance IB : interp (num_pair_star).
    Proof.
      split; intros [] v.
      exact (nps_rel (Vector.hd v) (Vector.hd (Vector.tl v))).
    Defined.


    Lemma Pr_irref (d:num_pair_star) : i_Pr d d -> False.
    cbn. destruct d as [n|x y|].
    - easy.
    - lia.
    - easy.
    Qed.

    Definition rho_canon (rho : nat -> num_pair_star) := rho 0 = Num 0 /\ rho 1 = Star.

    Lemma IB_F_zero rho : rho_canon rho -> rho ⊨ F_zero.
    Proof.
      (*split.
      - unfold rho_canon. cbn. destruct (rho 0) as [n|x y|], (rho 1) as [n'|x' y'|].
        + intros [[[H0 H3] H4] H5]. easy.
        + intros [[[H0 H3] H4] H5]. exfalso. destruct (H3 (Pair x' x')) as [Hl Hr]. 1: easy. lia.
        + intros [[[H0 H3] H4] H5]. destruct (Nat.eq_dec n 0) as [Ht|Hf]. 1: split; congruence.
          exfalso. assert (n=c2 n) as H'.
          * apply (H4 (Pair (S n) (c2 n)) (Pair 0 n)). 1-3:easy. split. 1:lia. apply c2_descr.
          * pose proof (c2_descr n) as Hn. rewrite <- H' in Hn. assert (n=1) by nia.
            apply (H5 (Pair 1 0) (Pair 0 0)). 1-2,4: easy. lia.
        + intros [[[H0 H3] H4] H5]. specialize (H4 (Pair n' x) Star). cbn in H4. destruct H4 as [H4l H4r]. 1-4: easy. exfalso. lia.
        + intros [[[H0 H3] H4] H5]. specialize (H3 Star); cbn in H3. exfalso. now apply H3.
        + intros [[[H0 H3] H4] H5]. easy.
        + intros [[[H0 H3] H4] H5]. easy.
        + intros [[[H0 H3] H4] H5]. enough (S y' = y') by lia. now apply (H3 (Num (S y'))).
        + intros [[[H0 H3] H4] H5]. easy.
      - *) intros [H0 H1]. cbn. rewrite !H0, !H1. cbn. split. 1:split. 1:split. 1:tauto.
        - intros [n|x y|]; tauto.
        - intros [n|x y|] [n'|x' y'|]. 5: {intros Hy [] [] [_ Hr]. rewrite <- Hy in Hr. lia. } all: tauto. 
        - intros [n|x y|] [n'|x' y'|]. 5: {intros [] [] [Hx Hy] Hx0. lia. } all: tauto.
    Qed.

    Lemma IB_F_makepair rho : rho_canon rho -> rho ⊨ F_makepair.
    Proof.
      intros [r0 r1]. cbn. rewrite ! r1. intros [n|x y|]. 2-3:tauto. intros [n'|x' y'|]. 2-3:tauto. intros [] [].
      exists (Pair n n'). tauto.
    Qed.

    Lemma IB_F_succ_left rho : rho_canon rho -> rho ⊨ F_succ_left.
    Proof.
      intros [r0 r1]. cbn. rewrite ! r0, ! r1. intros [n|x y|] [n'|x' y'|]. 1-3,5-9: tauto.
      intros [] [] x'0 y'0. exists (Pair (S n') 0), (Num (S n')). rewrite <- ! y'0, <- ! x'0. nia.
    Qed.

    Lemma IB_F_succ_right rho : rho_canon rho -> rho ⊨ F_succ_right.
    Proof.
      intros [r0 r1]. cbn. rewrite ! r0, ! r1. 
      intros [a'|x y|]. 2,3:tauto.
      intros [y'|x y|]. 2,3:tauto.
      intros [d|x y|]. 2,3:tauto.
      intros [c|x y|]. 2,3:tauto.
      intros [b|x y|]. 2,3:tauto.
      intros [a|x y|]. 2,3:tauto.
      intros [y|x_ y_|]. 2,3:tauto.
      intros [x|x_ y_|]. 2,3:tauto.

      intros [v|pa' pc|]. 1,3: tauto.
      intros [v|px py'|]. 1,3: tauto.
      intros [v|pa'2 p0|]. 1,3: tauto.
      intros [v|pa p02|]. 1,3: tauto.
      intros [v|py'2 p03|]. 1,3: tauto.
      intros [v|py p04|]. 1,3: tauto.
      intros [v|pc2 pd|]. 1,3: tauto.
      intros [v|pb py3|]. 1,3: tauto.
      intros [v|pa2 pb2|]. 1,3: tauto.
      intros [v|px2 py4|]. 1,3: tauto.
      do 18 (intros []).
      do 4 (intros H; rewrite <- H; clear H); intros [Hp1l Hp1r].
      do 4 (intros H; rewrite <- H; clear H); intros [Hp2l Hp2r].
      do 4 (intros H; rewrite <- H; clear H); intros [Hp3l Hp3r].
      do 4 (intros H; rewrite <- H; clear H); intros [Hp4l Hp4r].
      do 4 (intros H; rewrite <- H; clear H).
      split; nia.
    Qed.

    Definition rho_descr_phi rho (φ:nat->nat) n := forall k, k < n -> match rho k with Num n => n = (φ k) | _ => True end.
    Lemma IB_single_constr rho φ (n:nat) (h:h10upc) : rho_descr_phi rho φ n 
                                           -> rho_canon (fun k => rho (k + n)) 
                                           -> highest_var h < n
                                           -> rho ⊨ translate_single n h
                                           -> h10upc_sem φ h.
    Proof.
      intros Hrhophi [Hrho0 Hrho1] Hmaxhall .
      destruct h as [[a b][c d]].
      intros [p1 [p2 Hp1p2]].
      pose (@highest_var_descr ((a,b),(c,d))) as Hmaxh. cbn in Hmaxh,Hmaxhall.
      Opaque nps_rel. cbn in Hp1p2. rewrite Nat.add_comm in Hp1p2. rewrite <- ! (Nat.add_comm 2) in Hp1p2. cbn in Hp1p2. Transparent nps_rel.
      cbn in Hrho0, Hrho1.
      rewrite ! Hrho1 in Hp1p2.
      destruct (rho a) as [ra|l r|]eqn:Hra. 2-3: exfalso; apply Hp1p2.
      destruct (rho b) as [rb|l r|]eqn:Hrb. 2-3: exfalso; apply Hp1p2.
      destruct (rho c) as [rc|l r|]eqn:Hrc. 2-3: exfalso; apply Hp1p2.
      destruct (rho d) as [rd|l r|]eqn:Hrd. 2-3: exfalso; apply Hp1p2.
      assert (ra = φ a) as Hφa. 1: pose (@Hrhophi a) as Ha; rewrite Hra in Ha; apply Ha. 1:lia.
      assert (rb = φ b) as Hφb. 1: pose (@Hrhophi b) as Ha; rewrite Hrb in Ha; apply Ha. 1:lia.
      assert (rc = φ c) as Hφc. 1: pose (@Hrhophi c) as Ha; rewrite Hrc in Ha; apply Ha. 1:lia.
      assert (rd = φ d) as Hφd. 1: pose (@Hrhophi d) as Ha; rewrite Hrd in Ha; apply Ha. 1:lia.
      cbn. destruct p1 as [n''|a' b'|], p2 as [n'|c' d'|].
      1-4,6-9: exfalso; apply Hp1p2.
      cbn in Hp1p2. destruct Hp1p2 as [[[[[Hp1 Hp2] Hp3] Hp4] Hp5] Hp6].
      congruence.
    Qed.

    Lemma IB_emplace_exists rho n i : rho ⊨ emplace_exists n i -> exists f, (fun k => if k <? n then f (k) else rho (k-n)) ⊨ i.
    Proof.
      intros H.
      induction n as [|n IH] in rho,H|-*.
      - cbn in H. cbn. exists (fun n => Star). eapply (sat_ext IB (rho := rho) (xi:=fun k => rho(k-0))). 2: easy.
        intros x. now rewrite Nat.sub_0_r.
      - destruct H as [d H].
        destruct (IH (d.:rho) H) as [f IHf].
        exists (fun v => if Nat.eq_dec v n then d else f v).
        eapply (sat_ext IB (xi:=fun k => if k <? n then f k else (d .: rho) (k - n))). 2:apply IHf.
        intros x.
        destruct (Nat.eq_dec x n) as [Hxn|Hnxn].
        + destruct (Nat.ltb_ge x n) as [_ Hlt]. rewrite Hlt. 2:lia. clear Hlt.
          destruct (Nat.ltb_lt x (S n)) as [_ Hlt]. rewrite Hlt. 2:lia. clear Hlt. cbn.
          assert (x-n=0) as ->. 1: lia. cbn. congruence.
        + destruct (x <? n) eqn:Hneq.
          * destruct (Nat.ltb_lt x n) as [Hlt _]. apply Hlt in Hneq. clear Hlt.
            destruct (Nat.ltb_lt x (S n)) as [_ Hlt]. rewrite Hlt. 2:lia. clear Hlt. cbn. easy.
          * destruct (Nat.ltb_ge x n) as [Hlt _]. apply Hlt in Hneq. clear Hlt.
            destruct (Nat.ltb_ge x (S n)) as [_ Hlt]. rewrite Hlt. 2:lia. clear Hlt. assert (x-n=S(x-S n)) as ->. 1:lia. easy.
    Qed.

    Lemma IB_aux_transport rho : rho_canon rho -> rho ⊨ translate_constraints h10 -> H10UPC_SAT h10.
    Proof.
      intros [Hrho0 Hrho1].
      unfold translate_constraints. intros H.
      pose (highest_var_list h10) as h10max. fold h10max in H.
      edestruct (@IB_emplace_exists rho) as [f Hf]. 1: exact H.
      exists (fun k => match f k with Num n => n | _ => 0 end).
      intros c. pose proof (@highest_var_list_descr h10 c) as Hmaxh10. fold h10max in Hmaxh10.
      induction h10 as [|hx hr IH] in Hf,Hmaxh10|-*.
      - intros [].
      - intros [chx|chr].
        + destruct c as [[a b][c d]]. destruct Hf as [Hf _]. rewrite chx in *. eapply IB_single_constr.
          4: exact Hf.
          3: specialize (Hmaxh10 ltac:(now left)); lia.
          * intros k Hk. destruct (Nat.ltb_lt k (S h10max)) as [_ Hr]. rewrite Hr. 2:easy. destruct (f k) as [n|l r|]; easy.
          * split.
            -- destruct (Nat.ltb_ge (0+S h10max) (S h10max)) as [_ Hr]. rewrite Hr. 2:lia. cbn. assert (h10max-h10max=0) as ->. 1:lia. easy.
            -- destruct (Nat.ltb_ge (1+S h10max) (S h10max)) as [_ Hr]. rewrite Hr. 2:lia. assert (1+S h10max-S h10max=1) as ->. 1:lia. easy.
        + apply IH.
          * destruct Hf as [_ Hfr]. apply Hfr.
          * intros chr2. apply Hmaxh10. now right.
          * easy.
    Qed.

    Lemma IB_fulfills rho : rho ⊨ F -> H10UPC_SAT h10.
    Proof.
      intros H. unfold F in H. pose (Num 0 .: Star .: rho) as nrho. assert (rho_canon nrho) as nrho_canon.
      1: split; easy.
      apply (@IB_aux_transport nrho), H. 
      - easy.
      - now apply IB_F_zero.
      - now apply IB_F_makepair.
      - now apply IB_F_succ_left.
      - now apply IB_F_succ_right.
    Qed.
  End InverseTransport.

  Lemma inverseTransport : valid F -> H10UPC_SAT h10.
  Proof.
    intros H. apply (@IB_fulfills (fun b => Star)). apply H.
  Qed.
End validity.
Check @inverseTransport.

















