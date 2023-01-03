(* * FOL Reductions *)

From Undecidability.DiophantineConstraints Require Import H10C.
From Undecidability.DiophantineConstraints.Util Require Import H10UPC_facts.
From Undecidability.FOL Require Import Syntax.Facts Deduction.FragmentNDFacts Semantics.Tarski.FragmentSoundness Semantics.Tarski.FragmentFacts Syntax.BinSig Semantics.Kripke.FragmentCore  Semantics.Kripke.FragmentSoundness Semantics.Kripke.FragmentToTarski.
From Undecidability.FOL.Reductions Require Import H10UPC_to_FOL_minimal H10UPC_to_FOL_constructions.
From Undecidability.Shared Require Import Dec.
From Undecidability.Shared.Libs.PSL Require Import Numbers.
From Undecidability.Synthetic Require Import Definitions.
From Coq Require Import Arith Lia List.


(* ** Validity *)

(*
Idea: The relation (#&#35;#) has the following properties:#<ul>#
#<li>#n ~ p: n is left component of p#</li>#
#<li>#p ~ n: p is right component of p#</li>#
#<li>#p ~ p: the special relationship of H10UPC#</li>#
#<li>#n ~ m: n = m. Special case n=0, m=1: #<br />#
          The instance h10 of H10UPC is a yes-instance. #<br />#
          This is to facilitate Friedman translation#</li>#
*)


Set Default Proof Using "Type".
Set Default Goal Selector "!".


Notation Pr t t' := (@atom _ sig_binary _ _ tt (Vector.cons _ t _ (Vector.cons _ t' _ (Vector.nil _)))).

(* The validity reduction.
    We assume a generic falsity flag and a list h10 for which we build a formula.
 *)
Section validity.

  Context {ff : falsity_flag}. 
  Context {h10 : list h10upc}.
  (* All are placed in a context where $0 is the 0 constant and $1, $2 are arbitrary but fixed *)
  (* We do a Friedman translation, where this represents falsity *)
  Definition wFalse t:= Pr $t $(S t).
  (* We use a stronger version of falsity, which is <-> False in our standart model, to ease writing eliminators *)
  Definition sFalse := ∀ ∀ Pr $0 $1.
  (* Friedman not *)
  Definition Not k t := k → wFalse t.
  (* $k is a number *)
  Definition N k := Pr $k $k.
  (* $k is a pair *)
  Definition P' k (_:nat):= (N k) → sFalse.
  (* If $k is a pair ($l,$r), where $l, $r are numbers, then c. *)
  Definition P k l r t c := P' k t → N l → N r → Pr $l $k → Pr $k $r → c.
  (* if the pairs $pl = ($a,$b), $pr = ($c,$d) are in relation, then t *)
  Definition rel pl pr a b c d tt t := P pl a b tt (P pr c d tt (Pr $pl $pr → t)).
  (* There exist (Friedman translated) pairs relating ($a,$b) to ($c,$d) *)
  Definition erel a b c d t := Not (∀ ∀ P 0 (2+a) (2+b) (2+t) 
                                        (P 1 (2+c) (2+d) (2+t) 
                                         (Pr $0 $1 → wFalse (2+t)))) t.
  (* Axiom 1 - zero is a number *)
  Definition F_zero := N 0.
  (* Axiom 2 - we can build (left) successors: for each pair (a,0) we have a pair (S a, 0) *)
  Definition F_succ_left := ∀ N 0 → Not (∀ ∀ ∀ P 2 3 4 5
                                                 (P 0 1 4 5
                                                  (Pr $2 $0 → wFalse 5))) 2.
  (* Axiom 3 - we can build right successors: (x,y)#(a,b) -> (x,S y)#(S a,S (b+y)) *)
  Definition F_succ_right := ∀ ∀ ∀ ∀ ∀ ∀ ∀ ∀         (*8 pairs *)
                             ∀ ∀ ∀ ∀ ∀ ∀ ∀           (* 0 x 1 y 2 a 3 b 4 c 5 y' 6 a' 15 zero-const*)
                             rel 7 8 0 1 2 3 16      (* (x,y) # (a,b) *)
                            (rel 9 10 3 1 4 3 16     (* (b,y) # (c,b) *)
                            (rel 11 12 1 15 5 15 16  (* (y,0) # (y',0) *)
                            (rel 13 14 2 15 6 15 16  (* (a,0) # (a'0) *)
                            (erel 0 5 6 4 16))))     (* (x,y') # (a',c) *).
  (* Generate n all quantifiers around i *)
  Fixpoint emplace_forall (n:nat) (i:form) :=
          match n with 0 => i
        | S n => ∀ (emplace_forall n i) end.
  (* Translate our formula, one relation at a time *) 
  Definition translate_single (h:h10upc) nv := 
          match h with ((a,b),(c,d)) => 
            erel a b c d nv end.
  (* Translate an entire instance of H10UPC, assuming a proper context *)
  Fixpoint translate_rec (t:form) (nv:nat) (l:list h10upc) := 
          match l with nil => t
                     | l::lr => translate_single l nv → translate_rec t nv lr end.
  (* Actually translate the instance of H10UPC, by creating a proper context *)
  Definition translate_constraints (x:list h10upc) := 
    let nv := S (highest_var_list x)
    in (emplace_forall nv (translate_rec (Pr $(S nv) $(2+nv)) (S nv) x)) → Pr $1 $2.

  (* The actual reduction instance. If h10 is a yes-instance of H10UPC, this formula is valid and vice-versa
      The 3 variables are the zero constant and two arbitrary values which define the atomic predicate for 
      Friedman translation. *)
  Definition F := ∀ ∀ ∀ F_zero → F_succ_left → F_succ_right → translate_constraints h10.

  Section Transport.
    (* The solution to cs *)
    Context (φ: nat -> nat). 
    (* Proof that it actually is a solution *)
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
      (@i_atom _ _ _ I tt (Vector.cons _ i _ (Vector.cons _ i' _ (Vector.nil _)))).
    
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
      eapply (sat_ext I (xi := (fun v : nat => if v <? n then f v else (f n .: r) (v - n))) i).
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

  Lemma transport_direct : H10UPC_SAT h10 -> valid F.
  Proof.
    intros [φ Hφ].
    intros D I rho.
    intros cr1 cr2 zero.
    intros H_zero H_succ_left H_succ_right.
    eapply (@prove_constraints φ Hφ (Build_model H_zero H_succ_left H_succ_right)).
  Qed. 
End validity.


Theorem directValidReduction : reduces (H10UPC_SAT) (@valid sig_empty sig_binary falsity_off).
Proof.
exists (fun l => @F falsity_off l). split.
* apply transport_direct.
* apply inverseTransport.
Qed.

















