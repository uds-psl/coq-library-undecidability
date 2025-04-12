(* * FOL Reductions *)

From Undecidability.DiophantineConstraints Require Import H10C.
From Undecidability.DiophantineConstraints.Util Require Import H10UPC_facts.
From Undecidability.FOL Require Import Utils.FriedmanTranslationFragment Syntax.Facts Deduction.FragmentNDFacts Semantics.Tarski.FragmentSoundness Semantics.Tarski.FragmentFacts Syntax.BinSig Semantics.Kripke.FragmentCore  Semantics.Kripke.FragmentSoundness Semantics.Kripke.FragmentToTarski.
From Undecidability.Shared Require Import Dec.
From Undecidability.Shared.Libs.PSL Require Import Numbers.
From Stdlib Require Import Arith Lia List.
From Undecidability.FOL.Reductions Require Import H10UPC_to_FOL_constructions.

Import FragmentSyntax.


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


Set Default Goal Selector "!".

(* The validity reduction.
    We assume a generic falsity flag and a list h10 for which we build a formula.
 *)
Section Fr_validity.

  Context {ff : falsity_flag}. 
  Context {h10 : list h10upc}.
  Definition F_Fr := Fr (@F ff h10).
  (* We now define our standard model. *)
  Section FrInverseTransport.
    (* An element of the standard model is either a number or a pair. *)
    Inductive dom : Type := Num : nat -> dom | Pair : nat  -> nat -> dom.
    (* The interpretation of our single binary relation *)
    Definition dom_rel' (a : dom) (b:dom) : Prop := match (a,b) with
    | (Num  0, Num  1) => H10UPC_SAT h10
    | (Num n1, Num n2) => n1 = n2
    | (Num n1, Pair x2 _) => n1 = x2
    | (Pair _ y1, Num n2) => n2 = y1
    | (Pair x1 y1, Pair x2 y2) => h10upc_sem_direct ((x1, y1), (x2, y2))
    end.

    Local Instance IB : @interp _ (@extended_preds sig_binary) (dom) | 0.
    Proof using h10.
      split; intros [] v.
      - exact (H10UPC_SAT h10).
      - exact (dom_rel' (Vector.hd v) (Vector.hd (Vector.tl v))).
    Defined.

    (* [DLW] This one is overridden by a new definition, may be change the notation slightly
             would be better? *)
    #[local] Notation "rho ⊨ phi" := (sat rho (Fr phi)) (at level 20).

    (* Now we need rewrite helpers which transform our syntactic sugar into useful statements in the model *)
    Lemma IB_sFalse rho : rho ⊨ (∀ ∀ Pr $0 $1) <-> H10UPC_SAT h10.
    Proof.
    split.
    * intros H. specialize (H (Num 0) (Num 1)). cbn in H. apply H. intros Hf. congruence.
    * intros H d1 d2 Hc. apply H.
    Qed.
    Opaque sFalse.

    Notation dFalse := (H10UPC_SAT h10).
    Notation mDN P := ((P -> dFalse) -> dFalse).
    Notation dom_rel a b := (mDN (dom_rel' a b)).

    Lemma IB_sNot rho f : rho ⊨ (f → sFalse) <-> ((rho ⊨ f) -> H10UPC_SAT h10).
    Proof.
    split.
    * intros H. cbn in H. now rewrite IB_sFalse in H.
    * intros H. cbn. now rewrite IB_sFalse.
    Qed.

    Definition rho_canon' n (rho : nat -> dom) := rho n = Num 0 /\ rho (S n) = Num 0 /\ rho (S (S n)) = Num 1.
    Notation rho_canon rho := (rho_canon' 0 rho).
    Lemma IB_wFalse rho t : rho ⊨ wFalse t <-> dom_rel (rho t) (rho (S t)).
    Proof.
    split.
    * intros H. apply H.
    * intros H. unfold wFalse, Fr. intros P. apply H. apply P.
    Qed.
    Opaque wFalse.

    Lemma IB_dFalse rho t : rho t = Num 0 -> rho (S t) = Num 1 -> rho ⊨ wFalse t <-> dFalse.
    Proof.
    intros H1 H2. rewrite IB_wFalse. rewrite H1,H2. cbn. tauto.
    Qed.
    Opaque wFalse.

    Lemma IB_Not rho f t : rho ⊨ Not f t <-> ((rho ⊨ f) -> rho ⊨ wFalse t).
    Proof.
    split.
    * intros H. cbn in H. now rewrite IB_wFalse in H.
    * intros H. cbn. now rewrite IB_wFalse.
    Qed.
    Opaque Not.

    Lemma IB_F_zero rho : rho_canon rho -> rho ⊨ F_zero.
    Proof.
      intros (H0&H1&H2). cbn. rewrite !H0. tauto.
    Qed.

    Ltac dn := let H := fresh "H" in intros H; apply H.
    Lemma IB_N_e rho i n : rho i = n -> rho ⊨ N i -> mDN {m:nat | Num m = n}.
    Proof.
    intros Hrho H. destruct n as [m|a b].
    * dn. now exists m.
    * intros H1. apply H; cbn -[dom_rel']. intros Hh. apply H1. rewrite Hrho in Hh. exfalso. apply (@h10_rel_irref (a,b) Hh).
    Qed.

    Lemma IB_N_i rho i n : rho i = Num n -> (rho) ⊨ N i.
    Proof. cbn. intros ->. dn. now destruct n as [|n'] eqn:Heq.
    Qed.
    Opaque N.

    Lemma IB_P'_e rho i n : rho i = n -> rho ⊨ P' i -> mDN {a:nat & {b:nat & n = Pair a b}}.
    Proof.
    intros Hrho H. destruct n as [m|a b].
    * unfold P' in H. rewrite IB_sNot in H. intros Hc1. apply H.
      eapply IB_N_i, Hrho.
    * dn. now exists a, b.
    Qed. 

    Lemma IB_P'_i rho i a b : rho i = (Pair a b) -> rho ⊨ P' i.
    Proof.
    unfold P'. rewrite IB_sNot. intros Hrho H. apply (@IB_N_e rho i (Pair a b)). 
    1-2:easy. intros (m & Hm). congruence.
    Qed.
    Opaque P'.

    Lemma IB_P_e rho p l r ip il ir c :
        rho ip = p -> rho il = l -> rho ir = r
     -> rho ⊨ P ip il ir c -> {a:nat & {b:nat & p = Pair a b /\ l = Num a /\ r = Num b}} 
     -> rho ⊨ c.
    Proof.
    intros Hp Hl Hr H [a [b [Hp' [Hl' Hr']]]]. cbn in H. 
    rewrite Hp, Hl, Hr, Hp', Hl', Hr' in H. cbn in H. apply H.
    - eapply IB_P'_i. now rewrite Hp, Hp'.
    - eapply IB_N_i. now rewrite Hl, Hl'.
    - eapply IB_N_i. now rewrite Hr, Hr'.
    - dn. now destruct a.
    - dn. easy.
    Qed.


    Lemma mDN_sat rho phi : mDN (rho ⊨ phi) -> rho ⊨ phi.
    Proof.
      induction phi as [| |?[]|?[]] in rho|-*; cbn -[dom_rel']; intros H.
      - apply H. tauto.
      - intros Hc. apply H. intros Hc2. now apply Hc2.
      - intros H1. apply IHphi2. intros Hc. apply H. intros Hv. apply Hc, Hv, H1.
      - intros d. apply IHphi. intros Hc. apply H. intros Hc2. apply Hc, Hc2.
    Qed.

    Lemma IB_P_i rho ip il ir c : (forall a b, rho ip = (Pair a b) 
                                 -> rho il = (Num a) -> rho ir = (Num b) -> rho ⊨ c)
                                 -> rho ⊨ P ip il ir c.
    Proof.
      intros Hc1 Hc3 Hc4 Hc5 Hpl Hpr.
      apply mDN_sat. intros Hc8.
      unshelve eapply (IB_P'_e (n:=rho ip) _ Hc3); [easy|]. intros [pa [pb Hp]].
      unshelve eapply (IB_N_e (n:=rho il) _ Hc4); [easy|]. intros [la Ha].
      unshelve eapply (IB_N_e (n:=rho ir) _ Hc5); [easy|]. intros [lb Hb].
      apply Hpl; cbn -[dom_rel']; intros Hpl'.
      apply Hpr; cbn -[dom_rel']; intros Hpr'.
      rewrite Hp in *.
      rewrite <-Ha in *.
      rewrite <-Hb in *. unfold dom_rel' in *. 
      apply Hc8. destruct la; eapply (Hc1 pa pb); congruence.
    Qed.
    Opaque P.

    (* We show our model fulfills axiom 1 *)

    Lemma IB_F_succ_left rho : rho_canon rho -> rho ⊨ F_succ_left.
    Proof.
      intros (H0&H1&H2). unfold F_succ_left. intros n Hc1.
      rewrite IB_Not. intros Hc.
      rewrite IB_wFalse; cbn; rewrite H1, H2; intros _.
      eapply (IB_N_e (n:=n) (i:=0) eq_refl Hc1).
      intros [m Hnm]. cbn in Hc.
      specialize (Hc (Pair m 0) (Num (S m)) (Pair (S m) 0)).
      eapply IB_P_e in Hc; cbn. 2-4: reflexivity. 2: eexists; eexists; repeat split; congruence.
      eapply IB_P_e in Hc; cbn. 2-4: reflexivity. 2: eexists; eexists; repeat split; congruence.
      cbn in Hc. rewrite IB_dFalse in Hc. 2-3: cbv; congruence.
      apply Hc. dn. lia.
    Qed.

    (* We show we can extract constraints from our model *)

    Lemma IB_rel_e rho ipl ipr ia ib ic id t : rho ⊨ rel ipl ipr ia ib ic id t 
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
    eapply IB_P_e in H; cbn. 2-4: reflexivity. 2: eexists; eexists; repeat split; eassumption.
    eapply IB_P_e in H; cbn. 2-4: reflexivity. 2: eexists; eexists; repeat split; eassumption.
    cbn in H.
    apply H. dn. rewrite Hpl, Hpr. easy.
    Qed.

    Lemma IB_rel_i rho ipl ipr ia ib ic id t :
                ({a&{b&{c&{d|rho ipl=Pair a b
                            /\ rho ipr = Pair c d
                            /\ rho ia=Num a
                            /\ rho ib=Num b
                            /\ rho ic=Num c
                            /\ rho id=Num d
                            /\ h10upc_sem_direct ((a,b),(c,d))}}}} -> rho ⊨ t)
             -> rho ⊨ rel ipl ipr ia ib ic id t.
    Proof.
    intros H.
    apply IB_P_i.
    intros a b Hpl Ha Hb. apply IB_P_i.
    intros c d Hpr Hc Hd Habcd. cbn -[dom_rel'] in Habcd.
    apply mDN_sat. intros Hc'. apply Habcd. intros Habcd'.
    apply Hc'. apply H. exists a,b,c,d. cbn in Habcd'.
    rewrite Hpl, Hpr in Habcd'. now repeat split.
    Qed.

    (* We show our model fulfills axiom 2 *)

    Lemma IB_F_succ_right rho : rho_canon rho -> rho ⊨ F_succ_right.
    Proof.
      intros (H0&H1&H2). unfold F_succ_right. intros p1 p2 p3 p4 p5 p6 p7 p8 a' y' c b a y x.
      apply IB_rel_i. cbn. intros [nx [ny [na [nb [Hp8 [Hp7 [Hx [Hy [Ha [Hb [Hr1l Hr1r]]]]]]]]]]].
      apply IB_rel_i. cbn. intros [nb' [ny' [nc [nb'' [Hp6 [Hp5 [Hb' [Hy' [Hc [Hb'' [Hr2l Hr2r]]]]]]]]]]].
      apply IB_rel_i. cbn. intros [ny'' [z [n'y [z' [Hp4 [Hp3 [Hy'' [Hz [H'y [Hz' [Hr3l Hr3r]]]]]]]]]]].
      apply IB_rel_i. cbn. intros [na' [z'' [n'a [z''' [Hp2 [Hp1 [Ha' [Hz'' [H'a [Hz''' [Hr4l Hr4r]]]]]]]]]]].
      unfold erel. cbn.
      rewrite IB_Not. intros H.
      rewrite H0 in *. cbn in H.
      specialize (H (Pair n'a (nc)) (Pair nx n'y)).
      eapply IB_P_e in H. 2-4: easy. 2: exists nx, n'y; cbn; firstorder.
      eapply IB_P_e in H. 2-4: easy. 2: exists n'a, nc; cbn; firstorder.
      cbn in H. rewrite IB_wFalse in H. rewrite IB_dFalse. 2-3: cbv; congruence.
      cbn -[dom_rel'] in H.
      assert (z=0 /\ z' = 0 /\ z'' = 0 /\ z''' = 0) as [-> [-> [-> ->]]].
      1:firstorder;congruence.
      assert (ny'' = ny /\ na' = na) as [-> ->].
      1:firstorder;congruence.
      assert (nb' = nb /\ ny' = ny) as [-> ->].
      1:firstorder;congruence.
      subst n'y. subst nc. subst n'a.
      rewrite <- IB_dFalse. 2: apply H1. 2: apply H2. apply IB_wFalse.
      apply H.
      dn. lia.
    Qed.

    (* We show we can encode constraints into our model *)

    (* rho_descr_phi describes that rho is defined by the solution to h10 *)
    Definition rho_descr_phi rho (φ:nat->nat) n :=
         forall k, k < n -> match rho k with Num n => n = (φ k) | _ => True end.
    Lemma IB_single_constr rho φ (n:nat) (h:h10upc) : rho_descr_phi rho φ n 
                                           -> highest_var h < n
                                           -> rho_canon' n rho
                                           -> rho ⊨ translate_single h (S n)
                                           -> (h10upc_sem φ h -> dom_rel (rho (1+n)) (rho (2+n)))
                                           -> dom_rel (rho (1+n)) (rho (2+n)).
    Proof.
      intros Hrhophi Hmaxhall (Hr0&Hr1&Hr2). 
      destruct h as [[a b][c d]]. unfold translate_single. cbn in Hmaxhall.
      intros Htr Hcon Hcon'. unfold erel in Htr. rewrite IB_Not in Htr.
      rewrite IB_dFalse in Htr. 2-3:easy. apply Htr.
      intros p2 p1.
      apply IB_P_i. cbn. intros na nb Hp1 Ha Hb.
      apply IB_P_i. cbn. intros nc nd Hp2 Hc Hd. rewrite Hp1, Hp2.
      intros Habcd.
      rewrite IB_dFalse. 2-3:easy.
      assert (na = φ a) as ->. 1: pose (@Hrhophi a) as Hp; rewrite Ha in Hp; apply Hp; lia.
      assert (nb = φ b) as ->. 1: pose (@Hrhophi b) as Hp; rewrite Hb in Hp; apply Hp; lia.
      assert (nc = φ c) as ->. 1: pose (@Hrhophi c) as Hp; rewrite Hc in Hp; apply Hp; lia.
      assert (nd = φ d) as ->. 1: pose (@Hrhophi d) as Hp; rewrite Hd in Hp; apply Hp; lia.
      apply Habcd. intros Habcd'.
      apply Hcon. 2: apply Hcon'.
      apply Habcd'.
    Qed. 
    (* Helper for working with nested quantifiers *)

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
        eapply (sat_ext IB (xi:=fun k => if k <? S n
                                         then (fun kk => if kk =? n then d
                                         else f kk) k else (rho) (k - S n))).
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
    (* Final utility lemma: translate the entire list of constraints *)

    Lemma IB_translate_rec rho phi f e hv : rho_descr_phi rho phi hv 
                            -> rho_canon' hv rho
                            -> (rho ⊨ f <-> dom_rel (rho (1+hv)) (rho (2+hv)))
                            -> highest_var_list e < hv 
                            -> ((forall c, In c e -> h10upc_sem phi c) -> rho ⊨ f)
                            -> rho ⊨ translate_rec f (S hv) e.
    Proof.
    intros Hrhophi (Hr0&Hr1&Hr2) Hsat Hhv H.
    induction e as [|eh er IH] in H,Hsat,Hhv|-*.
    - apply H. intros l [].
    - cbn. intros Hts. apply IH.
      + easy.
      + cbn in Hhv. lia.
      + intros HH. rewrite Hsat. eapply (IB_single_constr (h:=eh)).
        * exact Hrhophi.
        * pose proof (@highest_var_list_descr (eh::er) eh ltac:(now left)). lia.
        * easy.
        * easy.
        * intros Hsem. rewrite <- Hsat. apply H. intros c [il|ir]. 2:now apply HH. congruence.
    Qed.
    (* We can now extract the constraints from our translate_constraints function*)

    Lemma less_ge a b : a >= b -> a <? b = false.
    Proof.
      intros H. rewrite Nat.ltb_nlt. lia. 
    Qed.

    Lemma IB_aux_transport rho : rho_canon rho
                              -> rho ⊨ translate_constraints h10
                              -> H10UPC_SAT h10.
    Proof.
      intros (Hrho0&Hrho1&Hrho2).
      pose ((S (highest_var_list h10))) as h10vars. 
      unfold translate_constraints. fold h10vars. intros H.
      cbn in H. rewrite Hrho1, Hrho2 in H.
      apply H. 2:easy. 
      apply IB_emplace_forall. intros f.
      pose (fun n => match (f n) with (Num k) => k | _ => 0 end) as phi.
      eapply (IB_translate_rec (e:=h10) (hv:=h10vars) (phi:= phi)).
      - intros x HH. destruct (Nat.ltb_lt x h10vars) as [_ Hr]. rewrite Hr. 2:easy.
        unfold phi. now destruct (f x).
      - split. 2:split. all: rewrite less_ge; [|lia].
        1: rewrite <- Hrho0. 2: rewrite <- Hrho1. 3: rewrite <- Hrho2. all: f_equal; lia.
      - cbn -[dom_rel' Nat.leb Nat.sub]. easy.
      - lia.
      - intros HG. cbn -[dom_rel' Nat.leb Nat.sub].
        destruct (Nat.ltb_ge (S h10vars) h10vars) as [_ H1]. rewrite H1. 2:lia.
        destruct (Nat.ltb_ge (S (S h10vars)) h10vars) as [_ H2]. rewrite H2. 2:lia.
        assert (S h10vars-h10vars = 1) as ->. 1:lia. 
        assert (S(S h10vars)-h10vars = 2) as ->. 1:lia.
        rewrite Hrho1, Hrho2. cbn. exists phi. easy.
    Qed.

    (* To conclude, we can wrap the axioms around it.*)
    Lemma IB_fulfills rho : rho ⊨ (@F ff h10) -> H10UPC_SAT h10.
    Proof.
      intros H. unfold F in H. pose (Num 0 .: Num 0 .: Num 1 .: rho) as nrho.
      assert (rho_canon nrho) as nrho_canon.
      1: split; easy.
      apply (@IB_aux_transport nrho), H. 
      - easy.
      - now apply IB_F_zero.
      - now apply IB_F_succ_left.
      - now apply IB_F_succ_right.
    Qed.
  End FrInverseTransport.

  (* If F is valid, h10 has a solution: *)
  Lemma FrInverseTransport : valid (Fr (@F ff h10)) -> H10UPC_SAT h10.
  Proof.
    intros H. apply (@IB_fulfills (fun b => Num 0)). apply H.
  Qed.

End Fr_validity.


(* We also have classical provability, assuming LEM *)
Section classical_provability.
  Context {ff : falsity_flag}. 
  Context {h10 : list h10upc}.

  Lemma classicalProvabilityTransport : H10UPC_SAT h10 -> nil ⊢C F (h10:=h10).
  Proof.
  intros [φ Hφ]. apply intuitionistic_is_classical. eapply transport_prove. exact Hφ.
  Qed.

  Lemma classicalProvabilityInverseTransport : nil ⊢C F (h10:=h10) -> H10UPC_SAT h10.
  Proof.
  intros H%(Fr_cl_to_min)%soundness. apply FrInverseTransport. intros D I rho.
  apply H. easy.
  Qed.
End classical_provability.
