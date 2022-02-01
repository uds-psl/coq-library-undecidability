(* * FOL Reductions *)

From Undecidability.DiophantineConstraints Require Import H10C.
From Undecidability.DiophantineConstraints.Util Require Import H10UPC_facts.
From Undecidability.FOL Require Import Util.Syntax Util.FullTarski Util.FullTarski_facts Util.Syntax_facts Util.sig_bin.
From Undecidability.Shared Require Import Dec.
From Undecidability.Shared.Libs.PSL Require Import Numbers.
From Coq Require Import Arith Lia List.
Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.


(* ** Validity *)

(**
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

(** Some utils for iteration *)
Section Utils.

  Lemma it_shift (X:Type) (f:X->X) v n : it f (S n) v = it f n (f v).
  Proof.
  induction n as [|n IH].
  - easy.
  - cbn. f_equal. apply IH.
  Qed.

End Utils.
(** The validity reduction.
    We assume a list h10 for which we build a formula.
 *)

Section validity.

  Context {h10 : list h10upc}.
  Existing Instance falsity_on.
  Definition Pr (t t':term) := (@atom _ sig_binary _ _ tt (Vector.cons _ t _ (Vector.cons _ t' _ (Vector.nil _)))).

  (** #&dollar;#k is a number *)
  Definition N k := Pr $k $k.
  (** #&dollar;#k is a pair *)
  Definition P' k := ¬ (N k).
  (** If #&dollar;#k is a pair ($l,$r), where $l, $r are numbers, then t. *)
  Definition P k l r:= P' k ∧ N l ∧ N r ∧ Pr $l $k ∧ Pr $k $r.
  (** The pairs #&dollar;#pl = (#&dollar;#a,#&dollar;#b), #&dollar;#pr = (#&dollar;#c,#&dollar;#d) are in relation *)
  Definition rel pl pr a b c d := P pl a b ∧ P pr c d ∧ Pr $pl $pr.
  (** There exist  pairs relating (#&dollar;#a,#&dollar;#b) to (#&dollar;#c,#&dollar;#d) *)
  Definition erel a b c d := ∃ ∃ rel 0 1 (2+a) (2+b) (2+c) (2+d). 
  (** Axiom 1 - zero is a number *)
  Definition F_zero := N 0.
  (** Axiom 2 - we can build (left) successors: for each pair (a,0) we have a pair (S a, 0) *)
  Definition F_succ_left := ∀ N 0 ~> ∃ ∃ ∃ P 2 3 4 ∧ P 0 1 4 ∧ Pr $2 $0.
  (** Axiom 3 - we can build right successors: (x,y)#&#35;#(a,b) -> (x,S y)#&#35;#(S a,S (b+y)) *)
  Definition F_succ_right := ∀ ∀ ∀ ∀ ∀ ∀ ∀           (* 0 x 1 y 2 a 3 b 4 c 5 y' 6 a' 7 zero-const*)
                             erel 0 1 2 3 ~>         (* (x,y) # (a,b) *)
                            (erel 3 1 4 3 ~>         (* (b,y) # (c,b) *)
                            (erel 1 7 5 7 ~>       (* (y,0) # (y',0) *)
                            (erel 2 7 6 7 ~>       (* (a,0) # (a',0) *)
                            (erel 0 5 6 4))))     (* (x,y') # (a',c) *).
  (** Generate n all quantifiers around i *)
  Definition emplace_exists (n:nat) (i:form) := it (fun k => ∃ k) n i.

  (** Translate our formula, one relation at a time *) 
  Definition translate_single (h:h10upc) (nv:nat) := 
          match h with ((a,b),(c,d)) => 
            erel a b c d end.
  (** Translate an entire instance of H10UPC, assuming a proper context *)
  Fixpoint translate_rec (t:form) (nv:nat) (l:list h10upc) := 
          match l with nil => t
                     | l::lr => translate_single l nv ∧ translate_rec t nv lr end.
  (** Actually translate the instance of H10UPC, by creating a proper context *)
  Definition translate_constraints (x:list h10upc) := 
    let nv := S (highest_var_list x)
    in (emplace_exists nv (translate_rec (¬ ⊥) (S nv) x)).

  (** The actual reduction instance. If h10 is a yes-instance of H10UPC, this formula is valid and vice-versa
      The 3 variables are the zero constant and two arbitrary values which define the atomic predicate for 
      Friedman translation. *)
  Definition F := ∀ F_zero ~> F_succ_left ~> F_succ_right ~> translate_constraints h10.
  (** We now define our standard model. *)
  Section InverseTransport.
    (** An element of the standard model is either a number or a pair. *)
    Inductive dom : Type := Num : nat -> dom | Pair : nat  -> nat -> dom.
    (** The interpretation of our single binary relation *)
    Definition dom_rel (a : dom) (b:dom) : Prop := match (a,b) with
    | (Num n1, Num n2) => n1 = n2
    | (Num n1, Pair x2 _) => n1 = x2
    | (Pair _ y1, Num n2) => n2 = y1
    | (Pair x1 y1, Pair x2 y2) => h10upc_sem_direct ((x1, y1), (x2, y2))
    end.

    Global Instance IB : interp (dom).
    Proof using h10.
      split; intros [] v.
      exact (dom_rel (Vector.hd v) (Vector.hd (Vector.tl v))).
    Defined.

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
    Proof. cbn. intros ->. now destruct n as [|n'] eqn:Heq.
    Qed.
    Opaque N.

    Lemma IB_P'_e rho i n : rho i = n -> rho ⊨ P' i -> {a:nat & {b:nat & n = Pair a b}}.
    Proof.
    intros Hrho H. destruct n as [m|a b].
    * exfalso. unfold P' in H. eapply H, IB_N_i, Hrho.
    * now exists a, b.
    Qed.

    Lemma IB_P'_i rho i a b : rho i = (Pair a b) -> rho ⊨ P' i.
    Proof.
    unfold P'. intros Hrho H. destruct (@IB_N_e rho i (Pair a b)). 
    1-2:easy. congruence.
    Qed.
    Opaque P'.

    Lemma IB_P_e rho p l r ip il ir :
        rho ip = p -> rho il = l -> rho ir = r
     -> rho ⊨ P ip il ir -> {a:nat & {b:nat & p = Pair a b /\ l = Num a /\ r = Num b}}.
    Proof.
    intros Hp Hl Hr [[[[(a&b&->)%(IB_P'_e Hp) (nl&<-)%(IB_N_e Hl)] (nr&<-)%(IB_N_e Hr)] HP4] HP5].
    exists a, b; repeat split.
    - cbn in HP4. rewrite Hl,Hp in HP4. now rewrite HP4.
    - cbn in HP5. rewrite Hr,Hp in HP5. now rewrite HP5.
    Qed.

    Lemma IB_P_i rho ip il ir l r : rho ip = Pair l r -> rho il = Num l -> rho ir = Num r -> rho ⊨ P ip il ir.
    Proof.
    cbn. intros Hp Hl Hr. rewrite !Hp, !Hl, !Hr. repeat split.
    - eapply IB_P'_i. exact Hp.
    - eapply IB_N_i. exact Hl.
    - eapply IB_N_i. exact Hr.
    Qed.
    Opaque P.

    (** We show our model fulfills axiom 1 *)

    Lemma IB_F_succ_left rho : rho_canon rho -> rho ⊨ F_succ_left.
    Proof.
      intros H0. unfold F_succ_left. intros n [m Hnm]%(IB_N_e (n:=n)). 2:easy.
      exists (Pair m 0), (Num (S m)), (Pair (S m) 0). cbn. split. 2:lia. split.
      - eapply IB_P_i; cbn; try reflexivity. 1: congruence. apply H0.
      - eapply IB_P_i; cbn; try reflexivity. apply H0.
    Qed.

    (** We show we can extract constraints from our model *)

    Lemma IB_rel_e rho ipl ipr ia ib ic id : rho ⊨ rel ipl ipr ia ib ic id
                -> {a&{b&{c&{d|rho ipl=Pair a b
                            /\ rho ipr=Pair c d
                            /\ rho ia=Num a
                            /\ rho ib=Num b
                            /\ rho ic=Num c
                            /\ rho id=Num d
                            /\ h10upc_sem_direct ((a,b),(c,d))}}}}.
    Proof.
    intros [[H1 H2] H3]. eapply IB_P_e in H1, H2. 2-7: reflexivity.
    destruct H1 as (a&b&Hpl&Ha&Hb), H2 as (c&d&Hpr&Hc&Hd).
    exists a, b, c, d; repeat split; try easy.
    all: cbn in H3; rewrite Hpl, Hpr in H3; lia.
    Qed.

    Lemma IB_rel_i rho ipl ipr ia ib ic id a b c d : 
               rho ipl=Pair a b
            -> rho ipr=Pair c d
            -> rho ia=Num a
            -> rho ib=Num b
            -> rho ic=Num c
            -> rho id=Num d
            -> h10upc_sem_direct ((a,b),(c,d))
            -> rho ⊨ rel ipl ipr ia ib ic id.
    Proof.
    intros Hpl Hpr Ha Hb Hc Hd Habcd. split. 1:split.
    - eapply IB_P_i; eauto.
    - eapply IB_P_i; eauto.
    - cbn. rewrite Hpl, Hpr. apply Habcd.
    Qed.
    Opaque rel.



    Lemma IB_erel_e rho ia ib ic id : rho ⊨ erel ia ib ic id
                -> exists a b c d, rho ia=Num a
                                /\ rho ib=Num b
                                /\ rho ic=Num c
                                /\ rho id=Num d
                                /\ h10upc_sem_direct ((a,b),(c,d)).
    Proof.
    intros [pl [pr H]]. eapply IB_rel_e in H. destruct H as (a&b&c&d&Hpl&Hpr&Ha&Hb&Hc&Hd&Habcd1&Habcd2).
    exists a, b, c, d; now repeat split.
    Qed.

    Lemma IB_erel_i rho ia ib ic id a b c d : 
               rho ia=Num a
            -> rho ib=Num b
            -> rho ic=Num c
            -> rho id=Num d
            -> h10upc_sem_direct ((a,b),(c,d))
            -> rho ⊨ erel ia ib ic id.
    Proof.
    intros Ha Hb Hc Hd Habcd. exists (Pair c d), (Pair a b). eapply IB_rel_i. 1-2: reflexivity. all: easy. 
    Qed.
    Opaque erel.

    Ltac set_eq a b := assert (a = b) as -> by congruence.

    (** We show our model fulfills axiom 2 *)

    Lemma IB_F_succ_right rho : rho_canon rho -> rho ⊨ F_succ_right.
    Proof.
      intros H0. unfold F_succ_right. intros a' y' c b a y x Hr1 Hr2 Hr3 Hr4.
      eapply IB_erel_e in Hr1, Hr2, Hr3, Hr4.
      cbn in Hr1,Hr2,Hr3,Hr4.
      destruct Hr1 as (x_1&y_1&a_1&b_1&He11&He12&He13&He14&Hr1').
      destruct Hr2 as (b_2&y_2&c_1&b_3&He21&He22&He23&He24&Hr2').
      destruct Hr3 as (y_3&v0_1&y'_1&v0_2&He31&He32&He33&He34&Hr3').
      destruct Hr4 as (a_2&v0_3&a'_1&v0_4&He41&He42&He43&He44&Hr4').
      rewrite H0 in He32,He34,He42,He44.
      set_eq v0_1 0. set_eq v0_2 0. set_eq v0_3 0. set_eq v0_4 0.
      set_eq a_2 a_1. set_eq b_2 b_1. set_eq b_3 b_1. set_eq y_2 y_1. set_eq y_3 y_1.
      eapply IB_erel_i; cbn. 1-4:eauto. lia.
    Qed.

    (** We show we can encode constraints into our model *)

    (** rho_descr_phi describes that rho is defined by the solution to h10 *)
    Definition rho_descr_phi rho (φ:nat->nat) n :=
         forall k, k < n -> match rho k with Num n => n = (φ k) | _ => True end.
    Lemma IB_single_constr rho φ (n:nat) (h:h10upc) : rho_descr_phi rho φ n 
                                           -> highest_var h < n
                                           -> rho ⊨ translate_single h (S n)
                                           -> h10upc_sem φ h.
    Proof.
      intros Hrhophi Hmaxhall. 
      destruct h as [[a b][c d]]. unfold translate_single. cbn in Hmaxhall.
      intros (na&nb&nc&nd&Ha&Hb&Hc&Hd&Habcd)%IB_erel_e.
      unfold h10upc_sem.
      pose proof (Hrhophi a (ltac:(lia))) as Hpa. rewrite Ha in Hpa.
      pose proof (Hrhophi b (ltac:(lia))) as Hpb. rewrite Hb in Hpb.
      pose proof (Hrhophi c (ltac:(lia))) as Hpc. rewrite Hc in Hpc.
      pose proof (Hrhophi d (ltac:(lia))) as Hpd. rewrite Hd in Hpd.
      now rewrite <- Hpa, <- Hpb, <- Hpc, <- Hpd.
    Qed. 
    (** Helper for working with nested quantifiers *)

    Lemma IB_emplace_exists rho n i : 
        rho ⊨ emplace_exists n i
        -> (exists f, (fun k => if k <? n then f (k) else rho (k-n)) ⊨ i).
    Proof. 
      unfold emplace_exists. intros H.
      induction n as [|n IH] in rho,H|-*.
      - cbn. exists (fun _ => Num 0). eapply (sat_ext IB (rho:=rho) (xi:=fun k => rho(k-0))).
        2: easy.
        intros x. now rewrite Nat.sub_0_r.
      - cbn in H. destruct H as (d&Hd).
        specialize (IH (d.:rho) Hd). destruct IH as [f Hf].
        exists (fun kk => if kk =? n then d else f kk).
        eapply (sat_ext IB (xi:=fun k => if k <? n then f k else (d .: rho) (k - n))).
        2: easy.
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
    Opaque emplace_exists. 

    (** Final utility lemma: translate the entire list of constraints *)
    Lemma IB_translate_rec rho phi f e hv : rho_descr_phi rho phi hv 
                            -> highest_var_list e < hv 
                            -> rho ⊨ translate_rec f (S hv) e
                            -> (forall c, In c e -> h10upc_sem phi c) /\ rho ⊨ f.
    Proof.
    intros Hrhophi Hhv H.
    induction e as [|eh er IH] in H,Hhv|-*.
    - split. 1: intros c []. easy.
    - cbn. cbn in H, Hhv. destruct IH as [IH1 IH2]. 1:lia. 1:apply H.
      split. 2:easy. intros c [->|Her].
      + eapply (IB_single_constr Hrhophi). 1:lia. apply H. 
      + now apply IH1.
    Qed.
    (** We can now extract the constraints from our translate_constraints function*)

    Lemma IB_aux_transport rho : rho 0 = Num 0
                              -> rho ⊨ translate_constraints h10
                              -> H10UPC_SAT h10.
    Proof.
      intros Hrho0.
      pose ((S (highest_var_list h10))) as h10vars. 
      unfold translate_constraints. fold h10vars. intros H.
      apply IB_emplace_exists in H. destruct H as [f Hf].
      pose (fun n => match (f n) with (Num k) => k | _ => 0 end) as phi.
      exists phi.
      unshelve eapply (IB_translate_rec (e:=h10) (hv:=h10vars) (phi:= phi) _ _ Hf).
      - intros x HH. destruct (Nat.ltb_lt x h10vars) as [_ Hr]. rewrite Hr. 2:easy.
        unfold phi. now destruct (f x).
      - lia.
    Qed.

    (** To conclude, we can wrap the axioms around it.*)
    Lemma IB_fulfills rho : rho ⊨ F -> H10UPC_SAT h10.
    Proof.
      intros H. unfold F in H. pose (Num 0 .: rho) as nrho.
      assert (rho_canon nrho) as nrho_canon.
      1: split; easy.
      apply (@IB_aux_transport nrho), H; fold sat. 
      - easy.
      - now apply IB_F_zero.
      - now apply IB_F_succ_left.
      - now apply IB_F_succ_right.
    Qed.
  End InverseTransport.

  (** If F is valid, h10 has a solution: *)
  Lemma inverseTransport : valid F -> H10UPC_SAT h10.
  Proof.
    intros H. apply (@IB_fulfills (fun b => Num 0)). apply H.
  Qed.

  Section Transport.
    Context (D:Type).
    Context (I:interp D).
    Existing Instance I.

    Definition iPr (d1 d2 : D) : Prop := (@i_atom _ sig_binary _ _ tt (Vector.cons _ d1 _ (Vector.cons _ d2 _ (Vector.nil _)))).
    Lemma iPr_spec rho' t t' d1 d2 : rho' t = d1 -> rho' t' = d2 -> rho' ⊨ Pr $t $t' <-> iPr d1 d2.
    Proof. cbn. intros -> ->. easy. Qed.

    Definition iN d := iPr d d.
    Lemma iN_spec rho' t d : rho' t = d -> rho' ⊨ N t <-> iN d.
    Proof. unfold N,iN. intros H. now rewrite iPr_spec. Qed.
    
    Definition iP' d := ~ (iN d).
    Lemma iP'_spec rho' t d : rho' t = d -> rho' ⊨ P' t <-> iP' d.
    Proof. unfold P',iP'. intros H. cbn [sat]. unfold not. erewrite iN_spec. 1:easy. easy. Qed.

    Definition iP k l r:= (((iP' k /\ iN l) /\ iN r) /\ iPr l k) /\ iPr k r.
    Lemma iP_spec rho' k l r dk dl dr : rho' k = dk -> rho' l = dl -> rho' r = dr -> rho' ⊨ P k l r <-> iP dk dl dr.
    Proof. intros H1 H2 H3. unfold P,iP. erewrite <- !iPr_spec, <- !iN_spec, <- iP'_spec. 1:cbn;reflexivity. all:easy. Qed.

    Definition ierel a b c d := exists d1 d0, (iP d0 a b /\ iP d1 c d) /\ iPr d0 d1.
    Lemma ierel_spec rho' a b c d da db dc dd : rho' a = da -> rho' b = db -> rho' c = dc -> rho' d = dd -> rho' ⊨ erel a b c d <-> ierel da db dc dd.
    Proof. intros H1 H2 H3 H4. unfold erel,rel,ierel. split.
    - intros [d1 [d0 H]]. exists d1,d0. rewrite <- !iPr_spec, <- !iP_spec. 1:apply H. all:easy.
    - intros [d1 [d0 H]]. exists d1,d0. rewrite <- !iPr_spec, <- !iP_spec in H. 1:apply H. all:easy.
    Qed.
    Lemma ierel_spec' rho' a b c d : rho' ⊨ erel a b c d <-> ierel (rho' a) (rho' b) (rho' c) (rho' d).
    Proof. now apply ierel_spec. Qed.

    Section withAxioms.
      Context (rho:env D).
      Context (φ:nat->nat).
      Context (Hφ : forall c, In c h10 -> h10upc_sem φ c). 
      Context (HA1 : rho ⊨ F_zero).
      Context (HA2 : rho ⊨ F_succ_left).
      Context (HA3 : rho ⊨ F_succ_right).
      
      Record chain (n:nat) := {
        f :> nat -> D;
        chain_zero : f 0 = rho 0;
        chain_succ : forall m, m < n -> ierel (f m) (f 0) (f (S m)) (f 0)
      }.

      Lemma chain_N n (c:chain n) m : m <= n -> iN (c m).
      Proof using HA1.
      intros Hm. destruct m.
      - rewrite (chain_zero c). apply HA1.
      - destruct (chain_succ c Hm) as [d1 [d0 [[_ H] _]]]. unfold iP in H. apply H.
      Qed.

      Lemma chain_build n : inhabited (chain n).
      Proof using HA1 HA2.
      induction n as [|n [c]].
      - apply inhabits. split with (fun _ => rho 0).
        + easy.
        + intros m H. exfalso; lia.
      - cbn -[N P Pr] in HA2.
        destruct (@HA2 (c n)) as [pl [d [pr [[H1 H2] H3]]]].
        1: { rewrite ! iN_spec. 2:cbn; reflexivity. apply chain_N. easy. }
        rewrite !iP_spec in H1,H2. 1:rewrite !iPr_spec in H3. 2-9: cbn; easy.
        apply inhabits. pose (fun m => if m =? S n then d else c m) as f. split with f.
        + unfold f. destruct (Nat.eqb_neq 0 (S n)) as [_ ->]. 2:lia. apply chain_zero.
        + unfold f. destruct (Nat.eqb_neq 0 (S n)) as [_ ->]. 2:lia. 
          intros m Hm. destruct (Nat.eqb_neq m (S n)) as [_ ->]. 2:lia.
          destruct (S m=?S n) eqn:Heq.
          * apply beq_nat_true in Heq. assert (m=n) as -> by lia. exists pr, pl. rewrite chain_zero. split. 1:split. all:easy.
          * apply chain_succ. apply beq_nat_false in Heq. lia.
      Qed.

      Ltac h10ind_not_lt_0 := match goal with [H : h10upc_ind ?k 0 0 0 |- _] => exfalso; now apply (@h10upc_ind_not_less_0 k H) end.

      Lemma chain_proves a b c d n (f:chain n) :
               h10upc_sem_direct ((a,b),(c,d))
            -> a < n -> b < n -> c < n -> d < n
            -> ierel (f a) (f b) (f c) (f d).
      Proof using HA3.
      rewrite h10_equiv.
      intros k; remember k as Habcd eqn:Heq; clear Heq; revert k.
      induction 1 as [a|a b c d b' c' d' H1 IH1 H2 IH2 H3 IH3 H4 IH4]; intros Ha Hb Hc Hd.
      - apply chain_succ. easy.
      - cbn -[erel] in HA3. specialize (@HA3 (f c) (f b) (f d) (f d') (f c') (f b') (f a)).
        rewrite !ierel_spec' in HA3. cbn in HA3.
        rewrite !chain_zero in *.
        assert (0 < n) as H0n by lia.
        assert (b' < n) as Hbn by (inversion H3; [lia | h10ind_not_lt_0]).
        assert (c' < n) as Hcn by (inversion H4; [lia | h10ind_not_lt_0]).
        assert (d' < n) as Hdn by (rewrite <- h10_equiv in H2; cbn in H2; lia).
        apply HA3; eauto.
      Qed.

      Definition rho_descr_chain rho phi n (c:chain n) hv :=
         forall k, k < hv -> rho k = c (phi k).

      Lemma translate_rec_correct hv hn (cc:chain hn) (h:list h10upc) phi f rho' : 
               rho' ⊨ f
            -> (forall k, In k h -> h10upc_sem phi k)
            -> highest_var_list h < hv
            -> highest_num phi hv < hn
            -> rho_descr_chain rho' phi cc hv
            -> rho' ⊨ translate_rec f (S hv) h.
      Proof using D HA3 I rho.
      intros Hf Hsat Hhv Hhn Hc. induction h as [|[[a b][c d]] hr IH] in Hhv,Hsat|-*.
      - cbn. easy.
      - cbn -[erel]. cbn in Hhv. split.
        + rewrite ierel_spec. 2-5:rewrite Hc; [easy|lia].
          apply chain_proves. 1: eapply (Hsat ((a,b),(c,d))); now left.
          all: match goal with |- ?phi ?a < ?hn => enough (phi a <= highest_num phi hv) by lia end.
          all: apply highest_num_descr. all:lia.
        + apply IH.
          * intros x Hx. apply Hsat. now right.
          * lia.
      Qed.

      Lemma emplace_exists_spec rho' n i : 
        (exists f, (fun k => if k <? n then f (k) else rho' (k-n)) ⊨ i)
        -> rho' ⊨ emplace_exists n i.
      Proof.
      intros [f Hf]. unfold emplace_exists.
      induction n as [|n IH] in rho',f,Hf|-*.
      - cbn. eapply sat_ext. 2:exact Hf. intros x. cbn. now rewrite Nat.sub_0_r.
      - cbn. exists (f n). eapply sat_ext. 2:apply (IH (f n .: rho') f).
        + intros x. easy.
        + eapply sat_ext. 2:apply Hf. intros x. cbv beta.
          destruct (x <? n) eqn:Heq, (x <? S n) eqn:HSeq.
          * easy.
          * exfalso. rewrite Nat.ltb_lt in Heq. rewrite Nat.ltb_ge in HSeq. lia.
          * rewrite Nat.ltb_ge in Heq. rewrite Nat.ltb_lt in HSeq. assert (x = n) as -> by lia. rewrite Nat.sub_diag. easy.
          * rewrite Nat.ltb_ge in Heq. rewrite Nat.ltb_ge in HSeq. assert (x-n=S(x-S n)) as -> by lia. cbn. easy.
      Qed.

      Lemma translate_constraints_correct : 
            rho ⊨ translate_constraints (h10).
      Proof using D HA1 HA2 HA3 Hφ I h10 rho φ.
      unfold translate_constraints.
      pose (S(highest_var_list h10)) as hv. fold hv.
      pose (S(highest_num φ hv)) as hn.
      destruct (chain_build hn) as [c].
      apply emplace_exists_spec.
      exists (φ >> c).
      eapply (@translate_rec_correct hv hn c _  φ _ _).
      - cbn. easy.
      - exact Hφ.
      - unfold hv. lia.
      - unfold hn. lia.
      - intros m Hm. destruct (m <? hv) eqn:Heq.
        + easy.
        + apply Nat.ltb_ge in Heq. lia.
      Qed.
    End withAxioms.
    (** To conclude, we can wrap the axioms around it.*)
    Lemma F_correct rho : H10UPC_SAT h10 -> rho ⊨ F.
    Proof.
      intros [φ Hφ] z HA1 HA2 HA3. eapply translate_constraints_correct.
      - exact Hφ.
      - exact HA1.
      - exact HA2.
      - exact HA3.
    Qed.
  End Transport.

  (** If h10 has a solution, F is valid: *)
  Lemma transport : H10UPC_SAT h10 -> valid F.
  Proof.
    intros H M I rho. now apply F_correct. 
  Qed.


  (** sat things *)
  Lemma sat1 : (complement satis (¬ F)) -> complement (complement H10UPC_SAT) h10.
  Proof.
    intros Hc1 Hc2. apply Hc1. exists dom, IB, (fun b => Num 0). intros H.
    apply Hc2. eapply IB_fulfills. exact H.
  Qed.
  Lemma sat2 : complement (complement H10UPC_SAT) h10 -> (complement satis (¬ F)).
  Proof.
    intros Hc1 [D [I [rho H]]]. apply Hc1. intros Hh10.
    apply H. fold sat. eapply F_correct. exact Hh10.
  Qed.

  (** sat things 2 *)
  Lemma sat3 : (complement (complement satis) (¬ F)) -> complement H10UPC_SAT h10.
  Proof.
    intros Hc1 Hc2. apply Hc1.
    intros [D [I [rho H]]]. apply H. fold sat.
    apply F_correct. easy.
  Qed.
  Lemma sat4 : complement H10UPC_SAT h10 -> (complement (complement satis) (¬ F)).
  Proof.
    intros Hc1 Hc2. apply Hc2. exists dom, IB, (fun b => Num 0). intros H.
    apply Hc1. eapply IB_fulfills. exact H.
  Qed.

  (** sat things 3 *)
  Lemma sat5 : satis (¬ F) -> complement H10UPC_SAT h10.
  Proof.
    intros [D [I [rho H]]] Hc. apply H. fold sat.
    apply F_correct. easy.
  Qed.
  Lemma sat6 : complement H10UPC_SAT h10 -> satis (¬ F).
  Proof.
    intros Hc1. exists dom, IB, (fun b => Num 0). intros H.
    apply Hc1. eapply IB_fulfills. exact H.
  Qed.

End validity.


Lemma fullFragValidReduction : H10UPC_SAT ⪯ (valid (ff := falsity_on)).
Proof.
exists @F. split.
- apply transport.
- apply inverseTransport.
Qed.


Lemma fullFragSatisReduction : complement H10UPC_SAT ⪯ (satis (ff := falsity_on)).
Proof.
exists (fun k => ¬ (@F k)). split.
- intros H. eapply sat6. easy.
- intros H. eapply sat5. easy.
Qed.



