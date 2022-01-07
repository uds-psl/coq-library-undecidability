(* * FOL Reductions *)

From Undecidability.DiophantineConstraints Require Import H10C.
From Undecidability.DiophantineConstraints.Util Require Import H10UPC_facts.
From Undecidability.FOL Require Import Util.Syntax Util.Kripke Util.Deduction Util.Tarski Util.Syntax_facts Util.sig_bin.
From Undecidability.Shared Require Import Dec.
From Undecidability.Shared.Libs.PSL Require Import Numbers.
From Coq Require Import Arith Lia List.


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


Notation Pr t t' := (@atom _ sig_binary _ _ tt (Vector.cons _ t _ (Vector.cons _ t' _ (Vector.nil _)))).

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
    We assume a generic falsity flag and a list h10 for which we build a formula.
 *)
Section validity.

  Context {ff : falsity_flag}. 
  Context {h10 : list h10upc}.
  (** All are placed in a context where #&dollar;#0 is the 0 constant and #&dollar;#1, #&dollar;#2 are arbitrary but fixed. *)
  (** We do a Friedman translation, where this represents falsity. *)
  Definition wFalse t:= Pr $t $(S t).
  (** We use a stronger version of falsity, which is <-> False in our standart model, to ease writing eliminators. *)
  Definition sFalse := ∀ ∀ Pr $0 $1.
  (** Friedman not *)
  Definition Not k t := k --> wFalse t.
  (** #&dollar;#k is a number *)
  Definition N k := Pr $k $k.
  (** #&dollar;#k is a pair *)
  Definition P' k := (N k) --> sFalse.
  (** If #&dollar;#k is a pair ($l,$r), where $l, $r are numbers, then t. *)
  Definition P k l r c := P' k --> N l --> N r --> Pr $l $k --> Pr $k $r --> c.
  (** if the pairs #&dollar;#pl = (#&dollar;#a,#&dollar;#b), #&dollar;#pr = (#&dollar;#c,#&dollar;#d) are in relation, then t *)
  Definition rel pl pr a b c d t := P pl a b (P pr c d (Pr $pl $pr --> t)).
  (** There exist (Friedman translated) pairs relating (#&dollar;#a,#&dollar;#b) to (#&dollar;#c,#&dollar;#d) *)
  Definition erel a b c d t := Not (∀ ∀ P 0 (2+a) (2+b) 
                                        (P 1 (2+c) (2+d)  
                                         (Pr $0 $1 --> wFalse (2+t)))) t. 
  (** Axiom 1 - zero is a number *)
  Definition F_zero := N 0.
  (** Axiom 2 - we can build (left) successors: for each pair (a,0) we have a pair (S a, 0) *)
  Definition F_succ_left := ∀ N 0 --> Not (∀ ∀ ∀ P 2 3 4
                                                 (P 0 1 4
                                                  (Pr $2 $0 --> wFalse 5))) 2.
  (** Axiom 3 - we can build right successors: (x,y)#&#35;#(a,b) -> (x,S y)#&#35;#(S a,S (b+y)) *)
  Definition F_succ_right := ∀ ∀ ∀ ∀ ∀ ∀ ∀ ∀         (*8 pairs *)
                             ∀ ∀ ∀ ∀ ∀ ∀ ∀           (* 0 x 1 y 2 a 3 b 4 c 5 y' 6 a' 15 zero-const*)
                             rel 7 8 0 1 2 3      (* (x,y) # (a,b) *)
                            (rel 9 10 3 1 4 3     (* (b,y) # (c,b) *)
                            (rel 11 12 1 15 5 15  (* (y,0) # (y',0) *)
                            (rel 13 14 2 15 6 15  (* (a,0) # (a',0) *)
                            (erel 0 5 6 4 16))))     (* (x,y') # (a',c) *).
  (** Generate n all quantifiers around i *)
  Definition emplace_forall (n:nat) (i:form) := it (fun k => ∀ k) n i.

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
  (** We now define our standard model. *)
  Section InverseTransport.
    (** An element of the standard model is either a number or a pair. *)
    Inductive dom : Type := Num : nat -> dom | Pair : nat  -> nat -> dom.
    (** The interpretation of our single binary relation *)
    Definition dom_rel (a : dom) (b:dom) : Prop := match (a,b) with
    | (Num  0, Num  1) => H10UPC_SAT h10
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

    (** Now we need rewrite helpers which transform our syntactic sugar into useful statements in the model *)
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
    Proof. cbn. intros ->. now destruct n as [|n'] eqn:Heq.
    Qed.
    Opaque N.

    Lemma IB_P'_e rho i n : rho i = n -> rho ⊨ P' i -> {a:nat & {b:nat & n = Pair a b}}.
    Proof.
    intros Hrho H. destruct n as [m|a b].
    * exfalso. unfold P' in H. rewrite IB_sNot in H. eapply H, IB_N_i, Hrho.
    * now exists a, b.
    Qed.

    Lemma IB_P'_i rho i a b : rho i = (Pair a b) -> rho ⊨ P' i.
    Proof.
    unfold P'. rewrite IB_sNot. intros Hrho H. destruct (@IB_N_e rho i (Pair a b)). 
    1-2:easy. congruence.
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
    - now destruct a.
    - easy.
    Qed.

    Lemma IB_P_i rho ip il ir c : (forall a b, rho ip = (Pair a b) 
                                 -> rho il = (Num a) -> rho ir = (Num b) -> rho ⊨ c)
                                 -> rho ⊨ P ip il ir c.
    Proof.
    intros Hplrc. intros [pa [pb Hp]]%(IB_P'_e (n:=rho ip))
                         [la Ha]%(IB_N_e (n:=rho il))
                         [rb Hb]%(IB_N_e (n:=rho ir)) Hpl Hpr. 2-4: easy.
    cbn in Hpl, Hpr. rewrite Hp,<-Ha,<-Hb  in *. apply (@Hplrc la rb); destruct la; congruence.
    Qed.
    Opaque P.

    (** We show our model fulfills axiom 1 *)

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

    (** We show we can extract constraints from our model *)

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
    eapply IB_P_e in H. 2-4: easy. 2: exists a, b; cbn; auto.
    eapply IB_P_e in H. 2-4: easy. 2: exists c, d; cbn; auto.
    apply H. cbn. rewrite Hpl, Hpr. easy.
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
    apply IB_P_i. intros a b Hpl Ha Hb.
    apply IB_P_i. intros c d Hpr Hc Hd.
    intros Habcd. apply H. exists a,b,c,d. cbn in Habcd. rewrite Hpl, Hpr in Habcd. now repeat split.
    Qed.

    (** We show our model fulfills axiom 2 *)

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

    (** We show we can encode constraints into our model *)

    (** rho_descr_phi describes that rho is defined by the solution to h10 *)
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
    (** Helper for working with nested quantifiers *)

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
    (** Final utility lemma: translate the entire list of constraints *)

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
    (** We can now extract the constraints from our translate_constraints function*)

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

    (** To conclude, we can wrap the axioms around it.*)
    Lemma IB_fulfills rho : rho ⊨ F -> H10UPC_SAT h10.
    Proof.
      intros H. unfold F in H. pose (Num 0 .: Num 0 .: Num 1 .: rho) as nrho.
      assert (rho_canon nrho) as nrho_canon.
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

  (** If F is valid, h10 has a solution: *)
  Lemma inverseTransport : valid F -> H10UPC_SAT h10.
  Proof.
    intros H. apply (@IB_fulfills (fun b => Num 0)). apply H.
  Qed.

End validity.

(** Next is provability. Here we prove that if h10, our H10UPC_SAT instace, has a solution, F is provable.*)
Section provability.
  (** Again, assume a falsity flag and a problem instance. *)
  Context {ff : falsity_flag}. 
  Context {h10 : list h10upc}.
  Section ProvabilityTransport.
    (** The solution to cs *)
    Context (φ: nat -> nat). 
    (** Proof that it actually is a solution *)
    Context (Hφ : forall c, In c h10 -> h10upc_sem φ c). 

    Instance lt_dec (n m : nat) : dec (n < m). Proof. 
    apply Compare_dec.lt_dec.
    Defined.
    Instance le_dec (n m : nat) : dec (n <= m). Proof. 
    apply Compare_dec.le_dec.
    Defined. 

    (** Some useful tactics for manipulating proof contexts. *)

    Ltac var_eq := cbn; f_equal; lia.
    Ltac var_cbn := repeat (unfold up,scons,funcomp; cbn).
    Ltac doAllE s t := match goal with [ |- ?A ⊢I ?P] => assert (P = t[s..]) as ->; [idtac|eapply AllE] end.
    Ltac doAllI n := apply AllI; let H := fresh "H" in 
       match goal with [ |- map (subst_form ↑) ?A ⊢I ?phi ] => edestruct (@nameless_equiv_all _ _ _ intu A phi) as [n H]; rewrite H; clear H end.



    (** Helper for working with nested forall quantifiers. *)
    Lemma emplace_forall_subst (n:nat) (i:form) sigma : (emplace_forall n i)[sigma] = 
          emplace_forall n (i[it up n sigma]).
    Proof.
    induction n as [|n IH] in sigma|-*.
    - easy.
    - cbn. f_equal. now rewrite IH, <- it_shift.
    Qed.

    Fixpoint specialize_n (n:nat) (f:nat->nat) (k:nat) := 
          match n with 0 => $k 
                     | S n => match k with 0 => $(f 0)
                                         | S k => specialize_n n (fun l => (f (S l))) k end end.

    Lemma emplace_forall_elim (n:nat) (i:form) (pos:nat->nat) A : 
        A ⊢I emplace_forall n i -> A ⊢I (i[specialize_n n pos]).
    Proof.
    intros Hpr. induction n as [|n IH] in i,pos,Hpr|-*.
    - cbn. now rewrite subst_id.
    - cbn in Hpr. enough (i[up (specialize_n n (fun l=> (pos(S l))))][$(pos 0)..] = i[specialize_n (S n) pos]) as <-.
      + apply AllE. specialize (IH (∀ i) (fun l => (pos (S l)))). apply IH.
        unfold emplace_forall. rewrite <- it_shift. cbn. apply Hpr.
      + rewrite subst_comp. apply subst_ext. intros [|k].
        * easy.
        * var_cbn. rewrite subst_term_comp. var_cbn. now rewrite subst_term_id.
    Qed.

    Lemma specialize_n_resolve n f2 a : specialize_n n f2 a
                                        = if Dec (a < n) then $(f2 a) else $(a-n).
    Proof.
    induction n as [|n IH] in f2,a|-*.
    - cbn. var_eq.
    - cbn. destruct a as [|a].
      + easy.
      + cbn.
        unfold funcomp in IH. cbn in IH.
        rewrite IH. do 2 destruct (Dec _). 2,3: exfalso;lia. all:var_eq.
    Qed.

    (** We define the notion of a chain.
        A chain contains the de Brujin indices at which chain entries are present. *)
    Inductive chain : nat -> Type := chainZ : chain 0
                                   | chainS : forall (h:nat) (n pl pr:nat), chain h -> chain (S h).
    Definition height h (c:chain h) := h.

    Derive Signature for chain.
    (** We need to show some "uniqueness" lemmas for our chain, so we need an inversion lemma *)
    Lemma chain_inversion n (c:chain n) : (match n return chain n -> Type 
                                                   with 0 => fun cc => cc = chainZ | 
                                                        S nn => fun cc' => {'(n,pl,ph,cc) & cc' = chainS n pl ph cc} 
                                                   end) c.
    Proof.
    destruct c as [|m n pl pr c]. 1:easy. exists (n,pl,pr,c). easy.
    Qed.
    (** More functions on chains: chainData gets the data for some index, find* is an easier accessor *)
    Fixpoint chainData (h:nat) (c:chain h) (a:nat) := match c with
        @chainZ => (0,0,0)
      | @chainS _ n pl pr cc => if Dec (h=a) then (n,pl,pr) else chainData cc a end.
    
    Lemma chainData_0 (h:nat) (c:chain h) : chainData c 0 = (0,0,0).
    Proof. now induction c as [|h n pl ph cc IH]. Qed.

    Definition findNum h (c:chain h) a := let '(n,pl,ph) := chainData c a in n.
    Definition findPairLow h (c:chain h) a := let '(n,pl,ph) := chainData c a in pl.
    Definition findPairHigh h (c:chain h) a := let '(n,pl,ph) := chainData c a in ph.
    Fixpoint chain_exists h (c:chain h) := match c with
      @chainZ => N 0 :: nil
    | @chainS _ n pl ph cc => N n :: P' pl :: P' ph :: 
                   Pr $pl $0 :: Pr $(findNum cc (height cc)) $pl ::
                   Pr $ph $0 :: Pr $n $ph ::
                   Pr $pl $ph :: chain_exists cc end.

    Definition intros_defs (a b c e f g:nat) := Pr $e $g :: Pr $f $e :: N g :: N f :: P' e :: Pr $a $c :: Pr $b $a :: N c :: N b :: P' a :: nil.

    Definition intros_P (A:list form) (a b c e f g : nat) (i:form) :
    (intros_defs a b c e f g ++ A)  ⊢I i -> (A ⊢I P a b c (P e f g i)).
    Proof. intros H. do 10 apply II. exact H. Qed.

    (** Properties about our chain: numbers are N, pl and pr are in relation *)
    Lemma chain_proves_N (h:nat) (c:chain h) (i:nat) : i <= h -> In (N (findNum c i)) (chain_exists c).
    Proof.
    intros H. induction c as [|h n pl pr cc IH].
    - now left.
    - destruct (Dec (S h = i)) eqn:Heq.
      + left. unfold findNum. unfold chainData. now rewrite Heq.
      + do 8 right. unfold findNum, chainData. rewrite Heq. apply IH. lia.
    Qed.

    Lemma chain_proves_rel (h:nat) (c:chain h) (i:nat) : i <= h -> In (Pr $(findPairLow c i) $(findPairHigh c i)) (chain_exists c).
    Proof.
    intros H. induction c as [|h n pl pr cc IH].
    - now left.
    - destruct (Dec ((S h) = i)) eqn:Heq.
      + do 7 right. left. unfold findPairLow,findPairHigh,chainData. now rewrite Heq.
      + do 8 right. unfold findPairLow, findPairHigh, chainData. rewrite Heq. apply IH. lia.
    Qed.

    (** Chains up to h can be lowered to chains up to l for l <= h *)
    Lemma chain_lower (l:nat)  (h:nat) (c:chain h): l > 0 -> l <= h -> {cc : chain l & forall k, k <= l -> chainData c k = chainData cc k}.
    Proof.
    intros Hl Hh. revert c. assert (h=(h-l)+l) as -> by lia. generalize (h-l).
    intros dh c. induction dh as [|dh IH].
    - now exists c.
    - destruct (chain_inversion c) as [[[[n pl] ph] cc] ->]. fold Nat.add in cc.
      destruct (IH cc) as [cc' Hcc']. exists cc'.
      intros k Hk. cbn [chainData].
      destruct (Dec (S dh + l = k)) as [Hf|_].
      + lia.
      + apply Hcc'. lia.
    Qed.

    (** Chains are extensional, defined only by their data *)
    Lemma chain_data_unique (h:nat) (c1 c2 : chain h) : (forall k, k <= h -> chainData c1 k = chainData c2 k) -> c1 = c2.
    Proof.
    intros Heq. induction c1 as [|h n pl pr cc IHcc].
    - refine (match c2 with chainZ => _ end). easy.
    - destruct (chain_inversion c2) as [[[[n' pl'] ph'] cc'] ->].
      pose proof (Heq (S h) ltac:(lia)) as Heqh. cbn [chainData] in Heqh.
      destruct (Dec (S h = S h)) as [_|Hf]; [idtac|lia].
      rewrite (IHcc cc').
      + congruence.
      + intros k Hk. specialize (Heq k ltac:(lia)). cbn [chainData] in Heq.
        destruct (Dec (S h = k)) as [Ht|Hf]; [lia|easy].
    Qed.

    (** Lowering a chain preserves the hypotheses *)
    Lemma chain_exists_lower (l h :nat) (cl:chain l) (ch:chain h) : l<=h -> (forall k, k <= l -> chainData cl k = chainData ch k) 
                                                                         -> incl (chain_exists cl) (chain_exists ch).
    Proof.
    intros Hlh. revert ch. assert (h=(h-l)+l) as -> by lia. generalize (h-l) as dh.
    intros dh ch Heq. induction dh as [|dh IHdh].
    - now rewrite (@chain_data_unique l cl ch).
    - destruct (chain_inversion ch) as [[[[n pl] ph] ch'] Hch]; fold Nat.add in *.
      rewrite Hch. cbn; do 8 apply incl_tl. apply (IHdh ch').
      intros k Hk. rewrite Hch in Heq. specialize (Heq k Hk). cbn [chainData] in Heq.
      destruct (Dec (S dh + l =k)) as [Ht|Hf]; [lia|easy].
    Qed.

    (** Chain hypotheses prove all needed lemmata *)
    Lemma chain_proves_P_Low (h:nat) (c:chain h) (i:nat) A f : h > 0 -> i < h -> incl (chain_exists c) A 
                                                            -> A ⊢I P (findPairLow c (S i)) (findNum c i) 0 f -> A ⊢I f.
    Proof.
    intros Hh Hi HA Hpf.
    unfold P in Hpf.
    destruct (@chain_lower (S i) _ c) as [cc Hcc]. 1-2:lia.
    pose proof (@chain_exists_lower (S i) h cc c ltac:(lia)) as Hlower.
    eapply IE. 1:eapply IE. 1:eapply IE. 1:eapply IE. 1:eapply IE.
    1: unfold findPairLow, findNum in Hpf; apply Hpf.
    all: apply Ctx, HA.
    3: {pose proof (@chain_proves_N h c 0) as H0. unfold findNum in H0. rewrite chainData_0 in H0. apply H0. lia. }
    all: rewrite Hcc; [apply Hlower; [intros k Hk;symmetry;now apply Hcc|idtac]|lia].
    2: apply chain_proves_N; lia.
    all: destruct (chain_inversion cc) as [[[[n pl] ph] ch'] Hch]; subst cc; cbn [chain_exists chainData]. 
    - do 1 right. left. destruct (Dec _); [easy|lia].
    - do 4 right. left. rewrite Hcc. 2:lia. unfold chainData. do 2 destruct (Dec _); easy + lia.
    - do 3 right. left. destruct (Dec _). 1:easy. lia.
    Qed.

    Lemma chain_proves_P_High (h:nat) (c:chain h) (i:nat) A f : h > 0 -> i < h -> incl (chain_exists c) A
                                                             -> A ⊢I P (findPairHigh c (S i)) (findNum c (S i)) 0 f -> A ⊢I f.
    Proof.
    intros Hh Hi HA Hpf.
    unfold P in Hpf.
    destruct (@chain_lower (S i) _ c) as [cc Hcc]. 1-2:lia.
    pose proof (@chain_exists_lower (S i) h cc c ltac:(lia)) as Hlower.
    eapply IE. 1:eapply IE. 1:eapply IE. 1:eapply IE. 1:eapply IE.
    1: unfold findPairHigh, findNum in Hpf; apply Hpf.
    all: apply Ctx, HA.
    3: {pose proof (@chain_proves_N h c 0) as H0. unfold findNum in H0. rewrite chainData_0 in H0. apply H0. lia. }
    all: rewrite Hcc; [apply Hlower; [intros k Hk;symmetry;now apply Hcc|idtac]|lia].
    2: apply chain_proves_N; lia.
    all: destruct (chain_inversion cc) as [[[[n pl] ph] ch'] Hch]; subst cc; cbn [chain_exists chainData]. 
    - do 2 right. left. destruct (Dec _); [easy|lia].
    - do 6 right. left. destruct (Dec _); [easy|lia].
    - do 5 right. left. destruct (Dec _); [easy|lia].
    Qed.

    Lemma chain_proves_E_rel (h a : nat) (c:chain h) A f : S a <= h -> incl (chain_exists c) A -> A ⊢I rel (findPairLow c (S a)) (findPairHigh c (S a)) (findNum c a) 0 (findNum c (S a)) 0 f -> A ⊢I f.
    Proof.
    intros Ha HA Hpr.
    eapply IE.
    2: eapply Ctx, HA, (@chain_proves_rel _ _ (S a)); lia.
    unfold rel in Hpr.
    apply (@chain_proves_P_High h c a). 1-2:lia. 1:easy.
    apply (@chain_proves_P_Low h c a). 1-2:lia. 1:easy.
    exact Hpr.
    Qed.


    (** Helper definition erel_i, along with utility lemmata. *)
    Definition erel_i (a b c d t : nat) := (∀ ∀ P 0 (2+a) (2+b) 
                                               (P 1 (2+c) (2+d)
                                                 (Pr $0 $1 --> wFalse (2+t)))).
    
    Definition erel_findNum (a b c d h:nat) (cc:chain h):= erel_i (findNum cc a) (findNum cc b) (findNum cc c) (findNum cc d) (1).
    Lemma erel_findNum_II (a b c d h: nat) (cc:chain h) A : (erel_findNum a b c d cc :: A) ⊢I wFalse 1 -> A ⊢I erel (findNum cc a) (findNum cc b) (findNum cc c) (findNum cc d) 1.
    Proof. intros H. apply II. exact H. Qed.
    Definition erel_findNum_H (a b c d pl pr h : nat) (cc:chain h):list form := 
         Pr $pl $pr
      :: Pr $pr $(findNum cc d)
      :: Pr $(findNum cc c) $pr
      :: N (findNum cc d)
      :: N (findNum cc c)
      :: P' pr
      :: Pr $pl $(findNum cc b)
      :: Pr $(findNum cc a) $pl
      :: N (findNum cc b)
      :: N (findNum cc a)
      :: P' pl :: nil.


    Lemma erel_findNum_ExI (a b c d h : nat) (cc:chain h) A :
    (forall pl pr, (erel_findNum_H a b c d pl pr cc ++ A) ⊢I wFalse 1) -> A ⊢I erel_findNum a b c d cc .
    Proof.
    intros Hpr. unfold erel_findNum, erel_i.
    doAllI pr. cbn [subst_form]. doAllI pl.
    cbn.
    do 11 apply II. eapply Weak. 1: apply (Hpr pl pr).
    apply incl_app.
    - unfold erel_findNum_H. now repeat apply ListAutomation.incl_shift.
    - now do 11 apply incl_tl.
    Qed.

    Lemma erel_findNum_H_E (a b c d pl pr h : nat) (cc:chain h) A f : 
       incl (erel_findNum_H a b c d pl pr cc) A 
    -> A ⊢I rel pl pr (findNum cc a) (findNum cc b) (findNum cc c) (findNum cc d) f
    -> A ⊢I f.
    Proof.
    intros HA Hpr.
    let rec rep n := match n with 0 => now left | S ?nn => right; rep nn end in
    let rec f n k := match n with 0 => apply Hpr | S ?nn => eapply IE; [f nn (S k)|apply Ctx, HA; rep k] end in f 11 0.
    Qed.

    Lemma erel_i_subst (a b c d t:nat) s ss : (forall n,s n = $(ss n)) -> (ss (S t)) = S(ss t) -> (erel_i a b c d t --> wFalse t)[s] = erel_i (ss a) (ss b) (ss c) (ss d) (ss t) --> wFalse (ss t).
    Proof.
    intros H Hs. cbn. unfold erel_i,P,N,P',funcomp. rewrite ! H. do 20 f_equal. all: cbn; rewrite Hs; easy.
    Qed.

    Lemma erel_ereli (a b c d t:nat) : erel a b c d t = erel_i a b c d t --> wFalse t.
    Proof. easy. Qed.

    Fixpoint subst_list (l:list nat) (n:nat) := match l with nil => n | lx::lr => match n with 0 => lx | S n => subst_list lr n end end.

    Lemma emplace_forall_shift (n : nat) (f:form) : emplace_forall n (∀ f) = emplace_forall (S n) f.
    Proof. unfold emplace_forall. now rewrite it_shift. Qed.

    Lemma specialize_list (H f:form) (l:list nat) (n:nat) : 
       length l = n
    -> (H[subst_list l >> var]:: nil) ⊢I f
    -> (emplace_forall n H::nil) ⊢I f.
    Proof.
    induction l as [|lx lr IH] in n,H|-*.
    - intros <-. cbn. now erewrite subst_id.
    - intros <- Hpr. cbn [length]. specialize (IH (∀ H) (length lr) eq_refl).
      cbn in IH. rewrite emplace_forall_shift in IH.
      eapply IH, IE.
      + apply Weak with nil. 2:easy. apply II, Hpr.
      + assert (H[up (subst_list lr >> var)][$lx..] = H[subst_list (lx :: lr) >> var]) as <-.
        * rewrite subst_comp. apply subst_ext. now intros [|n].
        * apply AllE, Ctx. now left.
    Qed.

    (** We can create a chain up to an arbitrary index *)
    Lemma construct_chain_at (h:nat) HH : (h>0)
    -> incl (F_succ_right :: F_succ_left :: F_zero :: nil) HH
    -> (forall c:chain h, (chain_exists c ++  HH) ⊢I wFalse 1)
    -> HH ⊢I wFalse 1.
    Proof.
    intros Hn HHH H. induction h as [|h IH].
    - exfalso. lia. 
    - destruct h as [|h].
      + clear IH. apply (IE (phi:=(∀ (∀ (∀ P 2 3 3 (P 0 1 3 (Pr $2 $0 --> wFalse (4)))))))).
        * eapply IE.
          2: apply Ctx,HHH; do 2 right; now left.
          doAllE ($0) (N 0 --> (∀ (∀ (∀ P 2 3 4 (P 0 1 4 (Pr $2 $0 --> wFalse 5))))) --> wFalse (2)).
          1: easy.
          apply Ctx,HHH. right. now left.
        * doAllI pl. doAllI n1. doAllI pr. apply intros_P. cbn -[intros_defs].
          apply II.
          eapply Weak. 1:apply (H (chainS n1 pl pr chainZ)). apply incl_app.
          2: do 11 apply incl_tl; reflexivity.
          cbn -[map]. 
          intros f [Hf|[Hf|[Hf|[Hf|[Hf|[Hf|[Hf|[Hf|[Hf|[]]]]]]]]]]; rewrite <- Hf;
          let rec find n 
              := match n with 0 => now left
                            | S ?nn => (now left) + (right; find nn) end
          in find 11.
      + apply IH; [lia|clear IH]. intros c.
        eapply (IE (phi:=(∀ (∀ (∀ P 2 (3+findNum c (S h)) 3 
                                 (P 0 1 3 (Pr $2 $0 --> wFalse 4))))))). 
        * unfold F_succ_left. unfold Not. eapply IE.
          2: apply Ctx, in_or_app; left; eapply chain_proves_N; easy.
          doAllE ($(findNum c (S h))) (N 0 -->  (∀ (∀ (∀ P 2 3 4
                                              (P 0 1 4 (Pr $2 $0 --> wFalse 5))))) --> wFalse 2).
          -- easy.
          -- apply Ctx. apply in_or_app. right. apply HHH. right. now left.
        * doAllI pl. doAllI nh. doAllI pr. apply intros_P. cbn -[intros_defs].
          apply II.
          eapply Weak. 1:apply (H (chainS nh pl pr c)). apply incl_app.
          2: do 11 apply incl_tl; now apply incl_appr.
          cbn -[map]. 
          intros f [Hf|[Hf|[Hf|[Hf|[Hf|[Hf|[Hf|[Hf|H1]]]]]]]].
          9: do 11 right; apply in_or_app; now left.
          all: rewrite <- Hf;
          let rec find n 
              := match n with 0 => now left
                            | S ?nn => (now left) + (right; find nn) end
          in find 11.
    Qed.
      
    (** Our chain can prove a single constraint *)
    Lemma prove_single (a b c d h: nat) (cc:chain h): 
       b <= h -> a <= h -> c <= h -> d <= h
    -> h10upc_sem_direct ((a,b),(c,d))
    -> (chain_exists cc ++ (F_succ_right :: F_succ_left :: F_zero :: nil)) ⊢I Not (erel_findNum a b c d cc) 1.
    Proof. 
    intros Hb. induction b as [|b IH] in h,cc,a,c,d,Hb|-*; intros Ha Hc Hd Habcd.
    - cbn in Habcd. assert (c = S a /\ d = 0) as [Hc' Hd']. 1:lia.
      rewrite Hc', Hd'. apply II. rewrite Hc' in Hc.
      apply (@chain_proves_E_rel h a cc). 1:lia.
      1: now apply incl_tl,incl_appl.
      eapply Weak with (erel_findNum a 0 (S a) 0 cc::nil). 2:intros k [->|[]]; now left.
      unfold erel_findNum, erel_i. change (∀∀ ?e) with (emplace_forall 2 e).
      eapply specialize_list with (findPairLow cc (S a)::findPairHigh cc (S a)::nil).
      1:easy. unfold findNum. rewrite ! chainData_0. apply Ctx. now left.
    - destruct (@h10upc_inv a b c d Habcd) as [c' [d' [Habcd' [Hc' Hd']]]].
      rewrite <- Hc', <- Hd' in *. 
      assert (h10upc_sem_direct ((d',b),(d'+b+1,d'))) as Hdb.
      1: split; [now lia|apply Habcd'].
      apply erel_findNum_II. eapply IE.
      1: eapply Weak; [apply (@IH a c' d' h); easy + lia | now apply incl_tl].
      apply erel_findNum_ExI. intros pab pc'd'. 
      eapply IE.
      1: eapply Weak; [apply (@IH d' (d'+b+1) d' h); lia + easy|idtac]. 
      1: now apply incl_appr; apply incl_tl.
      apply erel_findNum_ExI. intros pd'b psd'.
      apply (IE (phi:=erel_findNum a (S b) (S c') (d' + b + 1) cc)).
      2: apply Ctx, in_or_app; right; apply in_or_app; right; now left.
      apply (@chain_proves_E_rel h c' cc). 1:lia.
      1: now apply incl_appr, incl_appr, incl_tl, incl_appl.
      apply (@chain_proves_E_rel h b cc). 1:lia.
      1: now apply incl_appr, incl_appr, incl_tl, incl_appl.
      apply (@erel_findNum_H_E d' b (d' + b + 1) d' pd'b psd' h cc).
      1: now apply incl_appl.
      apply (@erel_findNum_H_E a b c' d' pab pc'd' h cc).
      1: now apply incl_appr, incl_appl.
      apply Weak with (F_succ_right::nil).
      2: apply incl_appr, incl_appr, incl_tl, incl_appr; intros k [->|[]]; now left.
      unfold F_succ_right. rewrite erel_ereli.
      change (∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀ ?a) with (emplace_forall 15 a).
      pose (
        (findNum cc a)
      ::(findNum cc b)
      ::(findNum cc c')
      ::(findNum cc d')
      ::(findNum cc (d'+b+1))
      ::(findNum cc (S b))
      ::(findNum cc (S c'))
      ::pab::pc'd'::pd'b::psd'
      ::(findPairLow cc (S b))::(findPairHigh cc (S b))
      ::(findPairLow cc (S c'))::(findPairHigh cc (S c'))::nil) as mylist.
      eapply specialize_list with mylist.
      1:easy.
      apply Ctx. now left.
    Qed.


    (** This allows us to conclude *)
    Lemma transport_prove : nil ⊢I F (h10:=h10).
    Proof using Hφ φ.
    unfold F. do 3 apply AllI. cbn. do 4 apply II. 
    pose ((S (highest_var_list h10))) as h10vars. fold h10vars.
    pose (highest_num φ h10vars) as h10max.
    pose proof (@highest_num_descr φ h10vars) as Hvars.
    fold h10max in Hvars.
    eapply (@construct_chain_at (S h10max)).
    1:lia. 1:now apply incl_tl. intros cc.
    epose proof (@emplace_forall_elim h10vars _ (fun k => findNum cc (φ k))) as Hpr.
    eapply IE. 2:eapply Hpr. 2: apply Ctx, in_or_app; right; now left.
    eapply Weak. 2: apply incl_app; [apply incl_appl;reflexivity|apply incl_appr,incl_tl;reflexivity].
    apply II. clear Hpr.
    assert (h10vars >= S( highest_var_list h10)) as Hless.
    1: lia.
    induction h10 as [|h h10' IHh] in Hvars,Hφ,Hless|-*.
    - apply Ctx. left. unfold translate_rec, wFalse, subst_form,Vector.map. do 3 f_equal.
      1: change(S h10vars) with (1+h10vars).
      all: cbn [subst_term]; rewrite specialize_n_resolve; destruct Dec; lia + f_equal;lia.
    - cbn -[Nat.mul h10vars chain_exists subst_form].
      apply II in IHh.
      2: intros c' Hc; apply Hφ; now right.
      2: exact Hvars.
      2: cbn in Hless; lia.
      eapply IE. 1: eapply Weak. 1: exact IHh.
      1: now apply incl_tl. 
      eapply IE. 1: apply Ctx; left; now cbn [subst_form].
      eapply Weak. 2: apply incl_tl; reflexivity.
      unfold translate_single. destruct h as [[a b][c d]].
      rewrite erel_ereli. clear IHh.
      unfold Not. erewrite (@erel_i_subst _ _ _ _ _ _ (fun k : nat => if Dec (k < h10vars) then findNum cc (φ k) else ((k - h10vars)))).
      3: repeat destruct Dec; (exfalso;lia) + lia. 
      2: intros n; rewrite specialize_n_resolve; destruct (Dec _); (exfalso;lia)+var_eq.
      destruct (highest_var_descr ((a,b),(c,d))) as [Hlessa [Hlessb [Hlessc Hlessd]]]. cbn in Hless.
      do 4 (destruct Dec as [htr|hff]; [clear htr|exfalso;lia]).
      do 1 (destruct Dec; [exfalso;lia|idtac]). 
      assert (forall a,S a - a=1) as -> by (intros;lia).
      eapply Weak.
      1: eapply (prove_single).
      + specialize (Hvars b ltac:(lia)). lia.
      + specialize (Hvars a ltac:(lia)). lia.
      + specialize (Hvars c ltac:(lia)). lia.
      + specialize (Hvars d ltac:(lia)). lia.
      + apply (@Hφ ((a,b),(c,d))). now left.
      + easy.
  Qed.
  End ProvabilityTransport.


  (** Final reduction transport *)
  Lemma proofTransport : H10UPC_SAT h10 -> nil ⊢I F (h10:=h10).
  Proof.
  intros [φ Hφ]. eapply transport_prove. exact Hφ.
  Qed.


  (** Reduction transport for validity, just a special case of the above *)
  Lemma transport : H10UPC_SAT h10 -> valid (F (h10:=h10)).
  Proof.
    intros Hh10.
    intros D I rho.
    eapply soundness.
    - now apply proofTransport.
    - easy.
  Qed.


  (** Inverse transport, uses standard model from before *)
  Lemma inverseProofTransport : nil ⊢I F (h10:=h10) -> H10UPC_SAT h10.
  Proof.
  intros H%soundness. apply inverseTransport. intros D I rho.
  apply H. easy.
  Qed.
End provability.

(** We also have Kripke validity *)
Section kripke_validity.
  Context {ff : falsity_flag}. 
  Context {h10 : list h10upc}.

  Lemma kripkeTransport : H10UPC_SAT h10 -> kvalid (F (h10:=h10)).
  Proof.
  intros H. 
  intros D M u rho. eapply ksoundness with nil.
  - now apply proofTransport.
  - intros a [].
  Qed.

  Lemma kripkeInverseTransport : kvalid (F (h10:=h10)) -> H10UPC_SAT h10.
  Proof.
  intros H. apply inverseTransport.
  intros D I rho. apply kripke_tarski. apply H.
  Qed.
End kripke_validity.

(** We also have classical provability, assuming LEM *)
Section classical_provability.
  Context {ff : falsity_flag}. 
  Context {h10 : list h10upc}.
  Context (LEM : forall P:Prop, P \/ ~P).

  Lemma classicalProvabilityTransport : H10UPC_SAT h10 -> nil ⊢C F (h10:=h10).
  Proof using LEM.
  intros [φ Hφ]. apply intuitionistic_is_classical. eapply transport_prove. exact Hφ.
  Qed.

  Lemma classicalProvabilityInverseTransport : nil ⊢C F (h10:=h10) -> H10UPC_SAT h10.
  Proof using LEM.
  intros H%(classical_soundness LEM). apply inverseTransport. intros D I rho.
  apply H. easy.
  Qed.
End classical_provability.

(** We have satisfiability, if we re-introduce negations *)
Section satisfiability.
  Context {h10 : list h10upc}.

  Lemma satisTransport : (~ H10UPC_SAT h10) -> satis ((F (ff:=falsity_on) (h10:=h10)) --> falsity).
  Proof.
  intros H.
  exists dom.
  exists (IB (h10:=h10)).
  exists (fun _ => Num 0).
  intros HF. apply H. eapply IB_fulfills. easy.
  Qed.

  Lemma satisInverseTransport : satis ((F (ff:=falsity_on) (h10:=h10)) --> falsity) -> (~ H10UPC_SAT h10).
  Proof.
  intros [D [I [rho HF]]] H.
  apply HF, (transport (ff:=falsity_on) H).
  Qed.
End satisfiability.

(** Similarly, we have Kripke satisfiability *)
Section ksatisfiability.
  Context {h10 : list h10upc}.

  Lemma ksatisTransport : (~ H10UPC_SAT h10) -> ksatis ((F (ff:=falsity_on) (h10:=h10)) --> falsity).
  Proof.
  intros H.
  exists dom.
  pose (kripke_tarski (ff:=falsity_on) (IB (h10:=h10))) as Hk.
  exists (interp_kripke (IB (h10:=h10))).
  exists tt.
  exists (fun _ => Num 0).
  rewrite <- Hk.
  intros HF. apply H. eapply IB_fulfills. easy.
  Qed.

  Lemma ksatisInverseTransport : ksatis ((F (ff:=falsity_on) (h10:=h10)) --> falsity) -> (~ H10UPC_SAT h10).
  Proof.
  intros [D [M [u [rho HF]]]] H.
  specialize (HF u). apply HF.
  - apply reach_refl.
  - apply (kripkeTransport (ff:=falsity_on) H).
  Qed.
End ksatisfiability.

Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.

(** Final collection of undecidability reductions *)
Section undecResults.

  Definition minimalSignature (f:funcs_signature) (p:preds_signature) : Prop := 
    match f,p with
     {|syms := F; ar_syms := aF|},{|preds := P; ar_preds := aP|}
       => (F -> False) /\ exists pp : P, aP pp = 2
    end.

  Lemma sig_is_minimal : minimalSignature sig_empty sig_binary.
  Proof.
  split.
  * intros [].
  * now exists tt.
  Qed.

  Definition reductionToMinimal (f:falsity_flag) {X:Type} (H:X -> Prop) (P:@form sig_empty sig_binary frag_operators f -> Prop) := 
   H ⪯ P.

  Theorem validReduction : reductionToMinimal (f:=falsity_off) H10UPC_SAT valid.
  Proof.
  exists (fun l => @F falsity_off l). split.
  * apply transport.
  * apply inverseTransport.
  Qed.

  Theorem satisReduction : reductionToMinimal (f:=falsity_on) (fun l => ~ H10UPC_SAT l) satis.
  Proof.
  exists (fun l => @F falsity_on l --> falsity). split.
  * apply satisTransport.
  * apply satisInverseTransport.
  Qed.

  Theorem proveReduction : reductionToMinimal (f:=falsity_off) H10UPC_SAT (fun k => nil ⊢M k).
  Proof.
  exists (fun l => @F falsity_off l). split.
  * apply proofTransport.
  * apply inverseProofTransport.
  Qed.

  Theorem classicalProveReduction (LEM : forall P:Prop, P \/ ~P) :
    reductionToMinimal (f:=falsity_off) H10UPC_SAT (fun k => nil ⊢C k).
  Proof.
  exists (fun l => @F falsity_off l). split.
  * apply classicalProvabilityTransport, LEM.
  * apply classicalProvabilityInverseTransport, LEM.
  Qed.

  Theorem kripkeValidReduction : reductionToMinimal (f:=falsity_off) H10UPC_SAT kvalid.
  Proof.
  exists (fun l => @F falsity_off l). split.
  * apply kripkeTransport.
  * apply kripkeInverseTransport.
  Qed.

  Theorem kripkeSatisReduction : reductionToMinimal (f:=falsity_on) (fun l => ~ H10UPC_SAT l) ksatis.
  Proof.
  exists (fun l => @F falsity_on l --> falsity). split.
  * apply ksatisTransport.
  * apply ksatisInverseTransport.
  Qed.

End undecResults.




