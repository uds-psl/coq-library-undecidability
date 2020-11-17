Require Import List Lia.

Require Import Undecidability.TM.SBTM.

Require Undecidability.StringRewriting.SR.
Require Import Undecidability.StringRewriting.Util.Definitions.
Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts.

Import ListNotations.

Lemma nil_app_tail {X} (x : X) l : ~ [] = l ++ [x]. destruct l; cbn; firstorder congruence. Qed.
Lemma nil_app_tail' {X} (x : X) l : ~ l ++ [x] = []. destruct l; cbn; firstorder congruence. Qed.

Section FixM.

    Variable M : SBTM.

    Notation END := 0.
    Notation X := 1.
    Notation "⦇" := 2.
    Notation "⦈" := 3.
    Notation tt := 4.
    Notation ff := 5.
    Notation "!! b" := (if b then tt else ff) (at level 1).
    Definition enc_state (q : Fin.t (S (num_states M))) := ((S ff) + proj1_sig (Fin.to_nat q)).
    Notation "! p" := (enc_state p) (at level 1).

    Fixpoint all_fins (n : nat) : list (Fin.t n) :=
        match n with
        | 0 => nil
        | S n => Fin.F1 :: map Fin.FS (all_fins n)
        end.

    Lemma in_all_fins n i :
      In i (all_fins n).
    Proof.
      induction i.
      - cbn. eauto.
      - cbn. right. eapply in_map_iff. eauto.
    Qed.

    Definition all_states {B} f : list B := flat_map f (all_fins (S (num_states M))).

    Definition all_syms {B} f : list B := [f tt ; f ff].

    Definition encode_sym (o : option bool) := match o with None => X | Some true => tt | Some false => ff end.

    Definition encode_trans (c : option (state M * option bool * move)) (q : Fin.t (S (num_states M))) : option (nat * nat * nat * move) := 
        option_map (fun '(s,o,m) => (!q, !s, encode_sym o, m)) c.

    Definition rules q₁ : list (list nat * list nat):= 
        match encode_trans (trans M (q₁, None)) q₁ with
        | Some (q₁, q₂, X, Lmove) => all_syms (fun l => ([l;q₁;X], [q₂;l])) ++ [([⦇;q₁;X],[⦇;q₂;X])]
        | Some (q₁, q₂, X, Nmove) => [([q₁;X], [q₂;X])]
        | Some (q₁, q₂, X, Rmove) => all_syms (fun r => ([q₁;X;r], [q₂;r])) ++ [([q₁;X;⦈],[q₂;X;⦈])]
        | Some (q₁, q₂, c, Lmove) => all_syms (fun l => ([l;q₁;X], [q₂;l;c])) ++ [([⦇;q₁;X],[⦇;q₂;X;c])]
        | Some (q₁, q₂, c, Nmove) => [([q₁;X], [q₂;c])]
        | Some (q₁, q₂, c, Rmove) => all_syms (fun r => ([q₁;X;r], [c;q₂;r])) ++ [([q₁;X;⦈],[c;q₂;X;⦈])]
        | None => []
        end ++
        let a := tt in
        match encode_trans (trans M (q₁, Some true)) q₁ with
        | Some (q₁, q₂, X, Lmove) => all_syms (fun l => ([l;q₁;a], [q₂;l;a])) ++ [([⦇;q₁;a],[⦇;q₂;X;a])]
        | Some (q₁, q₂, X, Nmove) => [([q₁;a], [q₂;a])]
        | Some (q₁, q₂, X, Rmove) => all_syms (fun r => ([q₁;a;r], [a;q₂;r])) ++ [([q₁;a;⦈],[a;q₂;X;⦈])]
        | Some (q₁, q₂, c, Lmove) => all_syms (fun l => ([l;q₁;a], [q₂;l;c])) ++ [([⦇;q₁;a],[⦇;q₂;X;c])]
        | Some (q₁, q₂, c, Rmove) => all_syms (fun r => ([q₁;a;r], [c;q₂;r])) ++ [([q₁;a;⦈],[c;q₂;X;⦈])]
        | Some (q₁, q₂, c, Nmove) => [([q₁;a], [q₂;c])]
        | None => []
        end ++
        let a := ff in
        match encode_trans (trans M (q₁, Some false)) q₁ with
        | Some (q₁, q₂, X, Lmove) => all_syms (fun l => ([l;q₁;a], [q₂;l;a])) ++ [([⦇;q₁;a],[⦇;q₂;X;a])]
        | Some (q₁, q₂, X, Rmove) => all_syms (fun r => ([q₁;a;r], [a;q₂;r])) ++ [([q₁;a;⦈],[a;q₂;X;⦈])]
        | Some (q₁, q₂, X, Nmove) => [([q₁;a], [q₂;a])]
        | Some (q₁, q₂, c, Lmove) => all_syms (fun l => ([l;q₁;a], [q₂;l;c])) ++ [([⦇;q₁;a],[⦇;q₂;X;c])]
        | Some (q₁, q₂, c, Rmove) => all_syms (fun r => ([q₁;a;r], [c;q₂;r])) ++ [([q₁;a;⦈],[c;q₂;X;⦈])]
        | Some (q₁, q₂, c, Nmove) => [([q₁;a], [q₂;c])]
        | None => []
        end.

    Definition R : SR.SRS nat := all_states rules.

    Lemma rules_incl q :
      incl (rules q) R.
    Proof.
      unfold R, all_states.
      intros r Hr.
      eapply in_flat_map.
      exists q. split; [ | assumption].
      eapply in_all_fins.
    Qed.

    Definition enc_conf '(ls, o, rs) (q : Fin.t (S (num_states M))) : list nat :=
      [⦇] ++ map (fun b : bool => !!b) (rev ls) ++ [!q] ++ [encode_sym o] ++ map (fun b : bool => !!b) rs ++ [⦈].

    Lemma simulation q1 q2 t1 t2 :
      eval M  q1 t1 q2 t2 -> SR.rewt R (enc_conf t1 q1) (enc_conf t2 q2).
    Proof.
      induction 1.
      - econstructor.
      - econstructor. 2:eassumption. clear - H.
        destruct t as [[ls o] rs]. cbn in H.
        eapply rew_subset with (2 := @rules_incl q).
        unfold rules.
        destruct o as [ [] | ] eqn:Eo; rewrite H; clear H.
        1: eapply rew_subset; [ | eapply incl_appr, incl_appl, incl_refl ].
        2: eapply rew_subset; [ | eapply incl_appr, incl_appr, incl_refl ].
        3: eapply rew_subset; [ | eapply incl_appl, incl_refl ].
        all:destruct w as [[] | ] eqn:Ew, m eqn:Em; cbn -[Nat.add].
        all:try match goal with [ |- context[enc_conf match ?l with _ => _ end]] => destruct l as [ | [] ] eqn:El end; cbn -[Nat.add].
        all: rewrite ?map_app; cbn [map app].
        all:unfold all_syms.
       
        Ltac inst_left := match goal with [ |- ?L = ?R ] => 
        match L with
          context C [?x1 :: ?x2 :: ?x3 :: ?r] => let t := context C [@nil nat] in instantiate (2 := t)
        | context C [?x1 :: ?x2 :: ?r] => let t := context C [@nil nat] in instantiate (2 := t)
        end
        end.
        Ltac help1 := cbn -[Nat.add]; simpl_list; cbn -[Nat.add];inst_left; cbn; now simpl_list.
        Ltac help2 := cbn -[Nat.add]; now simpl_list.

        all: eapply do_rew; [ (now left + (right; now left) + (right; right; now left) + (right; right; right; now left))  | help1 | help2].
    Qed.

    Lemma enc_state_inv q t q' :
      In (enc_state q) (enc_conf t q') -> q = q'.
    Proof.
      destruct t as [[ls o] rs].
      unfold enc_conf.
      rewrite !in_app_iff, !in_map_iff; repeat setoid_rewrite <- in_rev. cbn. firstorder try lia.
      all: try (destruct x; lia). eapply Fin.to_nat_inj. lia. destruct o as [[]|]; cbn in *; lia.
    Qed.

    Lemma enc_conf_END t q : ~ In END (enc_conf t q).
    Proof.
      destruct t as [[ls o] rs].
      unfold enc_conf.
      rewrite !in_app_iff, !in_map_iff; repeat setoid_rewrite <- in_rev. cbn.
      intros H. decompose [or] H; try lia; firstorder; try lia.
      all: try (destruct x; lia). destruct o as [[]|]; cbn in *; lia.
    Qed.

    Lemma enc_conf_inv' xs q ys ls o rs q' :
      xs ++ !q ++ ys = enc_conf (ls, o, rs) q' ->
      xs = [⦇] ++ map (fun b : bool => !!b) (rev ls) /\
      q = q' /\
      ys = encode_sym o :: map (fun b : bool => !!b) rs ++ [⦈].
    Proof.
      intros. pose proof (H' := H). cbn - [Nat.add] in H.
      destruct xs; cbn -[Nat.add] in H; inversion H; subst n; clear H.

      eapply list_prefix_inv' in H2 as (H1 & -> & H3).
      - subst. repeat split. eapply Fin.to_nat_inj. unfold "!" in H1. lia.
      - clear H'. induction xs in ls, H2 |- *.
        + firstorder.
        + cbn -[Nat.add]. destruct ls as [ | ? ? _] using rev_ind.
          * cbn -[Nat.add] in H2. inversion H2. subst. destruct xs; inversion H1; subst.
            destruct o as [ [] | ]; cbn in H0; lia.
            assert (In (!q) (map (fun b : bool => !! b) rs ++ [⦈])). rewrite <- H3. rewrite in_app_iff. cbn[In]. solve [eauto].
            eapply in_app_iff in H as [ (? & ? & ?) % in_map_iff | [ | []]]; try destruct x; cbn in H; lia.
          * rewrite rev_app_distr in H2. cbn -[Nat.add] in H2. inversion H2; subst.
            intros [ | ].
            -- destruct x; cbn in *; lia.
            -- eapply IHxs. 2:eauto. rewrite H1. reflexivity.
      - intros (? & ? & ?) % in_map_iff. destruct x; cbn in *; lia.
    Qed.

    Lemma enc_conf_inv xs q c ys ls o rs q' :
      xs ++ !q ++ [c] ++ ys = enc_conf (ls, o, rs) q' ->
      xs = [⦇] ++ map (fun b : bool => !!b) (rev ls) /\
      q = q' /\
      c = encode_sym o /\
      ys = map (fun b : bool => !!b) rs ++ [⦈].
    Proof.
      intros. eapply enc_conf_inv' in H as (-> & -> & [= -> ->]). eauto.
    Qed.

    Definition swap {X Y} : X * Y -> Y * X := fun '(x,y) => (y,x).

    Lemma rev_sim t q z : 
      SR.rew R (enc_conf t q) z -> exists q' w m, trans M (q, curr t) = Some (q', w, m) /\ z = enc_conf (mv m (wr w t)) q'.
    Proof.
      intros H. inversion H as [x y u v Hin HL HR]; subst z.
      destruct t as [[ls o] rs]. 
      eapply in_flat_map in Hin as (q_ & _ & Hq2).
      unfold rules in Hq2.
      rewrite ! in_app_iff in Hq2.
      destruct Hq2 as [ Hq2 | [Hq2 | Hq2]].
      all: destruct (trans M (q_, _)) as [ [[q' w] m] | ] eqn:Etrans; try destruct m eqn:Em;
          try destruct w as [[] | ] eqn:Ew; cbn -[Nat.add] in Hq2; (exists q', w, m || exfalso); rewrite ?Em, ?Ew.
      all: repeat match type of Hq2 with _ \/ _ => destruct Hq2 as [Hq2 | Hq2] end; inversion Hq2; subst u v; clear Hq2; cbn -[Nat.add].

      cbn [app] in HL.
      all:
          cbn [app] in HL;
          match type of HL with
          | ?L = ?R => match L with context C [! ?q :: ?c :: ?rs] => let ls := context C [@nil nat] in 
           replace L with (ls ++ !q ++ [c] ++ rs) in HL; [ | cbn; now simpl_list]
          end
          end.

    all:
        match type of HL with _ = enc_conf (?ls,?o,?rs) ?q =>
        let H1 := fresh "H" in let H2 := fresh "H" in let H3 := fresh "H" in let H4 := fresh "H" in let HH := fresh "H" in
        eapply enc_conf_inv in HL as (H1 & -> & H3 & H4); try rewrite H4 in *; destruct o as [ [] | ]; inversion H3; clear H3; cbn in H1;
        rewrite ?app_nil_r in H1; subst;
        split ; try eassumption; try reflexivity;
        (let x := match type of H1 with ?x ++ _ = _ => x end in
        destruct x; try (now inversion H1); cbn in H1; eapply cons_inj in H1 as [HH H1]; try rewrite HH in *; clear HH;
        now destruct ls as [ | []]; cbn in H1; 
        [ reflexivity || destruct x; now inversion H1 | try rewrite map_app in H1; cbn in H1; (eapply app_inj_tail in H1 as [-> [=]] + (try eapply nil_app_tail in H1 as []) + (try eapply nil_app_tail' in H1 as []) ).. ])
        + (destruct rs as [ | [] rs]; cbn in H4; eapply cons_inj in H4 as [ [=] H4]; rewrite ?H4 in *; clear H4;
           now cbn; simpl_list)
         end.
  Qed.
  
  Lemma help_exists1 (P : state M -> tape -> option bool -> move -> Prop) :
    (exists c q w m ls rs, P q (ls, c, rs) w m) ->  (exists q t w m, P q t w m).
  Proof.
    intros (c & q & w & m & ls & rs & H). now exists q, (ls, c, rs), w, m.
  Qed.    

  Lemma help_exists2 P Q :
    (P /\ exists ls rs, Q ls rs) -> exists ls rs : list bool, P /\ Q ls rs.
  Proof.
    firstorder.
  Qed.

  Lemma rev_sim_swap t q z : 
  SR.rew (map swap R) (enc_conf t q) z -> exists q' t' w m, trans M (q', curr t') = Some (q, w, m) /\ t = mv m (wr w t') /\ z = enc_conf t' q'.
  Proof.
    intros H. inversion H as [x y v u Hin HL HR]; subst z.
    eapply in_map_iff in Hin as ([? ?] & [= -> ->] & Hin).
    destruct t as [[ls o] rs]. 
    eapply in_flat_map in Hin as (q_ & _ & Hq2).
    unfold rules in Hq2.
    rewrite ! in_app_iff in Hq2.
    destruct Hq2 as [ Hq2 | [Hq2 | Hq2]].
    all: destruct (trans M (q_, _)) as [ [[q' w] m] | ] eqn:Etrans; try destruct m eqn:Em;
       try destruct w as [[] | ] eqn:Ew; cbn -[Nat.add] in Hq2.
    all: match type of Etrans with trans _ (_, ?c) = _ => (eapply help_exists1; exists c, q_, w, m) || exfalso end; rewrite ?Em, ?Ew; cbn [curr].
    all: repeat match type of Hq2 with _ \/ _ => destruct Hq2 as [Hq2 | Hq2] end; inversion Hq2; subst u v; clear Hq2; cbn -[Nat.add].
    all: try eapply help_exists2.

    all:
      cbn [app] in HL;
      match type of HL with
      | ?L = ?R => match L with context C [! ?q :: ?c :: ?rs] => let ls := context C [@nil nat] in 
       replace L with (ls ++ !q ++ [c] ++ rs) in HL; [ | cbn; now simpl_list]
      end
      end.

    all:
      match type of HL with _ = enc_conf (?ls,?o,?rs) ?q =>
      let H1 := fresh "H" in let H2 := fresh "H" in let H3 := fresh "H" in let H4 := fresh "H" in let HH := fresh "H" in
      eapply enc_conf_inv in HL as (H1 & -> & H3 & H4); try rewrite H4 in *; destruct o as [ [] | ]; inversion H3; clear H3; cbn in H1;
      rewrite ?app_nil_r in H1; subst;
      split ; [ eassumption | ]
      end.

    all: try now (try (destruct rs as [ | [] rs]; cbn in H3; inversion H3; subst);
    destruct x; try (now inversion H0); cbn in H0; eapply cons_inj in H0 as [HH H0]; try rewrite HH in *; clear HH; [
    destruct ls as [ | ? ls _ ] using rev_ind; cbn in H0; inversion H0;
     [ eexists [], _; split; reflexivity |
      exfalso; rewrite rev_app_distr in H0; cbn in H0; inversion H0 ] | 
   destruct ls as [ | [] ls ]; cbn in H0;
   destruct x; inversion H0; rewrite map_app in H0;
   eapply app_inj_tail in H0 as []; lia ]).


    all: try now (
      try (destruct rs as [ | [] rs]; cbn in H3; inversion H3; subst);
         destruct x; try (now inversion H0); cbn in H0; eapply cons_inj in H0 as [HH H0]; try rewrite HH in *; clear HH;
         destruct ls; cbn in H0; try (rewrite map_app in H0; eapply app_inj_tail in H0 as [H0 H1]);
         [ destruct x; inversion H0 | 
         destruct b; inversion H1 ;
         now ((eexists _, (_ :: _) + eexists _, []); split; try reflexivity;
      subst; cbn -[Nat.add]; now simpl_list)]).

   all: try now (try (destruct rs as [ | [] rs]; cbn in H3; inversion H3; subst);
     now ((eexists (_ :: ls), rs + eexists _, (_ :: _) + eexists _, [] + eexists _, _ + eexists (_ :: ls), rs); split; try reflexivity; cbn; now simpl_list)).

  Qed.

  Variable q_halt : state M.

  Definition all_symsX {B} f : list B := [f X ; f tt ; f ff].

  Definition Del := concat (all_symsX (fun c => all_syms (fun a => ([!q_halt; c ; a], [!q_halt ; c])))) ++
                    all_syms (fun a => ([a; !q_halt], [!q_halt])) ++
                    all_symsX (fun c => ( [⦇; !q_halt; c ; ⦈], [END])).

  Lemma enc_conf_equiv ls o rs q :
    enc_conf (ls, o, rs) q = ([⦇] ++ map (fun b : bool => !!b) (rev ls)) ++ ([!q] ++ [encode_sym o]) ++ (map (fun b : bool => !!b) rs ++ [⦈]).
  Proof.
    unfold enc_conf. now simpl_list.
  Qed.

  Lemma sim_Del t :
    SR.rewt Del (enc_conf t q_halt) [END].
  Proof.
    destruct t as [[ls o] rs].
    transitivity (enc_conf (ls, o, []) q_halt). {
      eapply rewt_subset. 2:{ unfold Del. eapply incl_appl. reflexivity. }
      induction rs.
      - reflexivity.
      - cbn -[Nat.add]. destruct o as [ [] | ], a; (econstructor; [ eapply do_rew; [ | | eapply enc_conf_equiv ] | eapply IHrs]).
        do 2 right; now left. reflexivity.  
        do 3 right; now left. reflexivity.
        do 4 right; now left. reflexivity.
        do 5 right; now left. reflexivity.
        do 0 right; now left. reflexivity.
        do 1 right; now left. reflexivity.
    }
    transitivity (enc_conf ([], o, []) q_halt). {
      eapply rewt_subset. 2:{ unfold Del. eapply incl_appr. eapply incl_appl. reflexivity. }
      induction ls.
      - reflexivity.
      - cbn -[Nat.add]. destruct  a; (econstructor; [ eapply do_rew; [ | | ] | eapply IHls]).
        all: cbn - [Nat.add].
        now left. cbn -[Nat.add]. simpl_list. cbn -[Nat.add]. instantiate (2 := 2 :: map (fun b : bool => !! b) (rev ls)). reflexivity. reflexivity.
        right. now left. cbn -[Nat.add]. simpl_list. cbn -[Nat.add]. instantiate (2 := 2 :: map (fun b : bool => !! b) (rev ls)). reflexivity. reflexivity.
    }
    destruct o as [ [] | ]; (
    eapply rewt_subset; [ | do 2 eapply incl_appr; reflexivity ]);
      (cbn -[Nat.add]; econstructor; [ eapply do_rew with (x := []) (y := []); simpl_list; try reflexivity; cbn; eauto | reflexivity]).
  Qed.

  Lemma rev_sim_Del t q z : 
    SR.rew Del (enc_conf t q) z -> q = q_halt /\ (z = END \/ exists t', z = enc_conf t' q_halt).
  Proof.
    intros H. inversion H as [x y v u Hin HL HR]; subst z.
    cbn -[Nat.add] in Hin.
    destruct t as [[ls o] rs].
    decompose [or] Hin; clear Hin. all: try tauto. 
    all: try specialize H0 as [= <- <-]. all: try specialize H1 as [= <- <-].
    all:
          cbn [app] in HL;
          match type of HL with
          | ?L = ?R => match L with context C [! ?q :: ?rs] => let ls := context C [@nil nat] in 
           replace L with (ls ++ !q ++ rs) in HL; [ | cbn; now simpl_list]
          end
          end; eapply enc_conf_inv' in HL as (H1 & <- & H3).
    1-6, 9-11: subst; destruct o as [ [] | ]; inversion H3; split; clear H3; try reflexivity.
    1-6, 9: destruct rs as [ | [] rs]; inversion H2; subst; rewrite app_nil_r in *.
    1-6: destruct x; inversion H1; subst.
    1-6: right; (eexists (ls, None, rs) + eexists (ls, Some true, rs) + ( eexists (ls, Some false, rs))) ; cbn -[Nat.add]; now simpl_list.
    4,5: subst; split; try reflexivity; right.
    4,5: destruct x; inversion H1; subst; clear H1; destruct ls as [ | ? ls ]; [ now destruct x; inversion H3; clear H3 |]; cbn in H3; 
        rewrite map_app in H3; cbn in H3; eapply app_inj_tail in H3 as [-> H3];
        destruct b; inversion H3; exists (ls, o, rs); cbn; now simpl_list.
    all: destruct x; inversion H1; subst; clear H1; cbn; eauto.
    1,3,5: destruct ls as [ | []]; cbn in H4; [ destruct x; inversion H4 | | ]; rewrite map_app in H4; 
      eapply app_inj_tail in H4 as [H4 [=]].
    1,2: destruct rs as [ | []]; inversion H2; eauto.
  Qed.

  Lemma rev_sim_Del_swap t q z : 
    SR.rew (map swap Del) (enc_conf t q) z -> q = q_halt /\ exists t',  z = enc_conf t' q_halt.
  Proof.
    intros H. inversion H as [x y v u Hin HL HR]; subst z.
    cbn -[Nat.add] in Hin.
    destruct t as [[ls o] rs].
    decompose [or] Hin; clear Hin. all: try tauto. 
    all: try specialize H0 as [= <- <-]. all: try specialize H1 as [= <- <-].
    1-8:
          cbn [app] in HL;
          match type of HL with
          | ?L = ?R => match L with context C [! ?q :: ?rs] => let ls := context C [@nil nat] in 
           replace L with (ls ++ !q ++ rs) in HL; [ | cbn; now simpl_list]
          end
          end; eapply enc_conf_inv' in HL as (H1 & <- & H3).
    1-6:destruct o as [ [] | ]; inversion H3; split; subst; try clear H3; try reflexivity.
    all: rewrite ?app_nil_r in *; subst.
    7,8: split; [ reflexivity | ].
    1: exists (ls, None, true :: rs).
    2: exists (ls, None, false :: rs).
    3: exists (ls, Some true, true :: rs).
    4: exists (ls, Some true, false :: rs).
    5: exists (ls, Some false, true :: rs).
    6: exists (ls, Some false, false :: rs).
    1-6: cbn -[Nat.add]; now simpl_list.
    1: exists (true :: ls, o, rs); cbn; now simpl_list.
    1: exists (false :: ls, o, rs); cbn; now simpl_list.
    all: edestruct enc_conf_END; rewrite <- HL; eauto.
  Qed.

  Lemma rev_sim_END z :
    ~ SR.rew (R ++ map swap R) [END] z.
  Proof.
    intros H. inversion H as [x y v u Hin HL HR]; subst z.
    eapply in_app_iff in Hin as [Hin | Hin].
    2: eapply in_map_iff in Hin as ([] & [= -> ->] & Hin).
    all: eapply in_flat_map in Hin as (q_ & _ & Hq2).
    all: unfold rules in Hq2.
    all: rewrite ! in_app_iff in Hq2.
    all: destruct Hq2 as [Hq2 | [Hq2 | Hq2]].
      all: destruct (trans M (q_, _)) as [ [[q' w] m] | ] eqn:Etrans; try destruct m eqn:Em;
       try destruct w as [[] | ] eqn:Ew; cbn -[Nat.add] in Hq2; decompose [or] Hq2.
      all: try specialize H0 as [= <- <-]. all: try specialize H1 as [= <- <-].
      all: try now destruct x as [ | ? []]; inversion HL.
  Qed.

End FixM.

Lemma rew_app_inv (R1 R2 : SR.SRS nat) x y :
  SR.rew (R1 ++ R2) x y <-> SR.rew R1 x y \/ SR.rew R2 x y.
Proof.
  split.
  - inversion 1 as [x0 y0 u v H0]; subst; eapply in_app_iff in H0 as [H0 | H0].
    + left. econstructor. eauto.
    + right. econstructor. eauto.
  - intros [H | H]; eapply rew_subset; eauto.
Qed.

Lemma backwards M t q1 q:
  (forall c, trans M (q,c) = None /\ (forall q', trans M (q', c) = None -> q' = q)) ->
  SR.rewt ((R M ++ Del q) ++ map SR.swap (R M ++ Del q)) (enc_conf t q1) [0] -> exists t', eval M q1 t q t'. 
Proof.
  intros Hq H. revert Hq. remember [0] as x. remember (enc_conf t q1) as y.
  induction H in q1, Heqy, Heqx, t |- *; subst; intros Hq.
  + edestruct enc_conf_END. rewrite <- Heqy. eauto.
  + rewrite map_app in H. rewrite !rew_app_inv in H. destruct H as [[H | H] | [H | H]].
    * eapply rev_sim in H as (q' & w & m & H1 & H3). subst.
      edestruct IHrewt as (H4 & H5); [reflexivity | eauto | eauto |].
      eexists. econstructor. all: eassumption.
    * eapply rev_sim_Del in H as [-> [H | (t' & ->)]].
      -- do 2 econstructor. eapply Hq.
      -- econstructor. econstructor. eapply Hq.
    * eapply rev_sim_swap in H as (q' & w & m & t' & H1 & H3 & H4). subst. 
      edestruct IHrewt as (H4 & H5); [reflexivity | eauto | eauto |].
      inversion H5; subst; clear H5; try congruence.
      rewrite H in H1. inversion H1; subst; clear H1.
      eexists. eassumption.
    * eapply rev_sim_Del_swap in H as [ -> (t' & ->)].
      do 2 econstructor. eapply Hq.
Qed.

Lemma reduction :
    HaltSBTMu ⪯ SR.TSR.
Proof.
    unshelve eexists. { intros [(M & q & H) t]. exact (R M ++ (Del q), @enc_conf M t Fin.F1, [0]). }
    intros [(M & q & Hq) t]. split.
    - cbn -[Del R enc_state]. intros (t' & H).
      etransitivity. 
      + eapply rewt_subset. eapply simulation. eassumption. eauto.
      + eapply rewt_subset. eapply sim_Del. eauto.
    - cbn -[Del R Nat.add]. intros H1. now eapply (backwards Hq).
Qed.