Require Import List Lia.

Require Import Undecidability.TM.SBTM.

Require Undecidability.StringRewriting.SR.
Require Import Undecidability.StringRewriting.Util.Definitions.
Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts.
Require Import Undecidability.StringRewriting.Reductions.HaltSBTMu_to_SRH.

Import ListNotations.

Section FixM.

  Variable M : SBTM.  
  Notation END := 0.
  Notation X := 1.
  Notation "⦇" := 2.
  Notation "⦈" := 3.
  Notation tt := 4.
  Notation ff := 5.
  Notation "!! b" := (if b then tt else ff) (at level 1).
  Notation "! p" := (@enc_state M p) (at level 1).

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
    SR.rew (map SR.swap (R M)) (enc_conf t q) z -> exists q' t' w m, trans M (q', curr t') = Some (q, w, m) /\ t = mv m (wr w t') /\ z = enc_conf t' q'.
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
  
  Lemma enc_conf_END t q : ~ In END (@enc_conf M t q).
  Proof.
    destruct t as [[ls o] rs].
    unfold enc_conf.
    rewrite !in_app_iff, !in_map_iff; repeat setoid_rewrite <- in_rev. cbn.
    intros H. decompose [or] H; try lia; firstorder; try lia.
    all: try (destruct x; lia). destruct o as [[]|]; cbn in *; lia.
  Qed.
  
  Lemma rev_sim_Del_swap t q z : 
    SR.rew (map SR.swap Del) (enc_conf t q) z -> q = q_halt /\ exists t',  z = enc_conf t' q_halt.
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

End FixM.

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