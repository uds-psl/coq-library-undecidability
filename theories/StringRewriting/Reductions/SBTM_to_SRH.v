Require Import List Lia.

Require Import Undecidability.TM.SBTM.
Require Import Undecidability.TM.Reductions.HaltSBTM_to_HaltSBTMuniq.

Require Undecidability.StringRewriting.SR.
Require Import Undecidability.StringRewriting.Util.Definitions.
Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts.

Import ListNotations.

Lemma nil_app_tail {X} (x : X) l : ~ [] = l ++ [x]. destruct l; cbn; firstorder congruence. Qed.
Lemma nil_app_tail' {X} (x : X) l : ~ l ++ [x] = []. destruct l; cbn; firstorder congruence. Qed.

Definition SRH' '(Rs, x, A) := exists y : list nat, SR.rewt Rs x y /\ exists a, In a A /\ In a y.

Section FixM.

    Variable M : SBTM.

    Notation X := 0.
    Notation "⦇" := 1.
    Notation "⦈" := 2.
    Notation tt := 3.
    Notation ff := 4.
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
        | Some (q₁, q₂, X, Rmove) => all_syms (fun r => ([q₁;X;r], [q₂;r])) ++ [([q₁;X;⦈],[q₂;X;⦈])]
        | Some (q₁, q₂, X, Nmove) => [([q₁;X], [q₂;X])]
        | Some (q₁, q₂, c, Lmove) => all_syms (fun l => ([l;q₁;X], [q₂;l;c])) ++ [([⦇;q₁;X],[⦇;q₂;X;c])]
        | Some (q₁, q₂, c, Rmove) => all_syms (fun r => ([q₁;X;r], [c;q₂;r])) ++ [([q₁;X;⦈],[c;q₂;X;⦈])]
        | Some (q₁, q₂, c, Nmove) => [([q₁;X], [q₂;c])]
        | None => []
        end ++
        let a := tt in
        match encode_trans (trans M (q₁, Some true)) q₁ with
        | Some (q₁, q₂, X, Lmove) => all_syms (fun l => ([l;q₁;a], [q₂;l;a])) ++ [([⦇;q₁;a],[⦇;q₂;X;a])]
        | Some (q₁, q₂, X, Rmove) => all_syms (fun r => ([q₁;a;r], [a;q₂;r])) ++ [([q₁;a;⦈],[a;q₂;X;⦈])]
        | Some (q₁, q₂, X, Nmove) => [([q₁;a], [q₂;a])]
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

    Lemma enc_conf_inv xs q c ys ls o rs q' :
      xs ++ !q ++ [c] ++ ys = enc_conf (ls, o, rs) q' ->
      xs = [⦇] ++ map (fun b : bool => !!b) (rev ls) /\
      q = q' /\
      c = encode_sym o /\
      ys = map (fun b : bool => !!b) rs ++ [⦈].
    Proof.
      intros. pose proof (H' := H). cbn - [Nat.add] in H.
      destruct xs; cbn -[Nat.add] in H; inversion H; subst n; clear H.

      eapply list_prefix_inv in H2 as (H1 & -> & H3).
      - inversion H3; subst; clear H3; repeat split. eapply Fin.to_nat_inj. unfold "!" in H1. lia.
      - clear H'. induction xs in ls, H2 |- *.
        + firstorder.
        + cbn -[Nat.add]. destruct ls as [ | ? ? _] using rev_ind.
          * cbn -[Nat.add] in H2. inversion H2. subst. destruct xs; inversion H1; subst.
            destruct o as [ [] | ]; cbn in H0; lia.
            assert (In (!q) (map (fun b : bool => !! b) rs ++ [2])). rewrite <- H3. rewrite in_app_iff. cbn[In]. eauto.
            eapply in_app_iff in H as [ (? & ? & ?) % in_map_iff | [ | []]]; try destruct x; cbn in H; lia.
          * rewrite rev_app_distr in H2. cbn -[Nat.add] in H2. inversion H2; subst.
            intros [ | ].
            -- destruct x; cbn in *; lia.
            -- eapply IHxs. 2:eauto. rewrite H1. reflexivity.
      - intros (? & ? & ?) % in_map_iff. destruct x; cbn in *; lia.
    Qed.

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

  Lemma enc_state_inv q t q' :
    In (enc_state q) (enc_conf t q') -> q = q'.
  Proof.
    destruct t as [[ls o] rs].
    unfold enc_conf.
    rewrite !in_app_iff, !in_map_iff; repeat setoid_rewrite <- in_rev. cbn. firstorder try lia.
    all: try (destruct x; lia). eapply Fin.to_nat_inj. lia. destruct o as [[]|]; cbn in *; lia.
  Qed.

End FixM.

Lemma reduction :
    HaltSBTMuniq ⪯ SR.SRH.
Proof.
    unshelve eexists. { intros [ [[M q] H] t ]. exact (R M, @enc_conf M t Fin.F1, enc_state q). }
    intros [[[M q] Hq] t]. split.
    - cbn -[enc_state]. intros (t' & H).
      exists (enc_conf t' q). split.
      + now eapply simulation. 
      + destruct t' as [[ls o] rs].
        cbn -[Nat.add]. right. rewrite !in_app_iff. cbn; eauto.
    - cbn -[R Nat.add]. intros (x & H1 & H2). revert H1.
      generalize (@Fin.F1 (num_states M)). intros q1 H.
      revert q Hq H2. remember (enc_conf t q1) as y.
      induction H in q1, Heqy, t |- *; subst; intros q Hq H2.
      + exists t. eapply enc_state_inv in H2. subst. econstructor. eapply Hq.
      + eapply rev_sim in H as (q' & w & m & H1 & H3). subst.
        edestruct IHrewt as (H4 & H5). reflexivity. eauto. eauto. eexists. econstructor. 2:eassumption.
        eassumption.
Qed.