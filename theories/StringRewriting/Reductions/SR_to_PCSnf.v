Require Import List.
Import ListNotations.

Require Import Undecidability.StringRewriting.PCSnf.
Require Import Undecidability.StringRewriting.SR.
Require Import Undecidability.StringRewriting.Util.Definitions.
Require Import Undecidability.Shared.ListAutomation.
Import ListAutomationInstances ListAutomationHints.

Lemma derv_trans X R x y z :
    @derv X R x y -> derv R y z -> derv R x z.
Proof.
  induction 1.
  - eauto.
  - intros. econstructor; eauto.
Qed.

Section fix_R.

    Variable R : SRS nat.

    Variables x0 y0 : list nat.
    Definition Σ := x0 ++ y0 ++ sym R.

    Notation "#" := (fresh Σ).

    Definition R' := R ++ map (fun a => ([a], [a])) (# :: Σ).

    Lemma copy u v :
      incl u Σ ->
      derv R' (u ++ v) (v ++ u).
    Proof.
      intros Hu. induction u in v, Hu |- *; cbn.
      - simpl_list. constructor.
      - replace (a :: u ++ v) with ([a] ++ (u ++ v)) by reflexivity.
        replace (v ++ rev u ++ [a]) with ((v ++ rev u) ++ [a]) by now simpl_list.
        econstructor. constructor. eapply in_app_iff. right. eapply in_map_iff. eauto.
        simpl_list.
        replace (v ++ a :: u) with ((v ++ [a]) ++ u) by now simpl_list.
        eapply IHu. eauto.
    Qed. 

    Lemma correct1 x y :
      incl x Σ -> incl y Σ ->
      SR (R, x, y) -> PCSnf (R', x ++ [#], y ++ [#]).
    Proof.
      intros Hx Hy. cbn. induction 1 as [ | x' y'].
      - constructor.
      - inversion H as [ x y u v H1 H2 H3 ]; subst x' y'. simpl_list.
        eapply derv_trans. 1: eapply copy; eauto.
        simpl_list. econstructor. { econstructor. eapply in_app_iff. eauto. }
        simpl_list. eapply derv_trans. 1: eapply copy; eauto.
        simpl_list. econstructor. { econstructor. eapply in_app_iff. eauto. }
        eapply IHrewt; [ | eauto]. eapply incl_app; [ eauto | ]. eapply incl_app; [ | eauto ].
        unfold Σ. eauto.
    Qed.

    Lemma use_fresh {Σ} x : incl x Σ -> ~ In (fresh Σ) x.
    Proof.
      now intros H ? % H % fresh_spec.
    Qed.

    Hint Unfold Σ : core.

    Lemma correct2 x1 x2 y1 y2 :
      incl x1 Σ -> incl x2 Σ -> incl y1 Σ -> incl y2 Σ ->
      PCSnf (R', x2 ++ [#] ++ x1, y2 ++ [#] ++ y1) -> SR (R, x1 ++ x2, y1 ++ y2).
    Proof.
      intros Hx1 Hx2 Hy1 Hy2.
      remember (x2 ++ [#] ++ x1) as x.
      remember (y2 ++ [#] ++ y1) as y.
      induction 1 in x1, x2, y1, y2, Heqx, Heqy, Hx1, Hx2, Hy1, Hy2; subst.
      - eapply list_prefix_inv in Heqy as [-> -> ]. econstructor. unfold Σ in *. 
        + now intros ? % Hx2 % fresh_spec.
        + now intros ? % Hy2 % fresh_spec.
      - inversion H as [x u v [H2 | (a & Ha & H2) % in_map_iff] % in_app_iff H1 H3]; subst y.
        + assert (In # x) as Hx. {
            assert (In # (x2 ++ # :: x1)) as Hf by eauto.
            rewrite <- H1 in Hf. eapply in_app_iff in Hf as [ | ]; [ | now eauto].
            eapply sym_word_l in H3; eauto. exfalso.
            eapply fresh_spec with (l := Σ). 2:reflexivity. unfold Σ at 2. eauto.
          }
          eapply in_split in Hx as (x1_ & x2_ & ->).
          replace (u ++ x1_ ++ # :: x2_) with ((u ++ x1_) ++ [#] ++ x2_) in H1 by now simpl_list.
          eapply list_prefix_inv in H1 as (<- & ->).
          * econstructor. econstructor. eauto.
            replace (x1 ++ v ++ x1_) with ((x1 ++ v) ++ x1_) by now simpl_list.
            eapply IHderv.
            -- eapply incl_app. eauto. unfold Σ. eauto.
            -- etransitivity; eauto.
            -- eauto.
            -- eauto.
            -- now simpl_list.
            -- now simpl_list.
          * eapply use_fresh. eapply incl_app. unfold Σ. eauto. eapply list_prefix_inv'' in H1 as [<- <-].
            2: eapply use_fresh; eauto. 2: eapply use_fresh; eauto.
            etransitivity; eauto.
          * eapply use_fresh. eauto.
        + inversion Ha; subst; clear Ha. destruct H2 as [<- | H2].
          * eapply list_prefix_inv with (x := []) in H1 as [<- <-]; [ | firstorder | now eapply use_fresh].
            simpl_list. cbn in H.
            eapply (IHderv []); [ eauto .. | now simpl_list ].
          *  assert (In # x) as Hx. {
              assert (In # (x2 ++ # :: x1)) as Hf by eauto.
              rewrite <- H1 in Hf. eapply in_app_iff in Hf as [ | ]; [ | now eauto].
              exfalso. destruct H3 as [-> | []]. eapply fresh_spec with (l := Σ); eauto.
            }
            eapply in_split in Hx as (x1_ & x2_ & ->).
            replace ([a] ++ x1_ ++ # :: x2_) with (([a] ++ x1_) ++ [#] ++ x2_) in H1 by now simpl_list.
            eapply list_prefix_inv in H1 as (<- & ->).
            -- replace (x1 ++ [a] ++ x1_) with ((x1 ++ [a]) ++ x1_) by now simpl_list.
               eapply IHderv.
               ++ eapply incl_app. eauto. eauto.
               ++ etransitivity; eauto.
               ++ eauto.
               ++ eauto.
               ++ now simpl_list.
               ++ now simpl_list.
            -- eapply use_fresh. eapply incl_app. eauto. eapply list_prefix_inv'' in H1 as [<- <-].
               2: eapply use_fresh; eauto. 2: eapply use_fresh; eauto.
               etransitivity; eauto.
            -- eapply use_fresh. eauto.
    Qed.

End fix_R.

Require Import Undecidability.Synthetic.Definitions.

Lemma reduction :
  SR ⪯ PCSnf.
Proof.
  exists (fun '(R,x,y) => (R' R x y, x ++ fresh (Σ R x y), y ++ fresh (Σ R x y))).
  intros [[R x] y]. split.
  - eapply correct1; unfold Σ; eauto.
  - intros. eapply correct2 with (x0 := x) (y0 := y) (x1 := []) (y1 := []).
    1-4: unfold Σ; eauto. now simpl_list.
Qed.
