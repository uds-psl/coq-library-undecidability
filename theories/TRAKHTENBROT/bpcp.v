(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

Set Implicit Arguments.

Section dec.

  Variable (X : Type) (eqX_dec : forall x y : X, { x = y } + { x <> y }).

  Fact is_a_head_dec (l t : list X) : { x | l = t++x } + { ~ exists x, l = t++x }.
  Proof.
    revert t.
    induction l as [ | a l IHl ].
    + intros [ | t ]. 
      * left; exists nil; auto.
      * right; intros ([ | ] & ?); discriminate.
    + intros [ | b t ].
      * left; exists (a::l); auto.
      * destruct (eqX_dec a b) as [ -> | C ].
        - destruct (IHl t) as [ H | C ].
          ++ left; destruct H as (x & ->).
              exists x; auto.
          ++ right; contradict C; destruct C as (x & E).
             exists x; inversion E; subst; auto.
        - right; contradict C; destruct C as (? & E); inversion E; auto.
  Qed.
 
  Fact is_a_tail_dec (l t : list X) : { exists x, x++t = l } + { ~ exists x, x++t = l }.
  Proof.
    destruct (is_a_head_dec (rev l) (rev t)) as [ H | H ].
    + left; destruct H as (x & Hx).
      exists (rev x).
      apply f_equal with (f := @rev _) in Hx.
      rewrite rev_app_distr in Hx.
      do 2 rewrite rev_involutive in Hx; auto.
    + right; contradict H.
      destruct H as (x & Hx); exists (rev x); subst.
      apply rev_app_distr.
  Qed.

End dec.

Section pcp_hand.

  Variable (X : Type) (lc : list (list X * list X)).

  Inductive pcp_hand : list X -> list X -> Prop :=
    | in_pcph_0 : forall x y, In (x,y) lc -> pcp_hand x y
    | in_pcph_1 : forall x y u l, In (x,y) lc -> pcp_hand u l -> pcp_hand (x++u) (y++l).

  (** Any hand is either a card or of the for x++p/y++q where
      x/y is a non-void card and p/q is a hand *)

  Lemma pcp_hand_inv p q : 
       pcp_hand p q -> In (p,q) lc 
                    \/ exists x y p' q', In (x,y) lc /\ pcp_hand p' q' 
                                      /\ p = x++p' /\ q = y++q' 
                        /\  (x <> nil /\ y = nil  
                          \/ x = nil /\ y <> nil
                          \/ x <> nil /\ y <> nil ).
  Proof.
    induction 1 as [ x y H | x y p q H1 H2 IH2 ].
    + left; auto. 
    + destruct x as [ | a x ]; [ destruct y as [ | b y ] | ].
      * simpl; auto.
      * right; exists nil, (b::y), p, q; simpl; msplit 4; auto.
        right; left; split; auto; discriminate.
      * right; exists (a::x), y, p, q; simpl; msplit 4; auto.
        destruct y.
        - left; split; auto; discriminate.
        - right; right; split; discriminate.
  Qed.

  Definition PCP := exists l, pcp_hand l l.

  Section pcp_induction.

    Implicit Type (l m : list X).

    (** Notice that we could downgrade strict_suffix to Prop because
        a and b could be computed from the knowledge of there existence *)

    Definition strict_suffix x y l m := { a : _ & { b | (a <> nil \/ b <> nil) /\ l = a++x /\ m = b++y } }.
    
    Variable (P : list X -> list X -> Type)
             (IHP : forall l m, (forall l' m', strict_suffix l' m' l m -> P l' m') -> P l m).

    Theorem pcp_induction l m : P l m.
    Proof.
      induction on l m as IH with measure (length l + length m).
      apply IHP.
      intros l' m' (x & y & H & -> & ->).
      apply IH.
      do 2 rewrite app_length.
      destruct x; destruct y; simpl; try lia.
      destruct H as [ [] | [] ]; auto.
    Qed.

  End pcp_induction.
    
  Section bounded_dec.

    (** It is possible to decide pcp_hand, when equality is decidable
        of course *)
  
    Variable eqX_dec : forall x y : X, { x = y } + { x <> y }.

    Let eqlX_dec : forall l m : list X, { l = m } + { l <> m }.
    Proof. apply list_eq_dec; auto. Qed.

    Let eqXX_dec : forall p q : list X * list X, { p = q } + { p <> q }.
    Proof. decide equality; auto. Qed.

    (** Replaced induction on length p + length with strict suffix pair induction *)

    Theorem pcp_hand_dec p q : { pcp_hand p q } + { ~ pcp_hand p q }.
    Proof.
      revert p q; apply pcp_induction; intros p q dec.

      set (P (c : list X * list X) := let (x,y) := c 
           in exists d, p = x++fst d /\ q = y++snd d /\ pcp_hand (fst d) (snd d) /\ (x <> nil \/ y <> nil)).
      assert (forall c, { P c } + { ~ P c }) as Pdec.
      { intros (x,y); simpl.
        assert ( { x = nil /\ y = nil } + { x <> nil \/ y <> nil } ) as H.
        1: { destruct (eqlX_dec x nil); destruct (eqlX_dec y nil); tauto. }
        destruct H as [ (H1 & H2) | Hxy ].
        1: { right; intros ((? & ?) & ?); tauto. }
        destruct (is_a_head_dec eqX_dec p x) as [ (p' & Hp') | Hp ].
        2: { right; contradict Hp; revert Hp. 
             intros ((p',?) & E & _); exists p'; auto. }
        destruct (is_a_head_dec eqX_dec q y) as [ (q' & Hq') | Hq ].
        2: { right; contradict Hq; revert Hq. 
             intros ((?,q') & _ & E & _); exists q'; auto. }
        destruct (dec p' q') as [ H' | H' ].
        + exists x, y; auto.
        + left; exists (p',q'); auto.
        + right; contradict H'; revert H'.
          intros ((u,v) & -> & -> & C & _); simpl in *.
          apply app_inv_head in Hp'.
          apply app_inv_head in Hq'.
          subst; auto. }

      destruct list_dec with (1 := Pdec) (l := lc)
        as [ ((x,y) & H1 & H) | H ]; unfold P in H.
      + left.
        destruct H as ((p',q') & -> & -> & H & _); simpl in *.
        constructor 2; auto.
      + destruct In_dec with (1 := eqXX_dec) (a := (p,q)) (l := lc)
          as [ H2 | H2 ].
        * left; constructor 1; auto.
        * right; contradict H2.
          apply pcp_hand_inv in H2.
          destruct H2 as [ | (x & y & p' & q' & H2 & H3 & -> & -> & H4) ]; auto.
          destruct H with (1 := H2).
          exists (p', q'); msplit 3; tauto.
    Qed.

  End bounded_dec.

End pcp_hand.

