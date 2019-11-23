(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Eqdep_dec Bool.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos fin_quotient.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops membership hfs.

Set Implicit Arguments.

Section bt_model3.

  (** This discussion briefly describes how we encode finite and discrete 
      model X with a computable ternary relation R into an hereditary finite 
      set (hfs) with to elements l and r, l representing the points in X
      and r representing the triples in R.

      Because X is finite and discrete, one can compute a bijection X <~> pos n
      where n is the cardinal of X. Hence we assume that X = pos n and the
      ternary relation is R : pos n -> pos n -> pos n -> Prop
      
      1) We find a transitive hfs l such that pos n bijects with the elements
         of l (transitive means ∀x, x∈l -> x⊆l). Hence

                            pos n <-> { x | x ∈ l } 

         For this, we use the encoding of natural numbers into sets, 
         ie 0 := ø and 1+i := {i} U i and choose l to be the encoding 
         of n (the cardinal of X=pos n above).

         Notice that since l is transitive then so is P(l) (powerset)
         and hence P^i(l) for any i.
    
      2) forall x,y ∈ l, both {x} and {x,y} belong to P(l) 
         hence (x,y) = {{x},{x,y}} ∈ P(P(l))=P^2(l)
        
      3) Hence P^4(l) = P^2(P^2(l)) contains all ordered triples
         build from the elements of l. 

      5) So we can encode R as hfs r ∈ p := P^5(l) = P(P^4(l)) and
         p serves as our model, ie 

                      Y := { x : hfs | x ∈b p } 

         where x ∈b p is the Boolean encoding of x ∈ p to ensure 
         uniqueness of witnesses/proofs.
         
      6) In the logic, we replace any 
      
               R (x1,x2,x3) by ((x1,x2),x3) ∈ r

         encoded according to the above description.

      *)

  (** We have computed the transitive closure, spec'ed and proved finite *)  

  Variable (X : Type) (Xfin : finite_t X) (Xdiscr : discrete X) (x0 : X).

  Infix "∈" := hfs_mem.
  Notation "x ⊆ y" := (forall u, u ∈ x -> u ∈ y).
  Notation "⟬ x , y ⟭" := (hfs_opair x y).

  Let X_surj_hfs : { l : hfs & { f : hfs -> X & 
                    { g : X -> hfs |
                      hfs_transitive l
                   /\ (forall p, g p ∈ l)
                   /\ (forall x, x ∈ l -> exists p, x = g p)
                   /\ (forall p, f (g p) = p) } } }.
  Proof.
    destruct (finite_t_discrete_bij_t_pos Xfin)
      as ([ | n ] & Hn); auto.
    1: { exfalso; destruct Hn as (f & g & H1 & H2).
         generalize (f x0); intro p; invert pos p. }
    destruct Hn as (f & g & H1 & H2).
    destruct (hfs_pos_n_transitive n) 
      as (l & g' & f' & G1 & G2 & G3 & G4).
    exists l, (fun x => g (g' x)), (fun x => f' (f x)); msplit 3; auto.
    + intros x Hx.
      destruct (G3 x Hx) as (p & Hp).
      exists (g p); rewrite H2; auto.
    + intros p; rewrite G4; auto.
  Qed.

  (** First a surjective map from some transitive set l to X *)

  Let l := projT1 X_surj_hfs.
  Let s := projT1 (projT2 X_surj_hfs).
  Let i := proj1_sig (projT2 (projT2 (X_surj_hfs))).

  Let Hl : hfs_transitive l.
  Proof. apply (proj2_sig (projT2 (projT2 (X_surj_hfs)))). Qed.
  Let Hs : forall x, s (i x) = x. 
  Proof. apply (proj2_sig (projT2 (projT2 (X_surj_hfs)))). Qed.
  Let Hi : forall x, i x ∈ l. 
  Proof. apply (proj2_sig (projT2 (projT2 (X_surj_hfs)))). Qed.
  Let Hi' : forall s, s ∈ l -> exists x, s = i x.
  Proof. apply (proj2_sig (projT2 (projT2 (X_surj_hfs)))). Qed.

  (** Now we build P^5 l that contains all the set of triples of l *)

  Let p := iter hfs_pow l 5.

  Let Hp1 : hfs_transitive p.
  Proof. apply hfs_iter_pow_trans; auto. Qed.

  Let Hp2 : l ∈ p.
  Proof.
    apply hfs_iter_pow_le with (n := 1); simpl; auto.
    apply hfs_pow_spec; auto.
  Qed.

  Let Hp3 x y : x ∈ l -> y ∈ l -> ⟬x,y⟭  ∈ iter hfs_pow l 2.
  Proof.
    intros Hx Hy.
    do 2 apply hfs_pair_pow; auto.
  Qed.

  Let Hp4 x y : x ∈ l -> y ∈ l -> ⟬x,y⟭  ∈ p.
  Proof.
    intros Hx Hy.
    generalize (Hp3 Hx Hy).
    apply hfs_iter_pow_le; auto.
  Qed.
   
  Let Hp5 x y z : x ∈ l -> y ∈ l -> z ∈ l -> ⟬⟬x,y⟭,z⟭  ∈ iter hfs_pow l 4.
  Proof.
    intros Hx Hy Hz.
    repeat apply hfs_pair_pow; auto.
    apply hfs_iter_pow_le with (n := 0) (m := 2); auto.
  Qed.

  Let Hp6 x y z : x ∈ l -> y ∈ l -> z ∈ l -> ⟬⟬x,y⟭,z⟭  ∈ p.
  Proof.
    intros Hx Hy Hz.
    generalize (Hp5 Hx Hy Hz).
    apply hfs_iter_pow_le; auto.
  Qed.

  Variable (R : X -> X -> X -> Prop).
  Hypothesis HR : forall x y z, { R x y z } + { ~ R x y z }.

  Hint Resolve finite_t_prod hfs_mem_fin_t.

  (** We encode R as a subset of triples of elements of l in p *)

  Let encode_R : { r | r ∈ p 
                      /\ (forall a b c, ⟬⟬a,b⟭,c⟭  ∈ r -> a ∈ l /\ b ∈ l /\ c ∈ l)
                      /\ forall x y z, R x y z <-> ⟬⟬i x,i y⟭,i z⟭  ∈ r }.
  Proof.
    set (P t := let a := fst (fst t) in
                let b := snd (fst t) in
                let c := snd t
                in R (s a) (s b) (s c) /\ ((a ∈ l /\ b ∈ l) /\ c ∈ l)).
    set (f t := match t with ((a,b),c) => ⟬⟬a,b⟭,c⟭  end).
    destruct hfs_comprehension with (P := P) (f := f) as (r & Hr).
    + apply fin_t_dec.
      * intros; apply HR.
      * apply fin_t_prod with (P := fun t => fst t ∈ l /\ snd t ∈ l) (Q := fun x => x ∈ l); auto.
        apply fin_t_prod with (P := fun x => x ∈ l) (Q := fun x => x ∈ l); auto.
    + exists r; msplit 2.
      * apply hfs_pow_spec; intros x; rewrite Hr.
        intros (((a,b),c) & (H1 & (H2 & H3) & H4) & <-).
        unfold f; apply Hp5; auto.
      * intros a b c; rewrite Hr.
        intros (((a',b'),c') & H1 & H2).
        unfold f in H2.
        do 2 rewrite hfs_opair_spec in H2.
        destruct H2 as ((->&->)&->); auto.
        red in H1; simpl in H1; tauto.
      * intros x y z; split.
        - intros H.
          apply Hr.
          exists (i x,i y, i z); simpl; split; auto.
          split; simpl; auto.
          repeat rewrite Hs; auto.
        - rewrite Hr; intros (((x',y'),z') & H1 & H2).
          unfold f in H2.
          do 2 rewrite hfs_opair_spec in H2.
          destruct H2 as ((->&->)&->); auto.
          apply proj1 in H1; simpl in H1.
          revert H1; repeat rewrite Hs; auto.
  Qed.

  Let r := proj1_sig encode_R.
  
  Let Hr1 : r ∈ p.
  Proof. apply (proj2_sig encode_R). Qed.

  Let Hr2 : forall a b c, ⟬⟬a,b⟭,c⟭  ∈ r -> a ∈ l /\ b ∈ l /\ c ∈ l.
  Proof. apply (proj2_sig encode_R). Qed.

  Let Hr3 x y z : R x y z <->  ⟬⟬i x,i y⟭,i z⟭  ∈ r.
  Proof. apply (proj2_sig encode_R). Qed.

  (** The Boolean encoding of x ∈ p *)

  Let p_bool x := if hfs_mem_dec x p then true else false.

  Let p_bool_spec x : x ∈ p <-> p_bool x = true.
  Proof.   
    unfold p_bool.
    destruct (hfs_mem_dec x p); split; try tauto; discriminate.
  Qed.

  Let Y := sig (fun x => p_bool x = true).

  Let eqY : forall x y : Y, proj1_sig x = proj1_sig y -> x = y.
  Proof. 
    intros (x & Hx) (y & Hy); simpl.
    intros; subst; f_equal; apply UIP_dec, bool_dec.
  Qed.

  Let HY : finite_t Y.
  Proof. 
    apply fin_t_finite_t.
    + intros; apply UIP_dec, bool_dec.
    + generalize (hfs_mem_fin_t p); apply fin_t_equiv.
      intros x; auto.
  Qed.

  Let discrY : discrete Y.
  Proof.
    intros (x & Hx) (y & Hy).
    destruct (hfs_eq_dec x y) as [ -> | D ].
    + left; f_equal; apply UIP_dec, bool_dec.
    + right; contradict D; inversion D; auto.
  Qed.

  Let mem (x y : Y) := proj1_sig x ∈ proj1_sig y.

  Let mem_dec : forall x y, { mem x y } + { ~ mem x y }.
  Proof.
    intros (a & ?) (b & ?); unfold mem; simpl; apply hfs_mem_dec.
  Qed.

  Let yl : Y.    Proof. exists l; apply p_bool_spec, Hp2. Defined.
  Let yr : Y.    Proof. exists r; apply p_bool_spec, Hr1. Defined.

  (** Membership equivalence is identity in the model *)

  Let is_equiv : forall x y, m2_equiv mem x y <-> proj1_sig x = proj1_sig y.
  Proof.
    intros (x & Hx) (y & Hy); simpl.
    unfold m2_equiv, mem; simpl; split.
    2: intros []; tauto.
    intros H.
    apply hfs_mem_ext.
    intros z; split; intros Hz.
    * apply p_bool_spec in Hx.
      generalize (Hp1 Hz Hx).
      rewrite p_bool_spec; intros H'.
      apply (H (exist _ z H')); auto.
    * apply p_bool_spec in Hy.
      generalize (Hp1 Hz Hy).
      rewrite p_bool_spec; intros H'.
      apply (H (exist _ z H')); auto.
  Qed.

  Let is_pair : forall x y k, m2_is_pair mem k x y 
                          <-> proj1_sig k = hfs_pair (proj1_sig x) (proj1_sig y).
  Proof.
    intros (x & Hx) (y & Hy) (k & Hk); simpl.
    unfold m2_is_pair; simpl; rewrite hfs_mem_ext.
    generalize Hx Hy Hk; revert Hx Hy Hk.
    do 3 rewrite <- p_bool_spec at 1.
    intros Hx' Hy' Hk' Hx Hy Hk.
    split.
    + intros H a; split; rewrite hfs_pair_spec; [ intros Ha | intros [ Ha | Ha ] ].
      * generalize (Hp1 Ha Hk'); rewrite p_bool_spec; intros Ha'.
        specialize (H (exist _ a Ha')); simpl in H.
        repeat rewrite is_equiv in H; apply H; auto.
      * subst; apply (H (exist _ x Hx)); repeat rewrite is_equiv; simpl; auto.
      * subst; apply (H (exist _ y Hy)); repeat rewrite is_equiv; simpl; auto.
    + intros H (a & Ha); repeat rewrite is_equiv; simpl; rewrite <- hfs_pair_spec.
      apply H.
  Qed.
 
  Let is_opair : forall x y k, m2_is_opair mem k x y 
                              <-> proj1_sig k = ⟬proj1_sig x,proj1_sig y⟭.
  Proof.
    intros (x & Hx) (y & Hy) (k & Hk); simpl.
    unfold m2_is_opair; split.
    + intros ((a & Ha) & (b & Hb) & H); revert H.
      repeat rewrite is_pair; simpl.
      intros (-> & -> & ->); auto.
    + intros ->.
      generalize Hx Hy Hk; revert Hx Hy Hk.
      do 3 rewrite <- p_bool_spec at 1.
      intros Hx' Hy' Hk' Hx Hy Hk.
      apply hfs_trans_opair_inv in Hk'; auto.
      do 2 rewrite p_bool_spec in Hk'.
      destruct Hk' as (H1 & H2).
      exists (exist _ (hfs_pair x x) H1).
      exists (exist _ (hfs_pair x y) H2).
      repeat rewrite is_pair; simpl; auto.
  Qed.

  Let is_otriple : forall x y z k, m2_is_otriple mem k x y z 
                               <-> proj1_sig k = ⟬⟬proj1_sig x,proj1_sig y⟭ ,proj1_sig z⟭.
  Proof. 
    intros (x & Hx) (y & Hy) (z & Hz) (k & Hk); simpl.
    unfold m2_is_otriple. split.
    + intros ((a & Ha) & H); revert H.
      repeat rewrite is_opair; simpl.
      intros (-> & ->); auto.
    + intros ->.
      generalize Hk; revert Hk.
      rewrite <- p_bool_spec at 1.
      intros Hk' Hk.
      apply hfs_trans_otriple_inv, proj1 in Hk'; auto.
      rewrite p_bool_spec in Hk'.
      exists (exist _ (⟬x,y⟭) Hk').
      repeat rewrite is_opair; simpl; auto.
  Qed.

  Let has_triples : m2_has_otriples mem yl.
  Proof.
    intros (x & Hx') (y & Hy') (z & Hz'); simpl.
    intros Hx Hy Hz.
    generalize (Hp6 Hx Hy Hz); rewrite p_bool_spec; intros H1.
    exists (exist _ (⟬⟬x,y⟭,z⟭) H1).
    rewrite is_otriple; simpl; auto.
  Qed.

  Let i' : X -> Y.
  Proof.
    intros x.
    exists (i x).
    apply p_bool_spec.
    generalize (Hi x) Hp2; apply Hp1.
  Defined.

  Let Hi'' x : mem (i' x) yl.
  Proof. unfold i', yl, mem; simpl; auto. Qed.

  Let s' (y : Y) : X := s (proj1_sig y).

  (**
    For finite and discrete type X, non empty (as witnessed by a given element)
    equipped with a Boolean ternary relation R, one can compute a type Y, finite
    and discrete, equipped with a Boolean binary membership predicate ∈ which is 
    extensional. Y is a finite (set like) model which contains two sets yl and 
    yr and there is a bijection between X and (the elements of) yl. All ordered 
    triples build from elements of yl exist in Y, and yr encodes R in the set 
    of (ordered) triples it contains. 
    Finally, membership equivalence (≈) is the same as identity (=) in Y.

    Membership equivalence : x ≈ y := ∀z, z∈x <-> z∈y
    Membership extensional : x ≈ y -> ∀z, x∈z -> y∈z

    Triples are build the usual way (in set theory)
      - z ∈ {x,y} := z ≈ x \/ z ≈ y
      - ordered pairs: (x,y) is {{x},{x,y}}
      - ordered triples: (x,y,z) is ((x,y),z)

    Non-emptyness is not really necessary but then bijection between X=ø and yl
    has to be implemented with dependent functions, more cumbersome to work
    with. And first order models can never be empty because one has to be able
    to interpret variables. Maybe a discussion on the case of empty models
    could be necessary, the logic been reduced to True/False in that case.
    Any ∀ formula is True, any ∃ is False and no atomic formula can ever
    be evaluated (because it contains terms that cannot be interpreted). 
    Only closed formula have a meaning in the empty model 
  *)
  
  Local Theorem rel3_hfs : { Y : Type &
                     { _ : finite_t Y & 
                     { _ : discrete Y &
                     { mem : Y -> Y -> Prop &
                     { _ : forall u v, { mem u v } + { ~ mem u v } & 
                     { yl : Y &
                     { yr : Y & 
                     { i : X -> Y & 
                     { s : Y -> X |
                             m2_member_ext mem
                          /\ m2_has_otriples mem yl
                          /\ (forall x, mem (i x) yl)
                          /\ (forall y, mem y yl -> exists x, y = i x)
                          /\ (forall x, s (i x) = x)
                          /\ (forall a b c, R a b c <-> m2_is_otriple_in mem yr (i a) (i b) (i c))
                          /\ (forall x y, m2_equiv mem x y <-> x = y)
                      }}}}}}}}}.
  Proof.
    exists Y, HY, discrY, mem, mem_dec, yl, yr, i', s'.
    msplit 6; auto.
    + intros (u & Hu) (v & Hv) (w & Hw); unfold mem; simpl.
      unfold m2_equiv; simpl; intros H.
      cut (u = v); [ intros []; auto | ].
      apply hfs_mem_ext.
      apply p_bool_spec in Hu.
      apply p_bool_spec in Hv.
      clear w Hw.
      intros x; split; intros Hx.
      * generalize (Hp1 Hx Hu); rewrite p_bool_spec; intros H'.
        apply (H (exist _ x H')); auto.
      * generalize (Hp1 Hx Hv); rewrite p_bool_spec; intros H'.
        apply (H (exist _ x H')); auto.
    + intros y Hy; unfold i'.
      destruct (Hi' Hy) as (x & Hx).
      exists x; apply eqY; simpl; auto.
    + intros a b c; unfold m2_is_otriple_in.
      unfold m2_has_otriples in has_triples.
      destruct (has_triples (Hi'' a) (Hi'' b) (Hi'' c)) as (t & H2).
      split.
      * intros H; exists t; split; auto.
        destruct t as (t & H1); unfold yr, mem; simpl.
        rewrite is_otriple in H2; simpl in H2; subst.
        apply Hr3; auto.
      * intros ((t' & Ht') & H1 & H3).
        destruct t as (t & Ht).
        rewrite is_otriple in H2, H1.
        simpl in H1, H2.
        subst t'; unfold mem, yr in H3; simpl in H3.
        revert H3; apply Hr3.
    + intros x y; rewrite is_equiv; split; auto.
      intros; subst; auto.
  Qed.

End bt_model3.

Check rel3_hfs.
Print Assumptions rel3_hfs.
