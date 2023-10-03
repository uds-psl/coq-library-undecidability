(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import List Arith Lia Eqdep_dec Bool.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.FOL.TRAKHTENBROT
  Require Import notations decidable fol_ops membership hfs.

Set Implicit Arguments.

(* * Construction of the Hereditary Finite Sets model *)

Section bt_model_n.

  (*  This discussion briefly describes how we encode finite and discrete 
      model X with a decidable nt-ary relation R into an hereditary finite 
      set (hfs) with two elements l and r, l representing the points in X
      and r representing the n-tuples in R.

      Because X is finite and discrete, one can compute a bijection X <~> pos n
      where n is the cardinal of X. Hence we assume that X = pos n and the
      nt-art relation is R : vec (pos n) nt -> Prop
      
      1) We find a transitive hfs l such that (pos n) bijects with the elements
         of l (transitive means ∀x, x∈l -> x⊆l). Hence

                            pos n <-> { x | x ∈ l } 

         For this, we use the encoding of natural numbers into sets, 
         ie 0 := ø and 1+i := {i} U i and choose l to be the encoding 
         of n (the cardinal of X = pos n above).

         Notice that since l is transitive then so is P(l) (powerset)
         and hence P^i(l) for any i.
    
      2) forall x,y ∈ l, both {x} and {x,y} belong to P(l) 
         hence (x,y) = {{x},{x,y}} ∈ P(P(l))=P^2(l)
        
      3) l contains the empty set (cardinal > 0)
  
      4) Hence P^2nt(l) contains all nt-tuples build 
         from the elements of l by induction on n

      5) So we can encode R as hfs r ∈ p := P^(2nt+1)(l) = P(P^2nt(l)) and
         p serves as our model, ie 

                      Y := { x : hfs | x ∈b p } 

         where x ∈b p is the Boolean encoding of x ∈ p to ensure 
         uniqueness of witnesses/proofs.
         
      6) In the logic, we replace any 
      
               R v by [v] ∈ r

         encoded according to the above description.

      *)

  Variable (X : Type) (Xfin : finite_t X) (Xdiscr : discrete X) (x0 : X) (nt : nat).

  Notation "∅" := hfs_empty.
  Infix "∈" := hfs_mem.
  Notation "x ⊆ y" := (forall u, u ∈ x -> u ∈ y).
  Notation "⟬ x , y ⟭" := (hfs_opair x y).

  (* First we compute a bijection with the cardinal of X *)

  Section the_model.

    Local Definition X_surj_hfs : { d : hfs & 
                     { f : hfs -> X & 
                     { g : X -> hfs |
                        hfs_transitive d
                     /\ ∅ ∈ d
                     /\ (forall p, g p ∈ d)
                     /\ (forall x, x ∈ d -> exists p, x = g p)
                     /\ (forall p, f (g p) = p) 
                     }}}.
    Proof using x0 Xfin Xdiscr.
      destruct (finite_t_discrete_bij_t_pos Xfin)
        as ([ | n ] & Hn); auto.
      1: { exfalso; destruct Hn as (f & g & H1 & H2).
           generalize (f x0); intro p; invert pos p. }
      destruct Hn as (f & g & H1 & H2).
      destruct (hfs_pos_n_transitive n) 
        as (l & g' & f' & G1 & G0 & G2 & G3 & G4).
      exists l, (fun x => g (g' x)), (fun x => f' (f x)); msplit 4; auto.
      + intros x Hx.
        destruct (G3 x Hx) as (p & Hp).
        exists (g p); rewrite H2; auto.
      + intros p; rewrite G4; auto.
    Qed.

    (* First a surjective map from some transitive set d to X *)

    Local Definition d := projT1 X_surj_hfs.
    Local Definition s := projT1 (projT2 X_surj_hfs).
    Local Definition i := proj1_sig (projT2 (projT2 (X_surj_hfs))).

    Let Hd : hfs_transitive d.       Proof. apply (proj2_sig (projT2 (projT2 (X_surj_hfs)))). Qed.
    Let Hempty : ∅ ∈ d.              Proof. apply (proj2_sig (projT2 (projT2 (X_surj_hfs)))). Qed.

    Local Fact Hs : forall x, s (i x) = x.  
    Proof. apply (proj2_sig (projT2 (projT2 (X_surj_hfs)))). Qed.

    Local Fact Hi : forall x, i x ∈ d.
    Proof. apply (proj2_sig (projT2 (projT2 (X_surj_hfs)))). Qed.

    Local Fact Hi' : forall s, s ∈ d -> exists x, s = i x.
    Proof. apply (proj2_sig (projT2 (projT2 (X_surj_hfs)))). Qed.

    (* Now we build P^(1+2nt) d that contains all the sets of nt-tuples of d *)

    Local Definition p := iter hfs_pow d (1+(2*nt)).

    Local Fact Hp1 : hfs_transitive p.
    Proof. apply hfs_iter_pow_trans; auto. Qed.

    Local Fact Hp2 : d ∈ p.
    Proof.
      apply hfs_iter_pow_le with (n := 1); simpl; auto; try lia.
      apply hfs_pow_spec; auto.
    Qed.

    Local Fact Hp5 n v : (forall p, vec_pos v p ∈ d) -> @hfs_tuple n v ∈ iter hfs_pow d (2*n).
    Proof. apply hfs_tuple_pow; auto. Qed.

    Local Fact Hp6 n v : n <= nt -> (forall p, vec_pos v p ∈ d) -> @hfs_tuple n v ∈ p.
    Proof. 
      intros L H; apply Hp5 in H.
      revert H; apply hfs_iter_pow_le; try lia; auto.
    Qed.

  End the_model.

  Variable (R : vec X nt -> Prop).
  Hypothesis HR : forall v, { R v } + { ~ R v }.

  Hint Resolve finite_t_prod hfs_mem_fin_t : core.
  Hint Resolve Hp1 Hp2 Hp5 Hp6 Hs Hi Hi' : core.

  Section the_relation.

    (* We encode R as a subset of tuples of elements of d in p *)

    Let encode_R : { r | r ∈ p 
                      /\ (forall v, @hfs_tuple nt v ∈ r -> forall q, vec_pos v q ∈ d)
                      /\ forall v, R v <-> hfs_tuple (vec_map i v) ∈ r }.
    Proof.
      set (P v := R (vec_map s v) /\ forall q, vec_pos v q ∈ d).
      set (f := @hfs_tuple nt).
      destruct hfs_comprehension with (P := P) (f := f) as (r & Hr).
      + apply fin_t_dec.
        * intros; apply HR.
        * apply fin_t_vec with (P := fun t => t ∈ d).
          apply hfs_mem_fin_t.
      + exists r; msplit 2.
        * unfold p; rewrite Nat.add_comm, iter_plus with (b := 1).
          apply hfs_pow_spec; intros x; rewrite Hr.
          intros (v & H1 & <-).
          apply Hp5, H1.
        * unfold f; intros v.
          rewrite Hr.
          intros (w & H1 & H2).
          apply hfs_tuple_spec in H2; subst w.
          apply H1.
        * intros v.
          rewrite Hr.
          split.
          - exists (vec_map i v); split; auto.
            split; auto.
            ++ rewrite vec_map_map.
               revert H; apply fol_equiv_ext.
               f_equal; apply vec_pos_ext; intro; rew vec.
            ++ intro; rew vec.
          - intros (w & (H1 & _) & H2).
            apply hfs_tuple_spec in H2.
            revert H1; subst w; apply fol_equiv_ext.
            f_equal; apply vec_pos_ext; intro; rew vec.
    Qed.

    Local Definition r := proj1_sig encode_R.
  
    Local Fact Hr1 : r ∈ p.
    Proof. apply (proj2_sig encode_R). Qed.

    Local Fact Hr2 v : @hfs_tuple nt v ∈ r -> forall q, vec_pos v q ∈ d.
    Proof. apply (proj2_sig encode_R). Qed.

    Local Fact Hr3 v : R v <-> hfs_tuple (vec_map i v) ∈ r.
    Proof. apply (proj2_sig encode_R). Qed.

  End the_relation.

  Hint Resolve Hr1 Hr2 Hr3 : core.

  (* The Boolean encoding of x ∈ p *)

  Local Definition p_bool x := if hfs_mem_dec x p then true else false.

  Local Fact p_bool_spec x : x ∈ p <-> p_bool x = true.
  Proof.   
    unfold p_bool.
    destruct (hfs_mem_dec x p); split; try tauto; discriminate.
  Qed.

  Local Fact p_bool_spec1 x : x ∈ p -> p_bool x = true.
  Proof. apply p_bool_spec. Qed.

  Local Fact p_bool_spec2 x : p_bool x = true -> x ∈ p.
  Proof. apply p_bool_spec. Qed.

  Local Definition Y := sig (fun x => p_bool x = true).

  Notation π1 := (@proj1_sig _ (fun x => p_bool x = true)).

  Hint Resolve p_bool_spec p_bool_spec1 p_bool_spec2 : core.

  Local Fact eqY : forall x y : Y, π1 x = π1 y -> x = y.
  Proof. 
    intros (x & Hx) (y & Hy); simpl.
    intros; subst; f_equal; apply UIP_dec, bool_dec.
  Qed.

  Local Fact HY : finite_t Y.
  Proof. 
    apply fin_t_finite_t.
    + intros; apply UIP_dec, bool_dec.
    + generalize (hfs_mem_fin_t p); apply fin_t_equiv.
      intros x; auto.
  Qed.

  (* This one is not needed anymore *)

  Local Fact discrY : discrete Y.
  Proof.
    intros (x & Hx) (y & Hy).
    destruct (hfs_eq_dec x y) as [ -> | D ].
    + left; f_equal; apply UIP_dec, bool_dec.
    + right; contradict D; inversion D; auto.
  Qed.

  Local Definition mem (x y : Y) := π1 x ∈ π1 y.

  Local Fact mem_dec : forall x y, { mem x y } + { ~ mem x y }.
  Proof.
    intros (a & ?) (b & ?); unfold mem; simpl; apply hfs_mem_dec.
  Qed.

  Local Definition yd : Y := exist _ _ (p_bool_spec1 Hp2).
  Local Definition yr : Y := exist _ _ (p_bool_spec1 Hr1).

  Local Fact fa_mem_Y (P : _ -> Prop) :
                           (forall a, a ∈ p -> P a)
                       <-> (forall a, P (π1 a)).
  Proof.
    split.
    + intros H (a & Ha); simpl; auto.
    + intros H a Ha.
      apply (H (exist _ _ (p_bool_spec1 Ha))).
  Qed.

  Local Fact ex_mem_Y (P : _ -> Prop) :
                           (exists a, a ∈ p /\ P a)
                       <-> (exists a, P (π1 a)).
  Proof.
    split.
    + intros (a & H & Ha). 
      exists (exist _ a (p_bool_spec1 H)); auto.
    + intros ((a & Ha) & H); simpl in *; eauto.
  Qed.

  Local Fact mem_fa_Y (P : _ -> Prop) k : k ∈ p -> (forall a, P a -> a ∈ p)
                       -> (forall a, a ∈ k <-> P a)
                       <-> (forall a, π1 a ∈ k <-> P (π1 a)).
  Proof.
    intros H1 H2.
    rewrite <- fa_mem_Y with (P := fun a => a ∈ k <-> P a).
    split.
    + intros H ? _; auto.
    + intros H a; split. 
      * intros Ha; apply H; auto.
        apply (Hp1 Ha); auto.
      * intros Ha; apply H; auto.
  Qed.

  (* Membership equivalence is identity in the model *)

  Local Fact mem_equiv_Y u v : 
                        u ∈ p 
                     -> v ∈ p
                     -> (forall y : Y, π1 y ∈ u <-> π1 y ∈ v)
                    <-> (forall x : hfs, x ∈ u <-> x ∈ v).
  Proof.
    intros Hu Hv.
    symmetry; apply mem_fa_Y; auto.
    intros s Hs; apply (Hp1 Hs); auto.
  Qed.

  Local Fact is_equiv : forall x y, mb_equiv mem x y <-> π1 x = π1 y.
  Proof.
    intros (x & Hx) (y & Hy); simpl.
    unfold mb_equiv, mem; simpl; split.
    2: { intros []; tauto. }
    rewrite mem_equiv_Y; auto; apply hfs_mem_ext.
  Qed.

  Local Fact mem_ext_Y x y : x ∈ p -> y ∈ p -> (forall a, π1 a ∈ x <-> π1 a ∈ y) <-> x = y.
  Proof.
    intros H1 H2; split.
    + intros H; apply hfs_mem_ext.
      rewrite mem_fa_Y; auto.
      intros z Hz; apply (Hp1 Hz); auto.
    + intros ->; tauto.
  Qed.

  Hint Resolve mem_ext_Y : core.

  Local Fact is_pair : forall x y k, mb_is_pair mem k x y 
                                 <-> π1 k = hfs_pair (π1 x) (π1 y).
  Proof.
    intros (x & Hx) (y & Hy) (k & Hk); simpl.
    unfold mb_is_pair; simpl.
    unfold mb_equiv, mem; simpl.
    rewrite hfs_pair_spec'.
    rewrite mem_fa_Y; auto.
    2: intros ? [ -> | -> ]; auto.
    fol equiv; intros (a & Ha); simpl.
    fol equiv; try tauto.
    fol equiv; auto.
  Qed.

  Local Fact is_opair : forall x y k, mb_is_opair mem k x y 
                                  <-> π1 k = ⟬π1 x,π1 y⟭.
  Proof.
    intros (x & Hx) (y & Hy) (k & Hk); simpl.
    unfold mb_is_opair; simpl.
    split.
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

  Local Fact is_tuple n : forall v t, @mb_is_tuple _ mem t n v 
                                  <-> π1 t = hfs_tuple (vec_map π1 v).
  Proof.
    induction n as [ | n IHn ]; intros v (t & Ht).
    + vec nil v; clear v; simpl; split.
      * intros H; apply hfs_mem_ext.
        intros z; split.
        - intros Hz.
          assert (Hz' : p_bool z = true).
          { apply p_bool_spec.
            apply Hp1 with (1 := Hz), p_bool_spec; auto. }
          destruct (H (exist _ z Hz')); auto.
        - rewrite hfs_empty_spec; tauto. 
      * intros -> (z & ?); unfold mem; simpl.
        rewrite hfs_empty_spec; tauto.
    + vec split v with x; simpl; split.
      * intros (t' & H1 & H2).
        rewrite IHn in H2; try lia.
        rewrite <- H2.
        apply is_opair with (k := exist _ t Ht); auto.
      * intros ->.
        assert (H1 : p_bool (hfs_tuple (vec_map π1 v)) = true).
        { apply p_bool_spec.
          apply p_bool_spec in Ht.
          apply hfs_trans_opair_inv, proj2, hfs_trans_pair_inv in Ht; auto; tauto. }
        exists (exist _ (hfs_tuple (vec_map π1 v)) H1); split.
        - rewrite is_opair; simpl; auto.
        - rewrite IHn; simpl; auto.
  Qed.

  Local Fact has_tuples : mb_has_tuples mem yd nt.
  Proof.
    intros v Hv.
    set (t := hfs_tuple (vec_map (proj1_sig (P:=fun x : hfs => p_bool x = true)) v)).
    assert (H1 : p_bool t = true).
    { apply p_bool_spec, Hp6; auto; intro; rew vec; apply Hv. }
    exists (exist _ t H1).
    apply is_tuple; simpl; reflexivity.
  Qed.

  Local Definition i' x : Y := exist _ _ (p_bool_spec1 (Hp1 (Hi x) Hp2)).
 
  Local Fact Hi'' x : mem (i' x) yd.
  Proof. unfold i', yd, mem; simpl; auto. Qed.

  Hint Resolve Hi'' : core.

  Local Definition s' (y : Y) : X := s (π1 y).

  (*
    For finite and discrete type X, non empty (as witnessed by a given element)
    equipped with a Boolean ternary relation R, one can compute a type Y, finite
    (and discrete), equipped with a Boolean binary membership predicate ∈ (which is 
    extensional). Y is a finite (set like) model which contains two sets yd and 
    yr and there is a bijection between X and (the elements of) yd. All ordered 
    nt-tuples build from elements of yd exist in Y, and yr encodes R in the set 
    of (ordered) nt-tuples it contains. 
    (Finally, membership equivalence (≈) is the same as identity (=) in Y).

    Membership equivalence : x ≈ y := ∀z, z∈x <-> z∈y
    Membership extensional : x ≈ y -> ∀z, x∈z -> y∈z

    Tuples are build the usual way (in set theory)
      - z ∈ {x,y} := z ≈ x \/ z ≈ y
      - ordered pairs: (x,y) is {{x},{x,y}}
      - ordered triples: (x,y,z) is ((x,y),z), etc

    Non-emptyness is not really necessary but then the bijection between X=ø 
    and yl has to be implemented with dependent functions, more cumbersome to work
    with. And first order models can never be empty because one has to be able
    to interpret variables. 

    Maybe a discussion on the case of empty models could help, but then 
    the FO logic been reduced to True/False in that case.
    Any ∀ formula is True, any ∃ is False and no atomic formula can ever
    be evaluated (because it contains terms that cannot be interpreted). 
    Only closed formula have a meaning in the empty model 
  *)
  
  Theorem reln_hfs : { Y : Type &
                     { _ : finite_t Y & 
                     { mem : Y -> Y -> Prop &
                     { _ : forall u v, { mem u v } + { ~ mem u v } & 
                     { yd : Y &
                     { yr : Y & 
                     { i : X -> Y & 
                     { s : Y -> X &
                             (forall x, mem (i x) yd)
                          /\ (forall y, mem y yd -> exists x, y = i x)
                          /\ (forall v, R v <-> mb_is_tuple_in mem yr (vec_map i v))
                      }}}}}}}}.
  Proof using x0 Xfin Xdiscr HR.
    exists Y, HY, mem, mem_dec, yd, yr, i', s'.
    msplit 2; auto.
    + intros y Hy; unfold i'.
      destruct (Hi' Hy) as (x & Hx).
      exists x; apply eqY; simpl; auto.
    + intros v; rewrite Hr3; split.
      * intros Hv.
        red.
        assert (H1 : p_bool (hfs_tuple (vec_map i v)) = true).
        { apply p_bool_spec, Hp1 with (1 := Hv); auto. }
        exists (exist _ (hfs_tuple (vec_map i v)) H1); split.
        - apply is_tuple; simpl; rewrite vec_map_map; auto.
        - unfold yr; red; simpl; auto.
      * intros ((t & Ht) & H1 & H2).
        rewrite is_tuple in H1.
        simpl in H1, H2.
        rewrite vec_map_map in H1; subst t; auto.
  Qed.

End bt_model_n.
