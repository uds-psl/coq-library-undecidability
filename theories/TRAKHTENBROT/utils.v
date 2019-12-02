(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Bool Eqdep_dec.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_list finite.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops.

Set Implicit Arguments.

Fact eq_bool_pirr (b1 b2 : bool) (H1 H2 : b1 = b2) : H1 = H2.
Proof. apply UIP_dec, bool_dec. Qed.

Fact eq_nat_pirr (n : nat) (H : n = n ) : H = eq_refl.
Proof. apply UIP_dec, eq_nat_dec. Qed.

Section graphs.

  Variable (X Y : Type) (R : X -> Y -> Prop).

  Definition graph_tot := forall x, ex (R x).
  Definition graph_fun := forall x y1 y2, R x y1 -> R x y2 -> y1 = y2.

  Definition is_graph_function := graph_fun /\ graph_tot.

  Hypothesis (H1 : finite_t Y)
             (H3 : forall x y, { R x y } + { ~ R x y }).

  Definition graph_tot_reif : is_graph_function -> { f | forall x y, R x y <-> y = f x }.
  Proof.
    intros (H2 & H4). 
    destruct finite_t_dec_choice with (3 := H4) as (f & Hf); auto.
    exists f; intros x y; split.
    + intros H; generalize H (Hf x); apply H2.
    + intros ->; auto.
  Qed.

End graphs.

Fact in_concat_iff X (ll : list (list X)) x : In x (concat ll) <-> exists l, In x l /\ In l ll.
Proof.
  rewrite <- (map_id ll) at 1.
  rewrite <- flat_map_concat_map, in_flat_map.
  firstorder.
Qed.

Section rel_chain.

  (* l = [s1;...;sn] 
     rel_chain R x l y <-> y (R s1) x1 (R s2) x2 .... (R sn) xn = x 
                       <-> y (R s1) o (R s2) o .... o (R sn) x
  *) 

  Fixpoint rel_chain I X (R : I -> X -> X -> Prop) y l x :=
    match l with
      | nil  => y = x
      | s::l => exists u, R s y u /\ rel_chain R u l x
    end.

  Fact rel_chain_map I J (f : I -> J) X (R : J -> X -> X -> Prop) y l x :
         rel_chain R y (map f l) x
     <-> rel_chain (fun i => R (f i)) y l x.
  Proof.
    revert y; induction l as [ | s l IHl ]; intros y; simpl; try tauto.
    apply exists_equiv; intro; rewrite IHl; tauto.
  Qed.

  Fact rel_chain_fold I X R f x l y :
             (forall s, In s l -> forall u v, R s v u <-> v = f s u)
          -> @rel_chain I X R y l x <-> y = fold_right f x l.
  Proof.
    revert y; induction l as [ | s l IHl ]; intros y Hl; simpl; try easy.
    split.
    + intros (u & H1 & H2); revert H2 H1; rewrite IHl, Hl; simpl; auto.
      * intros -> ->; simpl; auto.
      * intros ? ?; apply Hl; simpl; auto.
    + intros ->.
      exists (fold_right f x l); split.
      * apply Hl; simpl; auto.
      * apply IHl; auto.
        intros ? ?; apply Hl; simpl; auto.
  Qed.

  Fact rel_chain_fun I X R l :
             (forall s, In s l -> graph_fun (fun x y => R s y x))
          -> graph_fun (fun x y => @rel_chain I X R y l x).
  Proof.
    induction l as [ | s l IHl ]; simpl; intros H x y1 y2.
    + intros; subst; auto.
    + intros (u1 & H1 & H2) (u2 & H3 & H4).
      assert (forall s, In s l -> graph_fun (fun x y : X => R s y x)) as H0.
      { intros; apply H; auto. }
      specialize (IHl H0 _ _ _ H2 H4); subst.
      revert H1 H3; apply H; auto.
  Qed.

  Section simul.

    Variable (I X Y : Type) (R : I -> X -> X -> Prop) (T : I -> Y -> Y -> Prop)
             (simul : X -> Y -> Prop).

    Infix "⋈" := simul (at level 70, no associativity).

    Fact rel_chain_simul_tot sx l x y : 
                 (forall s x y sx, In s l -> x ⋈ y -> R s sx x -> exists sy, sx ⋈ sy /\ T s sy y)
              -> x ⋈ y 
              -> rel_chain R sx l x 
              -> exists sy, sx ⋈ sy /\ rel_chain T sy l y.
    Proof.
      intros H Hxy; revert H sx; induction l as [ | s l IHl ]; simpl; intros H0 sx H.
      + exists y; subst; auto.
      + destruct H as (x' & H1 & H2).
        destruct IHl with (2 := H2) as (y' & H3 & H4).
        { intros ? ? ? ? ?; apply H0; auto. }
        destruct H0 with (2 := H3) (3 := H1) as (sy & H5 & H6); auto. 
        exists sy; split; auto.
        exists y'; auto.
    Qed.

  End simul.

End rel_chain.

