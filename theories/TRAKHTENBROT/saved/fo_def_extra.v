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
  Require Import utils_tac utils_list finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations utils rel_chain fol_ops fo_sig fo_terms fo_logic fo_definable.

Set Implicit Arguments.

Notation ø := vec_nil.

Opaque fo_term_subst fo_term_map fo_term_sem.

Section extra.

  Variable (Σ : fo_signature) (ls : list (syms Σ)) (lr : list (rels Σ))
           (X : Type) (M : fo_model Σ X).

  Fact fol_def_subst1 R t : 
           fol_definable ls lr M (fun φ => R (φ 0))
        -> fot_definable ls M t
        -> fol_definable ls lr M (fun φ => R (t φ)).
  Proof.
    intros H1 H2.
    set (f n := match n with
        | 0 => t 
        | _ => fun φ => φ 0
      end).
    change (fol_definable ls lr M (fun φ => R (f 0 φ))). 
    apply fol_def_subst with (2 := H1) (f := f).
    intros [ | ]; simpl; fol def.
  Qed.

  Fact fol_def_subst_R_2 (R : (nat -> X) -> X -> X -> Prop) f t1 t2 : 
           fol_definable ls lr M (fun φ => R (fun n => φ (2+n)) (φ 0) (φ 1))
        -> fot_definable ls M t1
        -> fot_definable ls M t2
        -> fol_definable ls lr M (fun φ => R (fun n => φ (f n)) (t1 φ) (t2 φ)).
  Proof.
    intros H1 H2 H3.
    set (g n := match n with
        | 0 => t1 
        | 1 => t2
        | S (S n) => fun φ => φ (f n)
      end).
    change (fol_definable ls lr M (fun φ => R (fun n => g (2+n) φ) (g 0 φ) (g 1 φ))).
    apply fol_def_subst with (2 := H1) (f := g).
    intros [ | [] ]; simpl; fol def.
  Qed.

  Fact fol_def_subst3 R t1 t2 t3 : 
           fol_definable ls lr M (fun φ => R (φ 0) (φ 1) (φ 2))
        -> fot_definable ls M t1
        -> fot_definable ls M t2
        -> fot_definable ls M t3
        -> fol_definable ls lr M (fun φ => R (t1 φ) (t2 φ) (t3 φ)).
  Proof.
    intros H1 H2 H3 H4.
    set (f n := match n with
        | 0 => t1 
        | 1 => t2
        | 2 => t3
        | _ => fun φ => φ 0
      end).
    change (fol_definable ls lr M (fun φ => R (f 0 φ) (f 1 φ) (f 2 φ))). 
    apply fol_def_subst with (2 := H1) (f := f).
    intros [ | [ | [ | n ] ] ]; simpl; fol def.
  Qed.

  Fact fol_def_dec A : { A } + { ~ A } -> fol_definable ls lr M (fun _ => A).
  Proof.
    intros [ H | H ].
    + apply fol_def_equiv with (R := fun _ => True); try tauto; fol def.
    + apply fol_def_equiv with (R := fun _ => False); try tauto; fol def.
  Qed.

  Section rel_chain.

    (** Definition of the following encoding ...
        do not have to worry about managing bound
        variable with the high lever closure operators

          y ~ s1[s2[...sn[x]]] 
      iff y ~ s1[x1] /\ x1 ~ s2[x2] /\ ... /\ xn-1 ~ sn[xn] /\ xn ~ x   
      iff R(y,x1,s1) /\ R(x1,x2,s2) /\ ... /\ R(xn-1,xn,sn) /\ xn = x 
     *)

    Hypothesis Heq : fol_definable ls lr M (fun φ => φ 0 = φ 1).

    Theorem fol_def_rel_chain I R y l x : 
                fot_definable ls M x
             -> fot_definable ls M y
             -> (forall s, In s l -> fol_definable ls lr M (fun φ => R s (φ 0) (φ 1)))
             -> fol_definable ls lr M (fun φ => @rel_chain I X R (y φ) l (x φ)).
    Proof.
      revert y x; induction l as [ | s l IHl ]; intros y x Hx Hy Hl; simpl.
      + apply fol_def_subst2; auto.
      + fol def.
        * apply fol_def_subst2 with (R := R s); fol def.
          apply Hl; simpl; auto.
        * apply IHl; fol def.
          intros; apply Hl; right; auto.
    Qed.

    Variables (R : X -> X -> X -> Prop).

    Theorem fol_def_rel_chain' K y l x : 
                fol_definable ls lr M (fun φ => R (φ 0) (φ 1) (φ 2))
             -> fot_definable ls M x
             -> fot_definable ls M y
             -> forall f : K -> nat, fol_definable ls lr M (fun φ => rel_chain R (y φ) (map (fun s => φ (f s)) l) (x φ)).
    Proof.
      intros HR.
      revert y x; induction l as [ | s l IHl ]; intros y x Hx Hy f; simpl.
      + apply fol_def_subst2; auto.
      + fol def.
        apply fol_def_subst3; fol def.
    Qed.

  End rel_chain.

End extra.
