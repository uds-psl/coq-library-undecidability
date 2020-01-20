(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Bool Lia Eqdep_dec.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations utils fol_ops decidable.

Set Implicit Arguments.

(** We develop a basic theory of enumeration, ie empty types or
    types for which there is a surjection from nat.
    Same for predicates *)

(** We need an arbitrary surjection nat -> nat * nat *)

Local Definition surj n := 
  match pow2_2n1_dec n with
    | existT _ a (exist _ b _) => (a,b)
  end.

Local Fact Hsurj a b : exists n, surj n = (a,b).
Proof.
  exists (pow2 a*(2*b+1)-1).
  unfold surj.
  destruct (pow2_2n1_dec (pow2 a * (2 * b + 1) - 1)) as (c & d & H).
  replace (S (pow2 a*(2*b+1)-1)) with (pow2 a*(2*b+1)) in H.
  + apply pow2_dec_uniq in H; destruct H; subst; auto.
  + generalize (pow2_dec_ge1 a b); lia.
Qed.

Section enumerable_definitions.

  Variable (X : Type).

  (** enumerability of a Type *)

  Definition type_enum := exists f : nat -> option X, forall x, exists n, Some x = f n.
  Definition type_enum_t := { f : nat -> option X | forall x, exists n, Some x = f n }.

  Definition list_enum := exists f : nat -> list X, forall x, exists n, In x (f n).
  Definition list_enum_t := { f : nat -> list X | forall x, exists n, In x (f n) }.

  (** of a predicate, definition 1 *)

  Definition opt_enum P := exists f : nat -> option X, forall x, P x <-> exists n, Some x = f n.
  Definition opt_enum_t P := { f : nat -> option X | forall x, P x <-> exists n, Some x = f n }.

  (** of a predicate, definition 2 *) 

  Definition rec_enum P := exists (Q : nat -> X -> bool),
                           forall x, P x <-> exists n, Q n x = true.

  Definition rec_enum_t P := { Q : nat -> X -> bool | forall x, P x <-> exists n, Q n x = true }.

  Theorem type_list_enum : type_enum <-> list_enum.
  Proof.
    split.
    + intros (f & Hf).
      exists (fun n => match f n with Some x => x::nil | None => nil end).
      intros x; destruct (Hf x) as (n & Hn); exists n; rewrite <- Hn; simpl; auto.
    + intros (f & Hf).
      exists (fun n => let (a,b) := surj n in nth_error (f a) b).
      intros x; destruct (Hf x) as (a & Ha).
      destruct In_nth_error with (1 := Ha) as (b & Hb).
      destruct (Hsurj a b) as (n & Hn); exists n; now rewrite Hn.
  Qed.

  Theorem type_list_enum_t : type_enum_t ≋ list_enum_t.
  Proof.
    split.
    + intros (f & Hf).
      exists (fun n => match f n with Some x => x::nil | None => nil end).
      intros x; destruct (Hf x) as (n & Hn); exists n; rewrite <- Hn; simpl; auto.
    + intros (f & Hf).
      exists (fun n => let (a,b) := surj n in nth_error (f a) b).
      intros x; destruct (Hf x) as (a & Ha).
      destruct In_nth_error with (1 := Ha) as (b & Hb).
      destruct (Hsurj a b) as (n & Hn); exists n; now rewrite Hn.
  Qed.

  (** An alternate characterization with Boolean decider 

  Fact rec_enum_t_alt P : rec_enum_t P ≋ { Q : nat -> X -> bool | forall x, P x <-> exists n, Q n x = true }.
  Proof.
    split.
    + intros (Q & HQ & H).
      exists (fun n x => if HQ n x then true else false).
      intros x; rewrite H; apply exists_equiv; intros n.
      destruct (HQ n x); split; try tauto; discriminate.
    + intros (Q & H).
      exists (fun n x => Q n x = true).
      exists; auto; intros; apply bool_dec.
  Qed. *)

  Section list_enum_by_measure_fin_t.

    Variable (m : X -> nat) (Hm : forall n, fin_t (fun x => m x < n)).

    Theorem list_enum_by_measure_fin_t : list_enum_t.
    Proof.
      exists (fun n => proj1_sig (Hm n)).
      intros x; exists (S (m x)).
      apply (proj2_sig (Hm _)); auto.
    Qed.

  End list_enum_by_measure_fin_t.

  Section type_enum_t_by_measure.

    Variable (m : X -> nat) 
             (Hm : forall n, opt_enum_t (fun x => m x <= n)).

    Theorem type_enum_t_by_measure : type_enum_t.
    Proof.
      apply constructive_choice in Hm; destruct Hm as (f & Hf); clear Hm.
      exists (fun j => let (a,n) := surj j in f a n).
      intros x.
      destruct (proj1 (Hf _ x) (le_refl _)) as (a & Ha).
      destruct (Hsurj (m x) a) as (n & Hn).
      exists n; rewrite Hn; auto.
    Qed.

  End type_enum_t_by_measure.

End enumerable_definitions.

Section enumerable.

  Variable (X : Type) (Xdiscr : discrete X) (Xenum : type_enum X) (Xenum_t : type_enum_t X).

  Implicit Type (P : X -> Prop).

  (** On a discrete type, opt_enum implies rec_enum *)

  Fact opt_enum_rec_enum_discrete P : opt_enum P -> rec_enum P.
  Proof.
    intros (f & Hf).
    exists (fun n x => match f n with Some y => 
              if Xdiscr x y then true else false | None => false end); intros x; 
      rewrite Hf; split.
    + intros (n & Hn); exists n; rewrite <- Hn.
      destruct (Xdiscr x x) as [ | [] ]; auto.
    + intros (n & Hn); revert Hn.
      case_eq (f n).
      * intros y Hy.
        destruct (Xdiscr x y) as [ -> | ].
        - exists n; auto.
        - discriminate.
      * discriminate.
  Qed.

  Fact opt_enum_rec_enum_discrete_t P : opt_enum_t P -> rec_enum_t P.
  Proof.
    intros (f & Hf).
    exists (fun n x => match f n with Some y => 
              if Xdiscr x y then true else false | None => false end); intros x; 
      rewrite Hf; split.
    + intros (n & Hn); exists n; rewrite <- Hn.
      destruct (Xdiscr x x) as [ | [] ]; auto.
    + intros (n & Hn); revert Hn.
      case_eq (f n).
      * intros y Hy.
        destruct (Xdiscr x y) as [ -> | ].
        - exists n; auto.
        - discriminate.
      * discriminate.
  Qed.

  (** On a enumerable type, rec_enum implies opt_enum *)

  Fact rec_enum_opt_enum_type_enum P : rec_enum P -> opt_enum P.
  Proof.
    destruct Xenum as (s & Hs).
    intros (Q & HQ).
    set (f n := 
      let (a,b) := surj n
      in match s a with 
        | Some x => if Q b x then Some x else None
        | None => None
      end).
    exists f; intros x; rewrite HQ; split; unfold f.
    + intros (n & Hn).
      destruct (Hs x) as (a & Ha).
      destruct (Hsurj a n) as (m & Hm).
      exists m; rewrite Hm, <- Ha, Hn; auto.
    + intros (n & Hn).
      destruct (surj n) as (a,b).
      destruct (s a) as [ y | ]; try discriminate.
      revert Hn; case_eq (Q b y).
      * inversion 2; exists b; auto.
      * discriminate. 
  Qed.

  Fact rec_enum_opt_enum_type_enum_t P : rec_enum_t P -> opt_enum_t P.
  Proof.
    destruct Xenum_t as (s & Hs).
    intros (Q & HQ).
    set (f n := 
      let (a,b) := surj n
      in match s a with 
        | Some x => if Q b x then Some x else None
        | None => None
      end).
    exists f; intros x; rewrite HQ; split; unfold f.
    + intros (n & Hn).
      destruct (Hs x) as (a & Ha).
      destruct (Hsurj a n) as (m & Hm).
      exists m; rewrite Hm, <- Ha, Hn; auto.
    + intros (n & Hn).
      destruct (surj n) as (a,b).
      destruct (s a) as [ y | ]; try discriminate.
      revert Hn; case_eq (Q b y).
      * inversion 2; exists b; auto.
      * discriminate. 
  Qed.

  Hint Resolve opt_enum_rec_enum_discrete rec_enum_opt_enum_type_enum
               opt_enum_rec_enum_discrete_t rec_enum_opt_enum_type_enum_t.

  (** On a datatype, opt_enum and rec_enum are equivalent *)

  Theorem opt_rec_enum_equiv P : opt_enum P <-> rec_enum P.
  Proof. split; auto. Qed.

  Theorem opt_rec_enum_equiv_t P : opt_enum_t P ≋ rec_enum_t P.
  Proof. split; auto. Qed.

End enumerable.

Section enum_ops.

  Fact type_enum_t_unit : type_enum_t unit.
  Proof. 
    exists (fun _ => Some tt).
    intros []; exists 0; auto. 
  Qed.

  Fact type_enum_t_bool : type_enum_t bool.
  Proof. 
    exists (fun n => Some (match n with 0 => true | _ => false end)).
    intros [].
    + exists 0; auto.
    + exists 1; auto. 
  Qed.

  Fact type_enum_t_nat : type_enum_t nat.
  Proof.
    exists Some.
    intros n; exists n; auto.
  Qed.

  Fact type_enum_t_pos n : type_enum_t (pos n).
  Proof.
    exists (fun i => match le_lt_dec n i with left _ => None | right H => Some (nat2pos H) end).
    intros p.
    exists (pos2nat p).
    destruct (le_lt_dec n (pos2nat p)) as [ H | H ].
    + generalize (pos2nat_prop p); lia.
    + rewrite nat2pos_pos2nat; auto.
  Qed.

  Fact type_enum_opt_enum_t X : type_enum_t X ≋ opt_enum_t (fun _ : X => True).
  Proof.
    split.
    + intros (f & Hf); exists f; intros; split; auto.
    + intros (f & Hf); exists f; intros; apply Hf; auto.
  Qed.

  Fact opt_enum_t_prod X Y (P : X -> Prop) (Q : Y -> Prop) :
       opt_enum_t P -> opt_enum_t Q -> opt_enum_t (fun c => P (fst c) /\ Q (snd c)).
  Proof.
    intros (f & Hf) (g & Hg).
    exists (fun n => let (a,b) := surj n in 
      match f a, g b with
        | Some x, Some y => Some (x,y)
        | _     , _      => None
      end).
    intros (x,y); simpl; rewrite Hf, Hg; split.
    + intros ((a & Ha) & (b & Hb)).
      destruct (Hsurj a b) as (n & Hn).
      exists n; rewrite Hn, <- Ha, <- Hb; auto.
    + intros (n & Hn).
      destruct (surj n) as (a,b).
      revert Hn.
      case_eq (f a); try discriminate; intros u Hu.
      case_eq (g b); try discriminate; intros v Hv.
      inversion 1; split; [ exists a | exists b ]; auto.
  Qed.

  Fact opt_enum_t_sum X Y (P : X -> Prop) (Q : Y -> Prop) :
       opt_enum_t P -> opt_enum_t Q -> opt_enum_t (fun z : X + Y => match z with inl x => P x | inr y => Q y end).
  Proof.
    intros (f & Hf) (g & Hg).
    exists (fun n => let (a,b) := surj n in 
      match a with
        | 0 => match f b with Some x => Some (inl x) | _ => None end
        | _ => match g b with Some y => Some (inr y) | _ => None end
      end).
    intros [ x | y ].
    + rewrite Hf; split.
      * intros (b & Hb).
        destruct (Hsurj 0 b) as (n & Hn).
        exists n; rewrite Hn, <- Hb; auto.
      * intros (n & Hn); revert Hn.
        destruct (surj n) as ([ | a],b).
        - case_eq (f b); try discriminate; intros u Hu; inversion 1; exists b; auto.
        - destruct (g b); discriminate.
    + rewrite Hg; split.
      * intros (b & Hb).
        destruct (Hsurj 1 b) as (n & Hn).
        exists n; rewrite Hn, <- Hb; auto.
      * intros (n & Hn); revert Hn.
        destruct (surj n) as ([ | a],b).
        - destruct (f b); discriminate.
        - case_eq (g b); try discriminate; intros u Hu; inversion 1; exists b; auto.
  Qed.

  Fact opt_enum_t_dep_sum X (f : X -> Type) (P : forall x, f x -> Prop) :
         discrete X
      -> type_enum_t X 
      -> (forall x, opt_enum_t (P x)) 
      -> opt_enum_t (fun p : sigT f => P _ (projT2 p)).
  Proof.
    intros D (g & Hg) H.
    apply constructive_choice in H; destruct H as (h & Hh).
    exists (fun n : nat => match surj n with (a,b) =>
       match g a with
         | Some x => match h x b with
           | Some y => Some (existT _ x y)
           | None   => None
         end
         | None => None
       end end).
    intros (x & y); simpl; rewrite Hh; split.
    + intros (b & Hb).
      destruct (Hg x) as (a & Ha).
      destruct (Hsurj a b) as (n & Hn).
      exists n; rewrite Hn, <- Ha, <- Hb; auto.
    + intros (n & Hn); revert Hn.
      destruct (surj n) as (a,b).
      case_eq (g a); try discriminate; intros x' Hx'.
      case_eq (h x' b); try discriminate; intros y' Hy'.
      inversion 1; subst x'; exists b; rewrite Hy'.
      apply inj_pair2_eq_dec in H1; subst; auto.
  Qed.

  Fact opt_enum_t_image X Y (P : X -> Prop) (Q : Y -> Prop) (f : X -> Y) :
          (forall y, Q y <-> exists x, P x /\ y = f x)
       -> opt_enum_t P -> opt_enum_t Q.
  Proof.
    intros Hf (g & Hg).
    exists (fun n => match g n with Some x => Some (f x) | _ => None end).
    intros y; rewrite Hf; split.
    + intros (x & H1 & ->); revert H1; rewrite Hg.
      intros (n & E); exists n; rewrite <- E; auto.
    + intros (n & Hn); revert Hn.
      case_eq (g n); try discriminate. 
      intros x E; inversion 1; exists x; split; auto.
      apply Hg; exists n; auto.
  Qed.

  Fact opt_enum_t_vec X n (P : X -> Prop) :
       opt_enum_t P -> opt_enum_t (fun v : vec X n => forall p, P (vec_pos v p)).
  Proof.
    intros HP.
    induction n as [ | n IHn ].
    + exists (fun _ => Some vec_nil).
      intros v; vec nil v; split.
      * exists 0; auto.
      * intros _ p; invert pos p.
    + generalize (opt_enum_t_prod HP IHn).
      apply opt_enum_t_image with (f := fun p => vec_cons (fst p) (snd p)).
      intros v; split.
      * vec split v with x; intros H; exists (x,v); simpl; split; auto; split.
        - apply (H pos0).
        - intros p; apply (H (pos_nxt p)).
      * intros ((x,w) & (H1 & H2) & ->). 
        simpl fst in *; simpl snd in *.
        intros p; invert pos p; auto.
  Qed.

  Fact opt_enum_t_list X (P : X -> Prop) : 
       opt_enum_t P -> opt_enum_t (Forall P).
  Proof.
    intros H.
    generalize (opt_enum_t_dep_sum _ _ eq_nat_dec type_enum_t_nat (fun n => opt_enum_t_vec n H)).
    apply opt_enum_t_image 
      with (f := fun p => match p  with existT _ n v => vec_list v end).
    intros l; rewrite Forall_forall; split.
    + intros Hl; exists (existT _ (length l) (list_vec l)); simpl.
      split. 
      * intros p; apply Hl.
        rewrite <- (list_vec_iso l) at 3.
        apply in_vec_list, in_vec_pos.
      * rewrite list_vec_iso; auto.
    + intros ((n&v) & H1 & ->); simpl in *.
      intros x Hx; apply vec_list_inv in Hx.
      destruct Hx as (p & ->); auto.
  Qed.

  Fact type_enum_t_vec X n : type_enum_t X -> type_enum_t (vec X n).
  Proof.
    intros HX.
    apply type_enum_opt_enum_t in HX.
    apply type_enum_opt_enum_t.
    generalize (opt_enum_t_vec n HX).
    apply opt_enum_t_image with (f := fun v => v).
    intros v; split; try tauto; exists v; auto.
  Qed.

  Fact type_enum_t_list X : type_enum_t X -> type_enum_t (list X).
  Proof.
    intros HX.
    apply type_enum_opt_enum_t in HX.
    apply type_enum_opt_enum_t.
    generalize (opt_enum_t_list HX).
    apply opt_enum_t_image with (f := fun v => v).
    intros v; split; try tauto; exists v; split; auto.
    apply Forall_forall; auto.
  Qed.

End enum_ops.
