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
  Require Import notations utils fol_ops.

Set Implicit Arguments.

(** We need a surjection nat -> nat * nat *)

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

Definition decidable (P : Prop) := { P } + { ~ P }.

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

  Definition rec_enum P := exists (Q : nat -> X -> Prop) (_ : forall n x, decidable (Q n x)),
                           forall x, P x <-> exists n, Q n x.

  Definition rec_enum_t P := { Q : nat -> X -> Prop &
                             { _ : forall n x, decidable (Q n x) &
                                   forall x, P x <-> exists n, Q n x } }.

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

  (** An alternate characterization with Boolean decider *)

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
  Qed. 

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
    exists (fun n x => match f n with Some y => x = y | None => False end); exists.
    + intros n x.
      destruct (f n) as [ y | ].
      * apply Xdiscr.
      * right; tauto.
    + intros x; rewrite Hf; split.
      * intros (n & Hn); exists n; rewrite <- Hn; auto.
      * intros (n & Hn); exists n.
        destruct (f n) as [ y | ]; subst; tauto.
  Qed.

  Fact opt_enum_rec_enum_discrete_t P : opt_enum_t P -> rec_enum_t P.
  Proof.
    intros (f & Hf).
    exists (fun n x => match f n with Some y => x = y | None => False end); exists.
    + intros n x.
      destruct (f n) as [ y | ].
      * apply Xdiscr.
      * right; tauto.
    + intros x; rewrite Hf; split.
      * intros (n & Hn); exists n; rewrite <- Hn; auto.
      * intros (n & Hn); exists n.
        destruct (f n) as [ y | ]; subst; tauto.
  Qed.

  (** On a enumerable type, rec_enum implies opt_enum *)

  Fact rec_enum_opt_enum_type_enum P : rec_enum P -> opt_enum P.
  Proof.
    destruct Xenum as (s & Hs).
    intros (Q & Qdec & HQ).
    set (f n := 
      let (a,b) := surj n
      in match s a with 
        | Some x => if Qdec b x then Some x else None
        | None => None
      end).
    exists f; intros x; rewrite HQ; split; unfold f.
    + intros (n & Hn).
      destruct (Hs x) as (a & Ha).
      destruct (Hsurj a n) as (m & Hm).
      exists m; rewrite Hm, <- Ha.
      destruct (Qdec n x) as [ | [] ]; auto.
    + intros (n & Hn).
      destruct (surj n) as (a,b).
      destruct (s a) as [ y | ]; try discriminate.
      destruct (Qdec b y) as [ H | H ]; try discriminate.
      exists b; inversion Hn; auto.
  Qed.

  Fact rec_enum_opt_enum_type_enum_t P : rec_enum_t P -> opt_enum_t P.
  Proof.
    destruct Xenum_t as (s & Hs).
    intros (Q & Qdec & HQ).
    set (f n := 
      let (a,b) := surj n
      in match s a with 
        | Some x => if Qdec b x then Some x else None
        | None => None
      end).
    exists f; intros x; rewrite HQ; split; unfold f.
    + intros (n & Hn).
      destruct (Hs x) as (a & Ha).
      destruct (Hsurj a n) as (m & Hm).
      exists m; rewrite Hm, <- Ha.
      destruct (Qdec n x) as [ | [] ]; auto.
    + intros (n & Hn).
      destruct (surj n) as (a,b).
      destruct (s a) as [ y | ]; try discriminate.
      destruct (Qdec b y) as [ H | H ]; try discriminate.
      exists b; inversion Hn; auto.
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

Section decidable_fun_pos_bool.

  Variable (n : nat) (K : (pos n -> bool) -> Prop)
           (HK : forall P Q, (forall x, P x = Q x) -> K P <-> K Q)
           (D : forall P, decidable (K P)).

  Let Dfa : decidable (forall v, K (vec_pos v)).
  Proof.
    apply (fol_quant_sem_dec fol_fa).
    + apply finite_t_vec, finite_t_bool.
    + intros v; apply D.
  Qed.

  Let Dex : decidable (exists v, K (vec_pos v)).
  Proof.
    apply (fol_quant_sem_dec fol_ex).
    + apply finite_t_vec, finite_t_bool.
    + intros v; apply D.
  Qed.

  Theorem fa_fun_pos_bool_decidable : decidable (forall P, K P).
  Proof.
    destruct Dfa as [ H | H ].
    + left. 
      intros P; generalize (H (vec_set_pos P)).
      apply HK; intro; rew vec.
    + right; contradict H.
      intro; apply H.
  Qed.

  Theorem ex_fun_pos_bool_decidable : decidable (exists P, K P).
  Proof.
    destruct Dex as [ H | H ].
    + left.
      destruct H as (v & Hv).
      exists (vec_pos v); auto.
    + right; contradict H.
      destruct H as (P & HP).
      exists (vec_set_pos P).
      revert HP; apply HK.
      intro; rew vec. 
  Qed.

End decidable_fun_pos_bool.

Section decidable_fun_finite_bool.

  Variable (X : Type) (H1 : finite_t X) (H2 : discrete X)
           (K : (X -> bool) -> Prop)
           (HK : forall P Q, (forall x, P x = Q x) -> K P <-> K Q)
           (Dec : forall P, decidable (K P)).

  Let D : { n : nat & bij_t X (pos n) }.
  Proof.
    apply finite_t_discrete_bij_t_pos; auto.
  Qed.

  Let n := projT1 D.
  Let i : X -> pos n := projT1 (projT2 D).
  Let j : pos n -> X := proj1_sig (projT2 (projT2 D)).

  Let Hji : forall x, j (i x) = x.
  Proof. apply (proj2_sig (projT2 (projT2 D))). Qed.

  Let Hij : forall y, i (j y) = y.
  Proof. apply (proj2_sig (projT2 (projT2 D))). Qed.

  Let T P := K (fun p => P (i p)).

  Let T_ext P Q : (forall x, P x = Q x) -> T P <-> T Q.
  Proof. intros H; apply HK; intro; apply H. Qed.

  Let T_dec P : decidable (T P).
  Proof. apply Dec. Qed.

  Theorem fa_fun_bool_decidable : decidable (forall P, K P).
  Proof.
    assert (H : decidable (forall P, T P)).
    { apply fa_fun_pos_bool_decidable; auto. }
    destruct H as [ H | H ]; [ left | right ].
    + intros P.
      generalize (H (fun p => P (j p))).
      apply HK; intro; rewrite Hji; auto.
    + contradict H; intros P; apply H.
  Qed.

  Theorem ex_fun_bool_decidable : decidable (exists P, K P).
  Proof.
    assert (H : decidable (exists P, T P)).
    { apply ex_fun_pos_bool_decidable; auto. }
    destruct H as [ H | H ]; [ left | right ].
    + destruct H as (P & H).
      exists (fun x => P (i x)); auto.
    + contradict H.
      destruct H as (P & H).
      exists (fun p => P (j p)).
      revert H; apply HK.
      intro; rewrite Hji; auto.
  Qed.

End decidable_fun_finite_bool.

Section decidable_upto.

  Variable (X : Type) (R : X -> X -> Prop) 
           (P : X -> Prop) (HP : forall x, decidable (P x))
           (HR : forall x y, R x y -> P x <-> P y).

  Theorem decidable_list_upto_fa l :
             (forall x, exists y, In y l /\ R x y)
          -> decidable (forall x, P x).
  Proof.
    intros Hl.
    destruct list_dec with (P := fun x => ~ P x) (Q := P) (l := l)
      as [ (x & H1 & H2) | H ].
    + intros x; generalize (HP x); unfold decidable; tauto.
    + right; contradict H2; auto.
    + left; intros x.
      destruct (Hl x) as (y & H1 & H2).
      generalize (H _ H1); apply (HR H2).
  Qed.

  Theorem decidable_list_upto_ex l :
             (forall x, exists y, In y l /\ R x y)
          -> decidable (exists x, P x).
  Proof.
    intros Hl.
    destruct list_dec with (1 := HP) (l := l)
      as [ (x & H1 & H2) | H ].
    + left; exists x; auto.
    + right; intros (x & Hx).
      destruct (Hl x) as (y & H1 & H2).
      apply (H _ H1). 
      revert Hx; apply (HR H2).
  Qed.

End decidable_upto.

Definition fun_ext X Y (f g : X -> Y) := forall x, f x = g x.
Definition prop_ext X (f g : X -> Prop) := forall x, f x <-> g x.

Section fun_pos_finite_t_upto.

  Variable (X : Type) (HX : finite_t X).
 
  Theorem fun_pos_finite_t_upto n : finite_t_upto (pos n -> X) (@fun_ext _ _).
  Proof.
    assert (H : finite_t (vec X n)).
    { apply finite_t_vec; auto. }
    destruct H as (l & Hl).
    exists (map (@vec_pos _ _) l).
    intros f. 
    exists (vec_pos (vec_set_pos f)); split.
    + apply in_map_iff; exists (vec_set_pos f); auto.
    + intros p; rew vec.
  Qed.

End fun_pos_finite_t_upto.

Section fun_finite_t_upto.

  Variable (X : Type) (HX1 : finite_t X) (HX2 : discrete X)
           (Y : Type) (HY : finite_t Y).

  Let D : { n : nat & bij_t X (pos n) }.
  Proof.
    apply finite_t_discrete_bij_t_pos; auto.
  Qed.

  Theorem fun_finite_t_upto : finite_t_upto (X -> Y) (@fun_ext _ _).
  Proof.
    destruct finite_t_discrete_bij_t_pos with X
      as (n & i & j & Hji & Hij); auto.
    destruct fun_pos_finite_t_upto with Y n
      as (l & Hl); auto.
    exists (map (fun f x => f (i x)) l).
    intros f.
    destruct (Hl (fun p => f (j p))) as (g & H1 & H2).
    exists (fun x => g (i x)); split.
    + apply in_map_iff; exists g; auto.
    + intros x.
      red in H2.
      rewrite <- (Hji x) at 1; auto.
  Qed.

End fun_finite_t_upto.

Section dec_pred_finite_t_upto.

  Variable (X : Type) (HX1 : finite_t X) (HX2 : discrete X).

  Hint Resolve finite_t_bool.

  Let bool_prop (f : X -> bool) : { p : X -> Prop & forall x, decidable (p x) }.
  Proof.
    exists (fun x => f x = true).
    intro; apply bool_dec.
  Defined.

  Theorem pred_finite_t_upto : finite_t_upto { p : X -> Prop & forall x, decidable (p x) }
                               (fun p q => prop_ext (projT1 p) (projT1 q)).
  Proof.
    destruct fun_finite_t_upto with X bool as (l & Hl); auto.
    exists (map bool_prop l).
    intros (p & Hp).
    destruct (Hl (fun x => if Hp x then true else false)) as (f & H1 & H2).
    exists (bool_prop f); split.
    + apply in_map_iff; exists f; auto.
    + simpl; intros x; red in H2.
      rewrite <- H2.
      destruct (Hp x); split; auto; discriminate.
  Qed.

End dec_pred_finite_t_upto.

Section enum_val.

  Variable (X : Type) 
           (HX1 : finite_t X)
           (HX2 : discrete X) (x : X).

  Implicit Type (ln : list nat).

  Let R ln : (nat -> X) -> (nat -> X) -> Prop.
  Proof.
    intros f g.
    exact ( forall n, In n ln -> f n = g n ).
  Defined.

  Let combine (n : nat) : (X * (nat -> X)) -> nat -> X.
  Proof.
    intros (x', f) m.
    destruct (eq_nat_dec n m).
    + exact x'.
    + apply (f m).
  Defined.

  Theorem enum_valuations ln : finite_t_upto _ (R ln).
  Proof.
    induction ln as [ | n ln IH ].
    + exists ((fun _ => x)::nil).
      intros f; exists (fun _ => x); split; simpl; auto.
      intros ? [].
    + destruct HX1 as (l & Hl).
      destruct IH as (m & Hm).
      exists (map (combine n) (list_prod l m)).
      intros f.
      destruct (Hm f) as (g & H1 & H2).
      exists (combine n (f n,g)); split.
      * apply in_map_iff; exists (f n,g); split; auto.
        apply list_prod_spec; auto.
      * intros n' [ <- | Hn' ].
        - unfold combine.
          destruct (eq_nat_dec n n) as [ | [] ]; auto.
        - unfold combine.
          destruct (eq_nat_dec n n') as [ E | D ]; auto.
  Qed.

End enum_val.

Section enum_sig.

  Variable (syms : Type) (ar : syms -> nat) (Hsyms : discrete syms)
           (X : Type) 
           (HX1 : finite_t X)
           (HX2 : discrete X)
           (Y : Type) (HY : finite_t Y) (y : Y).

  Implicit Type (ls : list syms).

  Let R ls : (forall s, vec X (ar s) -> Y) -> (forall s, vec X (ar s) -> Y) -> Prop.
  Proof.
    intros s1 s2.
    exact ( (forall s, In s ls -> forall v, @s1 s v = s2 s v) ).
  Defined.

  Hint Resolve finite_t_vec vec_eq_dec.

  Let funs := forall s, vec X (ar s) -> Y.

  Let fun_combine s (f : vec X (ar s) -> Y) (g : funs) : funs.
  Proof.
    intros s'.
    destruct (Hsyms s s').
    + subst s; exact f.
    + apply g.
  Defined. 

  Theorem enum_sig ls : finite_t_upto funs (R ls).
  Proof.
    induction ls as [ | s ls IH ].
    + exists ((fun _ _ => y) :: nil).
      intros f; exists (fun _ _ => y); split; simpl; auto.
      intros ? [].
    + destruct IH as (m & Hm).
      destruct fun_finite_t_upto with (vec X (ar s)) Y
        as (l & Hl); auto.
      exists (map (fun p => fun_combine (fst p) (snd p)) (list_prod l m)).
      intros f.
      destruct (Hl (f s)) as (f' & H1 & H2).
      destruct (Hm f) as (g & H3 & H4).
      exists (fun_combine f' g); split.
      * apply in_map_iff; exists (f',g); split; auto.
        apply list_prod_spec; simpl; auto.
      * intros s' [ <- | Hs ] v.
        - red in H2; rewrite H2.
           unfold fun_combine.
           destruct (Hsyms s s) as [ E | [] ]; auto.
           rewrite (UIP_dec Hsyms E eq_refl); auto.
        - unfold fun_combine.
          destruct (Hsyms s s') as [ E | D ].
          ++ subst; cbn; apply H2.
          ++ apply H4; auto.
  Qed.

End enum_sig.
