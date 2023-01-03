(* ** Arithmetical Hierarchy in Type Theory *)

From Undecidability.Shared Require Import embed_nat.
Require Import Lia Vector Fin List.
Import Vector.VectorNotations.
From Undecidability.Synthetic Require Import Definitions.

Require Import PeanoNat (* Nat.eqb *) Bool.

From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Local Notation vec := Vector.t.
Derive Signature for vec.

Lemma eqhd : forall (x:nat) n (v: vec nat n), (VectorDef.hd (x :: v)) = x. Proof. reflexivity. Qed.
Lemma eqtl : forall (x:nat) n (v: vec nat n), (VectorDef.tl (x :: v)) = v. Proof. reflexivity. Qed.

Notation "P ⪯ₘ Q" := (reduces P Q) (at level 70).

Section ArithmeticalHierarchySemantic.

  (* ((vec nat k) -> Prop) punktweise gleich -> gleich *)
  (* und äquivalente Prop sind gleich *)
  Lemma fun_ext_prop_ext:
    (forall {X Y} (f g : X -> Y), (forall x, f x = g x) -> f = g) ->
    (forall (p q : Prop), (p <-> q) -> p = q) ->
    forall {k} (f g:(vec nat k) -> Prop) , (forall v, f v <-> g v) -> f = g.
  Proof.
    intros Fext Pext k f g H.
    apply Fext. intros x. apply Pext. apply H.
  Qed.

  Axiom PredExt : forall (k : nat) (f g : vec nat k -> Prop), (forall v : vec nat k, f v <-> g v) -> f = g.

  Inductive isΣsem : nat -> forall (k: nat), ((vec nat k) -> Prop) -> Prop :=
  | isΣsem0 {k} (f: vec nat k -> bool) : isΣsem 0 (fun v => f v = true)
  | isΣsemS {n} {k} {p: vec nat (S k) -> Prop} : @isΠsem n (S k) p -> @isΣsem (S n) k (fun v => exists x, p (x::v))
  
  with isΠsem : nat -> forall (k: nat), ((vec nat k) -> Prop) -> Prop :=
  | isΠsem0 {k} (f: vec nat k -> bool) : isΠsem 0 (fun v => f v = true)
  | isΠsemS {n} {k} {p: vec nat (S k) -> Prop} : @isΣsem n (S k) p -> @isΠsem (S n) k (fun v => forall x, p (x::v)).

  Derive Signature for isΣsem.
  Derive Signature for isΠsem.
  #[local] Hint Constructors isΣsem : core.
  #[local] Hint Constructors isΠsem : core.

  (* generacte induction scheme *)
  Scheme isΣsem_isΠsem_ind := Induction for isΣsem Sort Prop
  with isΠsem_isΣsem_ind := Induction for isΠsem Sort Prop.
  (* https://coq.inria.fr/refman/proofs/writing-proofs/reasoning-inductives.html#combined-scheme *)
  Combined Scheme isΣsem_isΠsem_mutind from isΣsem_isΠsem_ind,isΠsem_isΣsem_ind.

  Lemma curry {k} t: (nat -> vec nat k -> t) -> vec nat (S k) -> t.
  Proof.
    intros P v.
    inversion v as [|n k' v' eq]. subst.
    exact (P n v').
  Defined.

  Lemma curry0 t : t -> vec nat 0 -> t.
  Proof.
    intros P v. apply P.
  Defined.

  Lemma curry1 t: (nat -> t) -> vec nat 1 -> t.
  Proof.
    intros P. apply curry. intros n. apply curry0. exact (P n).
  Defined.

  Lemma curry2 t: (nat -> nat -> t) -> vec nat 2 -> t.
  Proof.
    intros P. apply curry. intros n. apply curry1. exact (P n).
  Defined.

  Goal isΣsem 1 (curry1 (fun n => exists k, n = 2 * k)).
  Proof.
    erewrite PredExt.
    - eapply isΣsemS. unshelve apply isΠsem0.
      apply curry2. intros k n.
      exact (n =? (2*k)).
    - intros v.
      repeat dependent destruction v.
      cbn. unfold curry0.
      split.
      + intros [k H]. exists k. now apply Nat.eqb_eq.
      + intros [k H]. exists k. now apply Nat.eqb_eq.
  Qed.

  Lemma semi_dec_iff_Σ1 {k} (p : vec nat k -> Prop):
    semi_decidable p <-> isΣsem 1 p.
  Proof.
  unfold semi_decidable, semi_decider.
  split.
  - intros [f Hf].
    rewrite (PredExt Hf).
    unshelve erewrite PredExt. {
      exact (fun v => exists n, (fun v => (fun v => f (Vector.tl v) (Vector.hd v)) v = true) (n::v)).
    } 2: reflexivity. eapply isΣsemS, isΠsem0.
  - intros H. repeat dependent destruction H.
    now exists (fun v n => f (n::v)).
  Qed.

  Lemma isΣΠsem0 {k} (f: vec nat k -> bool) n :
    isΣsem n (fun v => f v = true) /\ isΠsem n (fun v => f v = true).
  Proof.
    induction n in k, f |-*.
    - split; apply isΣsem0 + apply isΠsem0.
    - split.
      + rewrite PredExt with (g := fun v => exists x, f (Vector.tl (x::v)) = true) by firstorder.
        change (isΣsem (S n) (fun v => exists x, (fun v => f (Vector.tl v) = true) (x::v))).
        apply isΣsemS. apply IHn.
      + rewrite PredExt with (g := fun v => forall x, f (Vector.tl (x::v)) = true) by firstorder.
        change (isΠsem (S n) (fun v => forall x, (fun v => f (Vector.tl v) = true) (x::v))).
        apply isΠsemS. apply IHn.
  Qed.

  Lemma isΣΠn_In_ΣΠSn l :
    (forall n k (p: vec nat k -> Prop), isΣsem n p -> isΣsem (l + n) p)
/\  (forall n k (p: vec nat k -> Prop), isΠsem n p -> isΠsem (l + n) p).
  Proof.
    apply isΣsem_isΠsem_mutind; intros.
    all: try apply isΣΠsem0.
    all: replace (l + S n) with (S l + n) by lia.
    all: now constructor.
  Qed.

  Lemma isΣsem_m_red_closed : 
    (forall n k (q: vec nat k -> Prop), isΣsem n q -> forall k' (p : vec nat k' -> Prop), p ⪯ₘ q -> isΣsem n p)
/\  (forall n k (q: vec nat k -> Prop), isΠsem n q -> forall k' (p : vec nat k' -> Prop), p ⪯ₘ q -> isΠsem n p).
  Proof.
    apply isΣsem_isΠsem_mutind.
    - intros k f k' p [e He].
      erewrite PredExt. 2: apply He. apply isΣsem0.
    - intros n k q Πq IH k' p [e He].
      erewrite PredExt. 2: apply He.
      unshelve erewrite PredExt. 2: eapply isΣsemS, IH.
      + exists (fun v => (Vector.hd v)::(e (Vector.tl v))).
        intros x. split; intros H; apply H.
      + reflexivity.
    - intros k f k' p [e He].
      erewrite PredExt. 2: apply He. apply isΠsem0.
    - intros n k q Πq IH k' p [e He].
      erewrite PredExt. 2: apply He.
      unshelve erewrite PredExt. 2: eapply isΠsemS, IH.
      + exists (fun v => (Vector.hd v)::(e (Vector.tl v))).
        intros x. split; intros H; apply H.
      + reflexivity.
  Qed.

  Lemma isΣsemTwoEx k n (p : vec nat (S (S k)) -> Prop):
    isΠsem n p -> isΣsem (S n) (fun v => exists y x : nat, p (x :: y :: v)).
  Proof.
    intros H.
    unshelve eapply isΣsem_m_red_closed in H.
    2: exact (fun v => let (x, y) := unembed (VectorDef.hd v) in p (x :: y :: VectorDef.tl v)).
    2: {
      exists (fun v => let (x, y) := unembed (VectorDef.hd v) in x :: y :: Vector.tl v).
      intros v. destruct unembed. reflexivity.
    }
    apply isΣsemS in H. erewrite PredExt. { apply H. }
    intros v. cbv beta. split.
    - intros [y [x Hp]]. exists (embed (x, y)).
      now rewrite eqhd, eqtl, embedP.
    - intros [m Hp]. destruct (unembed m) as [x y] eqn:eq. exists y, x.
      now rewrite eqhd, eqtl, eq in Hp.
  Qed.

  Lemma isΣsemE k n (p : vec nat (S k) -> Prop):
    isΣsem (S n) p -> isΣsem (S n) (fun v => exists x : nat, p (x :: v)).
  Proof.
    intros H. dependent destruction H.
    now apply isΣsemTwoEx.
  Qed.

  Lemma isΠsemTwoAll k n (p : vec nat (S (S k)) -> Prop):
    isΣsem n p -> isΠsem (S n) (fun v => forall y x : nat, p (x :: y :: v)).
  Proof.
    intros H.
    unshelve eapply isΣsem_m_red_closed in H.
    2: exact (fun v => let (x, y) := unembed (VectorDef.hd v) in p (x :: y :: VectorDef.tl v)).
    2: {
      exists (fun v => let (x, y) := unembed (VectorDef.hd v) in x :: y :: Vector.tl v).
      intros v. destruct unembed. reflexivity.
    }
    apply isΠsemS in H. erewrite PredExt. { apply H. }
    intros v. cbv beta. split.
    - intros Hp m. rewrite eqhd, eqtl.
      now destruct (unembed m) as [x y] eqn:eq.
    - intros Hp y x. specialize (Hp (embed (x, y))).
      now rewrite eqhd, eqtl, embedP in Hp.
  Qed.

  Lemma isΠsemA k n (p : vec nat (S k) -> Prop):
    isΠsem (S n) p -> isΠsem (S n) (fun v => forall x : nat, p (x :: v)).
  Proof.
    intros H. dependent destruction H.
    now apply isΠsemTwoAll.
  Qed.

  Lemma isΣΠn_In_ΠΣSn :
    (forall n k (p: vec nat k -> Prop), isΣsem n p -> isΠsem (S n) p)
/\  (forall n k (p: vec nat k -> Prop), isΠsem n p -> isΣsem (S n) p).
  Proof.
    split; intros n k p H.
    - eapply isΣsem_m_red_closed in H.
      2: { exists (fun v => Vector.tl v). intros v. split; intros pv; apply pv. }
      apply isΠsemS in H. erewrite PredExt. 1: apply H. firstorder.
    - eapply isΣsem_m_red_closed in H.
      2: { exists (fun v => Vector.tl v). intros v. split; intros pv; apply pv. }
      apply isΣsemS in H. erewrite PredExt. 1: apply H. firstorder.
  Qed.

  Lemma isΣsem_and_closed n :
    (forall k (p: vec nat k -> Prop), isΣsem n p -> forall (q : vec nat k -> Prop), isΣsem n q -> isΣsem n (fun v => p v /\ q v))
/\  (forall k (p: vec nat k -> Prop), isΠsem n p -> forall (q : vec nat k -> Prop), isΠsem n q -> isΠsem n (fun v => p v /\ q v)).
  Proof.
    induction n as [|n IH].
    - split.
      + intros k p Hp q Hq. dependent destruction Hp. dependent destruction Hq.
        rewrite PredExt with (g := fun v => f0 v && f v = true) by now setoid_rewrite andb_true_iff.
        apply isΣsem0.
      + intros k p Hp q Hq. dependent destruction Hp. dependent destruction Hq.
        rewrite PredExt with (g := fun v => f0 v && f v = true) by now setoid_rewrite andb_true_iff.
        apply isΠsem0.
    - split; intros k p Hp q Hq; dependent destruction Hp; dependent destruction Hq.
      + unshelve erewrite PredExt; [exact (fun v => exists y x : nat, (fun v => p (Vector.hd v:: Vector.tl (Vector.tl v)) /\ p0 (Vector.hd (Vector.tl v)::Vector.tl (Vector.tl v))) (x::y::v))| | firstorder].
       apply isΣsemTwoEx. apply IH.
        * eapply isΣsem_m_red_closed. { apply H0. }
          now exists (fun v => (Vector.hd v :: Vector.tl (Vector.tl v))).
        * eapply isΣsem_m_red_closed. { apply H. }
          now exists (fun v => Vector.hd (Vector.tl v) :: Vector.tl (Vector.tl v)).
      + unshelve erewrite PredExt; [exact (fun v => forall y x : nat, (fun v => p (Vector.hd v:: Vector.tl (Vector.tl v)) /\ p0 (Vector.hd (Vector.tl v)::Vector.tl (Vector.tl v))) (x::y::v))| | firstorder].
        apply isΠsemTwoAll. apply IH.
        * eapply isΣsem_m_red_closed. { apply H0. }
          now exists (fun v => (Vector.hd v :: Vector.tl (Vector.tl v))).
        * eapply isΣsem_m_red_closed. { apply H. }
          now exists (fun v => Vector.hd (Vector.tl v) :: Vector.tl (Vector.tl v)).
  Qed.

  Variable vec_to_nat : forall k, vec nat k -> nat.
  Variable nat_to_vec : forall k, nat -> vec nat k.
  Variable vec_nat_inv : forall k v, nat_to_vec k (vec_to_nat v) = v.
  Variable nat_vec_inv : forall k n, vec_to_nat (nat_to_vec k n) = n.

  Variable list_vec_to_nat : forall k, list (vec nat k) -> nat.
  Variable nat_to_list_vec : forall k, nat -> list (vec nat k).
  Variable list_vec_nat_inv : forall k v, nat_to_list_vec k (list_vec_to_nat v) = v.
  Variable nat_list_vec_inv : forall k n, list_vec_to_nat (nat_to_list_vec k n) = n.

  Lemma isΣΠball n :
    (forall k (p : vec nat (S k) -> Prop), isΣsem n p -> isΣsem n (fun v => forall l, l < (Vector.hd v) -> p (l::(Vector.tl v))))
/\  (forall k (p : vec nat (S k) -> Prop), isΠsem n p -> isΠsem n (fun v => forall l, l < (Vector.hd v) -> p (l::(Vector.tl v)))).
  Proof.
    induction n as [|n [IH1 IH2]]; split; intros k p H; dependent destruction H.
    - unshelve erewrite PredExt with (g := fun v => (fix f' n v := match n with 0 => true | S n => f(n::v) && f' n v end)(Vector.hd v)(Vector.tl v) = true). 1: apply isΣsem0.
      intros v. dependent destruction v. clear.
      rewrite eqhd, eqtl. induction h as [|n IH].
      + split; lia.
      + split.
        * intros H. apply andb_true_iff. split; [apply H;lia|]. apply IH. intros l H'. apply H. lia.
        * intros [H H']%andb_true_iff. intros l le. assert (l = n \/ l < n) as [->|] by lia; [apply H | now apply IH].
    - unshelve erewrite PredExt with (g := fun v => (fix f' n v := match n with 0 => true | S n => f(n::v) && f' n v end)(Vector.hd v)(Vector.tl v) = true). 1: apply isΠsem0.
      intros v. dependent destruction v. clear.
      rewrite eqhd, eqtl. induction h as [|n IH].
      + split; lia.
      + split.
        * intros H. apply andb_true_iff. split; [apply H;lia|]. apply IH. intros l H'. apply H. lia.
        * intros [H H']%andb_true_iff. intros l le. assert (l = n \/ l < n) as [->|] by lia; [apply H | now apply IH].
    - unshelve erewrite PredExt.
        1: exact (fun v =>
        exists L : nat,
        (fun v => let L := Vector.hd v in let N := Vector.hd (Vector.tl v) in let v := Vector.tl (Vector.tl v) in
          (fun v =>
            forall (l : nat), l < Vector.hd v ->
              (fun v =>
                let l := Vector.hd v in
                let N := Vector.hd (Vector.tl v) in
                let L := Vector.hd (Vector.tl (Vector.tl v)) in
                let v := Vector.tl (Vector.tl (Vector.tl v)) in
                let L' := nat_to_vec N L in
                let xl := match Compare_dec.lt_dec l N with left lt => Vector.nth L' (of_nat_lt lt) | right _ => 42 end in
                  (fun v => p0 (Vector.tl v))(N::xl::l::v)
              )(l::v)
          )(N::L::v)
        )(L::v)).
      2: { 
        clear n IH1 IH2 H. intros v. cbn. dependent destruction v. rewrite eqhd. rewrite eqtl.
        induction h as [|n [IH1 IH2]].
        - firstorder lia.
        - split.
          + intros H. specialize (IH1 ltac:(intros l leq; apply H; lia)) as [L Hl].
            remember (nat_to_vec n L) as L'. destruct (H n ltac:(lia)) as [x Hx].
            exists (vec_to_nat(Vector.shiftin x L')). intros l lt. rewrite vec_nat_inv.
            destruct Compare_dec.lt_dec as [lt'|]; [|contradiction].
            assert (l = n \/ l < n) as [->|lt''] by lia.
            * enough ((shiftin x L')[@of_nat_lt lt'] = x) as -> by assumption.
              clear. induction L' as [|y k' L' IH]; [reflexivity|apply IH].
            * enough ((shiftin x L')[@of_nat_lt lt'] = L'[@of_nat_lt lt'']) as ->. { specialize (Hl l lt''). destruct Compare_dec.lt_dec;[|contradiction]. erewrite of_nat_ext. eauto. }
              clear. induction L' in l, lt', lt'' |-*; induction l; try lia + reflexivity + apply IHL'.
          + intros [L H] l lt. eexists. now apply H.
      }
      remember (fun v =>
        let l := Vector.hd v in
        let N := Vector.hd (Vector.tl v) in
        let L := Vector.hd (Vector.tl (Vector.tl v)) in
        let v := Vector.tl (Vector.tl (Vector.tl v)) in
        let L' := nat_to_vec N L in
        let xl := match Compare_dec.lt_dec l N with left lt => Vector.nth L' (of_nat_lt lt) | right _ => 42 end in
          (fun v => p0 (Vector.tl v))(N::xl::l::v)
      ) as p'.
      remember (fun v => forall (l : nat), l < Vector.hd v -> p'(l::v)) as p''.
      apply isΣsemS.
      unshelve eapply isΣsem_m_red_closed. 2: apply p''. 2: {
        exists (fun v => let L := Vector.hd v in
        let N := Vector.hd (Vector.tl v) in
        let v := Vector.tl (Vector.tl v) in (N :: L :: v)).
        intros v. now do 2 dependent destruction v.
      }
      rewrite Heqp''. specialize (IH2 _ p'). cbn in IH2.
      eapply isΣsem_m_red_closed. 1: apply IH2. 2: {
        exists (fun v => (Vector.hd v)::(Vector.hd v)::(Vector.tl v)).
        intros v. now dependent destruction v.
      }
      rewrite Heqp'.
      eapply isΣsem_m_red_closed. apply H.
      exists (fun v : vec nat (S (S (S k))) =>
      let l := Vector.hd v in
      let N := Vector.hd (Vector.tl v) in
      let L := Vector.hd (Vector.tl (Vector.tl v)) in
      let v0 := Vector.tl (Vector.tl (Vector.tl v)) in
      let L' := nat_to_vec N L in
      let xl :=
        match Compare_dec.lt_dec l N with
        | left lt => L'[@of_nat_lt lt]
        | right _ => 42
        end in Vector.tl (N :: xl :: l :: v0)).
      now intros.
  - unshelve erewrite PredExt. {
      exact (fun v =>
      forall L : nat,
      (fun v => let L := Vector.hd v in let N := Vector.hd (Vector.tl v) in let v := Vector.tl (Vector.tl v) in
        (fun v =>
          forall (l : nat), l < Vector.hd v ->
            (fun v =>
              let l := Vector.hd v in
              let N := Vector.hd (Vector.tl v) in
              let L := Vector.hd (Vector.tl (Vector.tl v)) in
              let v := Vector.tl (Vector.tl (Vector.tl v)) in
              let L' := nat_to_vec N L in
              let xl := match Compare_dec.lt_dec l N with left lt => Vector.nth L' (of_nat_lt lt) | right _ => 42 end in
                (fun v => p0 (Vector.tl v))(N::xl::l::v)
            )(l::v)
        )(N::L::v)
      )(L::v)).
    } 2: { 
      clear n IH1 IH2 H. intros v. cbn. dependent destruction v. rewrite eqhd, eqtl.
      induction h as [|n [IH1 IH2]].
      - firstorder lia.
      - split.
        + firstorder.
        + intros H l lt x.
          specialize (H (vec_to_nat (Vector.const x (S n))) l lt).
          rewrite vec_nat_inv in H. destruct Compare_dec.lt_dec; [|lia].
          now rewrite Vector.const_nth in H.
    }
    remember (fun v =>
      let l := Vector.hd v in
      let N := Vector.hd (Vector.tl v) in
      let L := Vector.hd (Vector.tl (Vector.tl v)) in
      let v := Vector.tl (Vector.tl (Vector.tl v)) in
      let L' := nat_to_vec N L in
      let xl := match Compare_dec.lt_dec l N with left lt => Vector.nth L' (of_nat_lt lt) | right _ => 42 end in
        (fun v => p0 (Vector.tl v))(N::xl::l::v)
    ) as p'.
    remember (fun v => forall (l : nat), l < Vector.hd v -> p'(l::v)) as p''.
    apply isΠsemS.
    unshelve eapply isΣsem_m_red_closed. 2: apply p''. 2: {
      exists (fun v => let L := Vector.hd v in
      let N := Vector.hd (Vector.tl v) in
      let v := Vector.tl (Vector.tl v) in (N :: L :: v)).
      intros v. now do 2 dependent destruction v.
    }
    rewrite Heqp''. specialize (IH1 _ p').
    eapply isΣsem_m_red_closed. 1: apply IH1. 2: {
      exists (fun v => (Vector.hd v)::(Vector.hd v)::(Vector.tl v)).
      intros v. now dependent destruction v.
    }
    rewrite Heqp'.
    eapply isΣsem_m_red_closed. apply H.
    exists (fun v : vec nat (S (S (S k))) =>
    let l := Vector.hd v in
    let N := Vector.hd (Vector.tl v) in
    let L := Vector.hd (Vector.tl (Vector.tl v)) in
    let v0 := Vector.tl (Vector.tl (Vector.tl v)) in
    let L' := nat_to_vec N L in
    let xl :=
      match Compare_dec.lt_dec l N with
      | left lt => L'[@of_nat_lt lt]
      | right _ => 42
      end in Vector.tl (N :: xl :: l :: v0)).
    now intros.
  Qed.

  Lemma isΣsemListΣ {k k'} (p : vec nat k -> Prop) n: 
    (isΣsem n p -> isΣsem n
      (fun v : vec nat (S k') =>
        List.Forall p (nat_to_list_vec k (Vector.hd v))))
  /\
    (isΠsem n p -> isΠsem n
      (fun v : vec nat (S k') =>
        List.Forall p (nat_to_list_vec k (Vector.hd v)))).
  Proof.
    assert ((fun v : vec nat (S k') => Forall p (nat_to_list_vec k (Vector.hd v)))
    ⪯ₘ (fun v : vec nat (S (S k')) =>
        forall l : nat,
        l < Vector.hd v ->
        (fun v0 : vec nat (S (S k')) =>
         p (nth (Vector.hd v0) (nat_to_list_vec k (Vector.hd (Vector.tl v0))) (const 42 k)))
          (l :: Vector.tl v))) as mred. {
      exists (fun v => (length (nat_to_list_vec k (Vector.hd v)))::v).
      intros v. dependent destruction v. cbn.
      remember (nat_to_list_vec k h) as L. clear.
      rewrite List.Forall_forall. split.
      - intros H l lt. apply H. now apply List.nth_In.
      - intros H x i. eapply List.In_nth in i as [l [lt <-]]. now apply H. 
    }
    split. all: intros H.
    all: unshelve eapply isΣsem_m_red_closed. 2, 4: exact (
      fun v : vec nat (S (S k')) =>
        forall l : nat,
        l < (Vector.hd v) ->
        (fun v => 
          p (List.nth (Vector.hd v) (nat_to_list_vec k (Vector.hd (Vector.tl v))) (const 42 k)))(l:: Vector.tl v)
    ).
    2, 4: apply mred.
    all: apply isΣΠball.
    all: eapply isΣsem_m_red_closed.
    1, 3: apply H.
    all: eexists; intros v; split; apply (fun x => x).
  Qed.

  (* Σ and Π are complements **)

  Definition DN := forall P, ~~P -> P.

  Definition Markov: Prop :=
    forall f: nat -> bool, ~(forall x, f x = false) -> exists n, f n = true.
  
  Lemma Markov_Forster:
    Markov <-> forall f : nat -> bool, ~~ (exists n, f n = true) -> exists n, f n = true.
  Proof.
    unfold Markov. split.
    - intros MP f nnE. apply MP. intros A. apply nnE. intros [n Hn]. congruence.
    - intros MP f nA. apply MP.
      intros nE. apply nA. intros x. destruct f eqn:eq.
      + exfalso. apply nE. now exists x.
      + reflexivity.
  Qed.

  Lemma DN_Markov : DN -> Markov.
  Proof.
    unfold DN, Markov.
    intros DN. intros f nA.
    assert (~(forall x, ~(f x = true))). {
      intros A. apply nA. intros x. specialize (A x). now destruct f.
    }
    apply DN. firstorder.
  Qed.
  
  Lemma Σ0sem_notΠ0_int :
    (forall k (p : vec nat k -> Prop), isΣsem 0 p -> isΠsem 0 (fun v => ~ (p v)))
 /\ (forall k (p : vec nat k -> Prop), isΠsem 0 p -> isΣsem 0 (fun v => ~ (p v))).
  Proof.
    split.
    all: intros k p H; inversion H.
    all: assert ((fun v : vec nat k => f v <> true) = (fun v : vec nat k => (fun v => if f v then false else true) v = true)) as -> by (apply PredExt; intros; now destruct f).
    all: constructor.
  Qed.
  
  Lemma int_notEx_Allnot {X} k (p: vec X (S k) -> Prop):
    forall v, (~(exists x, p (x::v)) <-> (forall x, ~p (x::v))).
  Proof. clear. firstorder. Qed.

  Lemma Σ1sem_notΠ1_int :
    forall k (p : vec nat k -> Prop), isΣsem 1 p -> isΠsem 1 (fun v => ~ (p v)).
  Proof.
    intros k p H.
    dependent destruction H.
    erewrite PredExt. 2: apply int_notEx_Allnot.
    change (isΠsem 1 (fun v : vec nat k => forall x : nat, (fun v => ~ p0 v )(x :: v))).
    apply isΠsemS.
    now apply Σ0sem_notΠ0_int.
  Qed.

  Lemma Π1sem_notΣ1_MP :
    Markov -> forall k (p : vec nat k -> Prop), isΠsem 1 p -> isΣsem 1 (fun v => ~ (p v)).
  Proof.
    unfold Markov. intros Markov k p H.
    dependent destruction H.
    dependent destruction H.
    replace (fun v : vec nat k => ~ (forall x : nat, f (x :: v) = true)) with (fun v : vec nat k => exists x : nat, (fun v => (if f v then false else true) = true)(x :: v)).
    - change (isΣsem 1 (fun v : vec nat k => exists x : nat, (fun v => (if f v then false else true) = true)(x :: v))). apply isΣsemS, isΠsem0.
    - apply PredExt. intros v. split.
      + intros [x H] nA. specialize (nA x). rewrite nA in H. discriminate.
      + intros nA. apply Markov. intros H. apply nA. intros x. specialize (H x). now destruct f.
  Qed.

  Lemma Π1sem_notΣ1_MP_inv :
    (forall k (p : vec nat k -> Prop), isΠsem 1 p -> isΣsem 1 (fun v => ~ (p v))) -> Markov.
  Proof.
    intros H f nA.
      specialize (H 0 (fun v => forall x, (fun v => (fun v => if f (Vector.hd v) then false else true) v = true) (x::v)) ltac:(apply isΠsemS, isΣsem0)).
      cbn in H. repeat dependent destruction H.
      assert ((fun (_:vec nat 0) => ~ (forall x : nat, (if f x then false else true) = true))(Vector.nil nat)) as H. {
        intros nA'. apply nA. intros x. specialize (nA' x). now destruct f.
      }
      rewrite H0 in H. destruct H as [x Hx]. rewrite <- Hx in H0.
      rewrite <- Hx.
      exists x. destruct f eqn:eqf; [easy|].
  Abort.

  Lemma equiv_DN_sdec : 
    (forall k (p : vec nat k -> Prop), semi_decidable p -> semi_decidable (fun v => ~~p v))
    <->
    (forall k (p : vec nat k -> Prop), isΠsem 1 p -> isΣsem 1 (fun v => ~ (p v))).
  Proof.
    split.
    - intros Hsdec k p H. repeat dependent destruction H.
      assert (semi_decidable (fun v => (exists x, f(x::v) = false))) as sdec. {
        unfold semi_decidable, semi_decider.
        exists (fun v x => if f(x::v) then false else true).
        intros v. split.
        - intros [x Hx]. exists x. now destruct f.
        - intros [x Hx]. exists x. now destruct f.
      }
      specialize (Hsdec _ _ sdec) as [f' Hf']. unfold semi_decider in Hf'.
      assert (forall v, ~~(exists x, f (x::v) = false) <-> ~forall x, f(x::v) = true) as eq. {
        enough (forall v, f v = true <-> ~f v = false) as eq by (setoid_rewrite eq; firstorder).
        intros v. now destruct f.
      }
      setoid_rewrite eq in Hf'. apply PredExt in Hf' as ->.
      change (isΣsem 1 (fun v => exists x, (fun v => f' (Vector.tl v) (Vector.hd v) = true) (x::v))).
      apply isΣsemS, isΠsem0.
    - intros H k p [f Hf]. unfold semi_decidable, semi_decider in *.
      assert (isΠsem 1 (fun v => ~p v)) as HΠ. {
        assert (forall x, ~p x <-> forall n, ~f x n = true) as ->%PredExt by firstorder.
        change (isΠsem 1 (fun v => forall x, (fun v => f (Vector.tl v) (Vector.hd v) <> true) (x::v))).
        apply isΠsemS.
        enough (forall v, f (Vector.tl v) (Vector.hd v) <> true <-> (fun v => if f (Vector.tl v) (Vector.hd v) then false else true) v = true) as ->%PredExt by apply isΣsem0.
        intros v. now destruct f.
      }
      specialize (H _ _ HΠ). repeat dependent destruction H.
      exists (fun v x => f0 (x::v)). intros v.
      change ((fun v : vec nat k => ~ ~ p v) v <-> (fun v : vec nat k => exists x : nat, f0 (x :: v) = true) v).
      now rewrite H0.
  Qed.

  Lemma equiv_sdec_functions :
    (forall k alpha, exists beta, forall (x : vec nat k), ~ (forall (n : nat), alpha x n = false) <-> (exists (n : nat), beta x n = true))
    <->
    (forall k (p : vec nat k -> Prop), semi_decidable p -> semi_decidable (fun v => ~~p v)).
  Proof.
    unfold semi_decidable, semi_decider.
    split.
    - intros H k p [f Hf].
      specialize (H _ f) as [f' Hf'].
      exists f'.
      intros x. rewrite <- Hf'.
      rewrite Hf.
      assert (~ (forall n : nat, f x n <> true) <-> ~ ~ (exists n : nat, f x n = true)) as <- by firstorder.
      split. all: intros nA A; apply nA; intros n; specialize (A n); now destruct f.
    - intros H k f.
      specialize (H k (fun v => exists x, f v x = true) ltac:(firstorder)) as [f' Hf'].
      exists f'. setoid_rewrite <- Hf'.
      intros v. assert (~ (forall n : nat, f v n <> true) <-> ~ ~ (exists n : nat, f v n = true)) as <- by firstorder.
      split. all: intros nA A; apply nA; intros n; specialize (A n); now destruct f.
  Qed.

  Goal 
    (forall k alpha, exists beta, forall (x : vec nat k), ~ (forall (n : nat), alpha x n = false) <-> (exists (n : nat), beta x n = true))
    <->
    (forall k (p : vec nat k -> Prop), isΠsem 1 p -> isΣsem 1 (fun v => ~ (p v))).
  Proof. rewrite equiv_sdec_functions. apply equiv_DN_sdec. Qed.

  Lemma negΣinΠsem:
    DN ->
     (forall n k (p: vec nat k -> Prop), isΣsem n p -> isΠsem n (fun v => ~(p v)))
  /\ (forall n k (p: vec nat k -> Prop), isΠsem n p -> isΣsem n (fun v => ~(p v))).
  Proof.
    intros DN.
    apply isΣsem_isΠsem_mutind.
    - intros. apply Σ0sem_notΠ0_int. constructor.
    - intros n k p H IH.
      erewrite PredExt.
      + eapply isΠsemS. apply IH.
      + intros v. split.
        * intros nE. intros x c. apply nE. eexists. apply c.
        * intros A [x nP]. now apply (A x).
    - intros. apply Σ0sem_notΠ0_int. constructor.
    - intros n k p H IH.
      erewrite PredExt.
      + eapply isΣsemS. apply IH.
      + intros v. split.
        * intros nA. apply DN. intros nE.
          apply nA. intros x. apply DN. intros nP.
          apply nE. now exists x.
        * intros [x nP] A. now apply nP.
  Qed.

End ArithmeticalHierarchySemantic.
