From Undecidability.L Require Import Computability.MuRec.
From Undecidability.L.Datatypes Require Import LNat LOptions LProd Lists.
From Undecidability Require Import FOL.DecidableEnumerable FOL.Reductions. 

Inductive is_computable {A} {t : TT A} (a : A) : Prop :=
  C : computable a -> is_computable a.

Notation enumerates f p := (forall x, p x <-> exists n : nat, f n = Some x).

Definition L_decidable {X} `{registered X} (P : X -> Prop) :=
  exists f : X -> bool, is_computable f /\ forall x, P x <-> f x = true.

Definition L_enumerable {X} `{registered X} (p : X -> Prop) := 
  exists f : nat -> option X, is_computable f /\ (enumerates f p).

Definition L_recognisable {X} `{registered X} (p : X -> Prop) :=
  exists s : term, forall x, p x <-> converges (s (enc x)).

Section L_enum_rec.

  Variable X : Type.
  Context `{registered X}.
  Variable (p : X -> Prop).

  Hypotheses (f : nat -> option X) (c_f : computable f) (H_f : enumerates f p).
  Hypotheses (d : X -> X -> bool) (c_d : computable d) (H_d : forall x y, reflect (x = y) (d x y)).

  Definition test := (fun x n => match f n with Some y => d x y | None => false end).

  Instance term_test : computable test.
  Proof.
    extract.
  Qed.
  
  Lemma proc_test (x : X) :
    proc (λ y, !!(ext test) !!(enc x) y).
  Proof.
    cbn. Lproc.
  Qed.
    
  Lemma L_enumerable_recognisable :
    L_recognisable p.
  Proof.
    exists (λ x, !!mu (λ y, !!(ext test) x y)).
    intros. split; intros.
    - eapply H_f in H0 as [n H0].
      edestruct (mu_complete (proc_test x)) with (n := n).
      + intros. exists (test x n0). cbn. Lsimpl.
      + cbn. Lsimpl. unfold test. rewrite H0. Lsimpl. destruct (H_d x x); intuition.
      + exists (ext x0). split; try Lproc.
        cbn. Lsimpl. now rewrite H1.
    - destruct H0 as (v & ? & ?).
      edestruct (mu_sound (proc_test x)) with (v := v) as (n & ? & ? & _).
      + intros. exists (test x n). cbn. Lsimpl.
      + Lproc.
      + rewrite <- H0. symmetry. cbn. Lsimpl.
      + subst. eapply H_f. exists n.
        assert ((λ y, !! (ext test) !! (enc x) y) !!(ext n) == ext (test x n)).
        cbn. Lsimpl. rewrite H2 in *.
        eapply unique_normal_forms in H3; try Lproc.
        eapply inj_enc in H3.
        unfold test in H3. destruct (f n); inv H3.
        destruct (H_d x x0); firstorder.
  Qed.

End L_enum_rec.
  
Definition L_nat := (fix f n := match n with 0 => [0] | S n => f n ++ [S n] end)%list.

Instance term_L_nat : computable L_nat.
Proof.
  extract.
Qed.

Definition T_nat_nat := Eval cbn in @L_T (nat * nat) _.

Definition pair' : nat * nat -> nat * nat := fun '(x,y) => (x,y).

Instance term_pair' : computable pair'.
Proof.
  extract.
Qed.

Instance term_T_nat_nat : computable T_nat_nat.
Proof.
  change (computable
    (fix T_prod (n : nat) : list (nat * nat) :=
       match n with
       | 0 => [(0, 0)]
       | S n0 =>
           (T_prod n0 ++ map pair' (L_nat n0 × L_nat n0))%list
       end)).
  extract.
Qed.

Instance term_R_nat_nat : computable R_nat_nat.
Proof.
  change (computable (fun n : nat => nthe n (T_nat_nat n))).
  extract.
Qed.

Definition lenumerates {X} L (p : X -> Prop) :=
  cumulative L /\ (forall x : X, p x <-> (exists m : nat, x el L m)).

Definition L_enum {X} `{registered X} (p : X -> Prop) :=
  exists L, is_computable L /\ lenumerates L p.

Instance term_ofNat X `{registered X} :
  computable (@ofNat X).
Proof.
  extract.
Qed.

Lemma projection X Y {HX : registered X} {HY : registered Y} (p : X * Y -> Prop) :
  L_enumerable p -> L_enumerable (fun x => exists y, p (x,y)).
Proof.
  intros (f & [cf] & ?).
  exists (fun n => match f n with Some (x, y) => Some x | None => None end).
  split.
  - econstructor. extract.
  - intros; split.
    + intros [y ?]. eapply H in H0 as [n]. exists n. now rewrite H0.
    + intros [n ?]. destruct (f n) as [ [] | ] eqn:E; inv H0.
      exists y. eapply H. eauto.
Qed.

Lemma L_enumerable_ext X `{registered X} p q : L_enumerable p -> (forall x : X, p x <-> q x) -> L_enumerable q.
Proof.
  intros (f & cf & Hf) He. exists f; split; eauto.
  intros ?. rewrite <- He. eapply Hf.
Qed.  

Lemma L_enumerable_enum {X} `{registered X} (p : X -> Prop) :
  L_enum p -> L_enumerable p.
Proof.
  intros (f & [cf] & Hf).
  exists (@ofNat X f). split.
  - econstructor. extract.
  - destruct Hf as [CX HX].
    intros. rewrite HX.
    + split; intros [n].
      * eapply In_nth_error in H0 as [m].
        destruct (pairs_retract (m, n)) as [k]. exists k. unfold ofNat. now rewrite H1.
      * unfold ofNat in *. destruct R_nat_nat as [ [] | ].
        eapply nth_error_In in H0. eauto. inv H0.
Qed.

Lemma L_enumerable_halt {X} `{registered X} (p : X -> Prop) :
  L_decidable (X := X * X) (fun '(x,y) => x = y) ->
  L_enumerable p -> p ⪯ converges.
Proof.
  intros (d & [c_d] & H_d) (f & [c_f] & H_f).
  edestruct L_enumerable_recognisable with (p := p) (d := fun x y => d (x,y)) (f := f); eauto.
  - extract.
  - intros. specialize (H_d (x,y)). destruct (d (x,y)); intuition.
  - now exists (fun x0 => x (enc x0)). 
Qed.  

