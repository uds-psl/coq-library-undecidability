(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Max Lia Wellfounded Bool Eqdep_dec.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import list_focus utils_tac utils_list.

Set Implicit Arguments.

Section le_lt_pirr.

  (* lt and lt are proof irrelevant *)

  (* a dependent induction principle for le *)
  
  Scheme le_indd := Induction for le Sort Prop.

  Theorem le_pirr x y (H1 H2 : x <= y) : H1 = H2.
  Proof.
    revert H2.
    induction H1 as [ | m H1 IH ] using le_indd; intro H2.

    change (le_n x) with (eq_rect _ (fun n' => x <= n') (le_n x) _ eq_refl).
    generalize (eq_refl x).
    pattern x at 2 4 6 10, H2. 
    case H2; [intro E | intros m l E].
    rewrite UIP_dec with (p1 := E) (p2 := eq_refl); auto.
    apply eq_nat_dec.
    contradiction (le_Sn_n m); subst; auto.
    
    change (le_S x m H1) with (eq_rect _ (fun n' => x <= n') (le_S x m H1) _ eq_refl).
    generalize (eq_refl (S m)).
    pattern (S m) at 1 3 4 6, H2.
    case H2; [intro E | intros p H3 E].
    contradiction (le_Sn_n m); subst; auto.
    injection E; intro; subst.
    rewrite (IH H3).
    rewrite UIP_dec with (p1 := E) (p2 := eq_refl); auto.
    apply eq_nat_dec.
  Qed.

  Fact lt_pirr x y (H1 H2 : x < y) : H1 = H2.
  Proof. simpl; intros; apply le_pirr. Qed.

End le_lt_pirr.

Section fin_reif.

  Variable (X : Type) (R : nat -> X -> Prop).

  Fact fin_reif n : (forall i, i < n -> exists x, R i x)
                 -> exists s, forall i (Hi : i < n), R i (s i Hi).
  Proof.
    revert R; induction n as [ | n IHn ]; intros R HR.
    + assert (s : forall x, x < 0 -> X) by (intros; lia).
      exists s; intros; lia.
    + destruct (HR 0) as (x & Hx); try lia.
      destruct IHn with (R := fun i x => R (S i) x) as (s & Hs).
      { intros; apply HR; lia. }
      exists (fun i => match i with 0 => fun _ => x | S i => fun Hi => s i (lt_S_n i n Hi) end).
      intros [ | i ] Hi; simpl; auto.
  Qed.

End fin_reif.

Fact fin_reif_nat (R : nat -> nat -> Prop) n :
         (forall i, i < n -> ex (R i)) -> exists s, forall i, i < n -> R i (s i).
Proof.
  intros HR.
  apply fin_reif in HR.
  destruct HR as (s & Hs).
  exists (fun i => match le_lt_dec n i with left _ => 0 | right H => s _ H end).
  intros i Hi; destruct (le_lt_dec n i); auto; lia.
Qed.

Section bounded_search.

  Theorem bounded_search m (P : nat -> Type) :
        (forall n, n < m -> P n + (P n -> False))
     -> { n : nat & (n < m) * P n }%type + { forall n, n < m -> P n -> False }.
  Proof.
    revert P; induction m as [ | m IHm ]; intros P HP.
    + right; intros; lia.
    + destruct (HP 0) as [ H0 | H0 ]; try lia.
      * left; exists 0; split; auto; lia.
      * destruct IHm with (P := fun n => P (S n)) as [ (n & H1 & H2) | H1 ].
        - intros; apply HP; lia.
        - left; exists (S n); split; auto; lia.
        - right; intros [ | n ] Hn; auto.
          apply H1; lia.
  Qed.

  Lemma bounded_min (P : nat -> Prop) : 
        (forall x, P x \/ ~ P x) 
     -> forall n, (exists k, k < n /\ P k /\ forall i, i < k -> ~ P i) \/ forall k, k < n -> ~ P k.
  Proof.
    intros HP.
    induction n as [ | n IHn ].
    + right; intros; lia.
    + destruct IHn as [ (k & H1 & H2 & H3) | H ].
      * left; exists k; repeat split; auto; lia.
      * destruct (HP n).
        - left; exists n; repeat split; auto.
        - right; intros k Hk.
          destruct (eq_nat_dec k n); subst; auto. 
          apply H; lia.
  Qed.

  Lemma minimize (P : nat -> Prop) : (forall x, P x \/ ~ P x) -> (exists n, P n) -> exists n, P n /\ forall i, i < n -> ~ P i.
  Proof.
    intros HP (n & Hn).
    destruct (@bounded_min _ HP (S n)) as [ (k & H1 & H2 & H3) | H ].
    + exists k; split; auto.
    + exfalso; apply H with n; auto.
  Qed.
   
  Lemma first_non_zero (f : nat -> nat) n : f 0 = 0 -> f n <> 0 -> exists i, i < n /\ (forall k, k <= i -> f k = 0) /\ f (i+1) <> 0.
  Proof.
    intros H0 H1.
    destruct (@minimize (fun i => f i <> 0)) as (i & H2 & H3).
    + intro; destruct (eq_nat_dec (f x) 0); lia.
    + exists n; auto.
    + assert (i <> 0) as Hi by (intro; subst; destruct H2; auto).
      exists (i-1); split; [ | split ].
      * destruct (le_lt_dec i n) as [ | H4 ]; try lia.
        apply H3 in H4; destruct H4; auto.
      * intros k Hk; generalize (H3 k); intros; lia.
      * replace (i-1+1) with i by lia; auto.
  Qed.

End bounded_search.

Fact interval_dec a b i : { a <= i < b } + { i < a \/ b <= i }.
Proof.
  destruct (le_lt_dec b i).
  + right; lia.
  + destruct (le_lt_dec a i).
    * left; lia.
    * right; lia.
Qed.

(* Fact interval_dec a b n : { a <= n < b } + { ~ a <= n < b }.
Proof.
  destruct (le_lt_dec a n).
  2: right; lia.
  destruct (le_lt_dec b n).
  1: right; lia.
  left; lia.
Qed. *)


Definition lsum := fold_right plus 0.
Definition lmax := fold_right max 0.

Fact lmax_spec l x : lmax l <= x <-> Forall (fun y => y <= x) l.
Proof.
  revert x; induction l as [ | y l IHl ]; simpl.
  + split; auto; try lia.
  + intros x; rewrite Forall_cons_inv, <- IHl, Nat.max_lub_iff; tauto.
Qed.

Fact lsum_app l r : lsum (l++r) = lsum l+lsum r.
Proof.
  induction l as [ | x l IHl ]; simpl; auto; rewrite IHl; lia.
Qed.

Fact lsum_le x l : In x l -> x <= lsum l.
Proof.
  intros H; apply in_split in H.
  destruct H as (u & v & ->).
  rewrite lsum_app; simpl; lia.
Qed.

Fact lmax_prop l x : In x l -> x <= lmax l.
Proof.
  specialize (proj1 (lmax_spec l _) (le_refl _)).
  rewrite Forall_forall; auto.
Qed.

Section new.

  Definition nat_new l := S (lmax l).

  Fact nat_new_spec l : ~ In (nat_new l) l.
  Proof.
    assert (forall x, In x l -> x < nat_new l) as H.
      induction l as [ | x l IHl ].
      intros _ [].
      intros y [ [] | Hy ]; apply le_n_S;
        [ apply le_max_l | ].
      apply IHl, le_S_n in Hy.
      apply le_trans with (1 := Hy), le_max_r.
    intros C; apply H in C; lia.
  Qed.

End new.

Local Notation Zero := false.
Local Notation One  := true.

Fixpoint div2 n : nat * bool :=
  match n with
    | 0 => (0,Zero)
    | 1 => (0,One)
    | S (S n) => let (p,b) := div2 n in (S p,b)
  end.

Fact div2_spec n : match div2 n with 
                     | (p,One)  => n = 2*p+1 
                     | (p,Zero) => n = 2*p
                   end.
Proof.
  induction n as [ [ | [ | n ] ] IHn ] using (well_founded_induction lt_wf); simpl; auto.
  specialize (IHn n).
  destruct (div2 n) as (p,[]); simpl in * |- *; lia.
Qed.

Fixpoint div2_2p1 p : div2 (2*p+1) = (p,One).
Proof.
  destruct p as [ | p ].
  simpl; auto.
  replace (2*S p+1) with (S (S (2*p+1))) by lia.
  unfold div2; fold div2; rewrite div2_2p1; auto.
Qed.

Fixpoint div2_2p0 p : div2 (2*p) = (p,Zero).
Proof.
  destruct p as [ | p ].
  simpl; auto.
  replace (2*S p) with (S (S (2*p))) by lia.
  unfold div2; fold div2; rewrite div2_2p0; auto.
Qed.

Fixpoint pow2 p := 
  match p with 
    | 0   => 1
    | S p => 2*pow2 p
  end.

Fact pow2_fix0 : pow2 0 = 1.
Proof. reflexivity. Qed.

Fact pow2_fix1 p : pow2 (S p) = 2*pow2 p.
Proof. reflexivity. Qed.

Fact pow2_ge1 p : 1 <= pow2 p.
Proof. induction p; simpl; lia. Qed.

Fact pow2_2n1_dec n : { p : nat & { b | S n = pow2 p*(2*b+1) } }.
Proof.
  induction on n as IH with measure n.
  generalize (div2_spec (S n)).
  destruct (div2 (S n)) as (d,[]); intros Hn.
  + exists 0, d; simpl; lia.
  + destruct d as [ | d ].
    * simpl in Hn; lia.
    * destruct (IH d) as (p & b & H).
      - lia.
      - exists (S p), b; rewrite pow2_fix1, <- mult_assoc, <- H; auto.
Qed.

Fact pow2_dec_uniq p a q b : pow2 p*(2*a+1) = pow2 q*(2*b+1) -> p = q /\ a = b.
Proof.
  revert q; induction p as [ | p IHp ]; intros [ | q ].
  + simpl; lia.
  + rewrite pow2_fix0, pow2_fix1, <- mult_assoc; lia.
  + rewrite pow2_fix0, pow2_fix1, <- mult_assoc; lia.
  + rewrite !pow2_fix1, <- !mult_assoc; intros H.
    destruct (IHp q); lia.
Qed.

Fact pow2_dec_ge1 p b : 1 <= pow2 p*(2*b+1).
Proof.
  change 1 with (1*1) at 1; apply mult_le_compat; 
    try lia; apply pow2_ge1.
Qed.

Section pow2_bound.

  Let loop := fix loop x n :=
    match n with 
      | 0 => 0
      | S n => match div2 x with 
                 | (0,_) => 0
                 | (p,_) => S (loop p n)
               end
    end.

  Let loop_prop n : forall x, x < n -> x < pow2 (S (loop x n)).
  Proof.
    induction n as [ | n IHn ]; intros x Hx.
    { lia. }
    unfold loop; fold loop.
    generalize (div2_spec x).
    destruct (div2 x) as ([ | p ],[]); intros H.
    + simpl; lia.
    + simpl; lia.
    + specialize (IHn (S p)); spec in IHn.
      * lia.
      * simpl in IHn |- *; lia.
    + specialize (IHn (S p)); spec in IHn.
      * lia.
      * simpl in IHn |- *; lia.
  Qed.

  Definition find_pow2 x := S (loop (pred x) x).

  Fact find_pow2_geq x : 1 <= find_pow2 x.
  Proof. unfold find_pow2; lia. Qed.

  Fact find_pow2_prop x : x <= pow2 (find_pow2 x).
  Proof.
    unfold find_pow2; destruct x.
    + simpl; lia.
    + apply loop_prop; auto. 
  Qed.

End pow2_bound.

Section nat_sorted.
   
  Definition nat_sorted ll := forall l a m b r, ll = l ++ a :: m ++ b :: r -> a < b.
  
  Fact in_nat_sorted_0 : nat_sorted nil.
  Proof. intros [] ? ? ? ? ?; discriminate. Qed.
  
  Fact in_nat_sorted_1 x : nat_sorted (x::nil).
  Proof. intros [ | ? [] ] ? [] ? ? ?; discriminate. Qed.
  
  Fact in_nat_sorted_2 x y ll : x < y -> nat_sorted (y::ll) -> nat_sorted (x::y::ll).
  Proof.
    intros H1 H2 l a m b r H3.
    destruct l as [ | u l ].
    inversion H3; subst.
    destruct m as [ | v m ].
    inversion H4; subst; auto.
    inversion H4; subst.
    apply lt_trans with (1 := H1), (H2 nil _ m _ r); auto.
    inversion H3; subst.
    apply (H2 l _ m _ r); auto.
  Qed.
  
  Fact in_nat_sorted_3 x ll : Forall (lt x) ll -> nat_sorted ll -> nat_sorted (x::ll).
  Proof.
    induction 1 as [ | y ll Hll IHl ].
    intro; apply in_nat_sorted_1.
    intros H.
    apply in_nat_sorted_2; auto.
  Qed.
  
  Fact nat_sorted_cons_inv x ll : nat_sorted (x::ll) -> nat_sorted ll.
  Proof. intros H l a m b r ?; apply (H (x::l) _ m _ r); subst; solve list eq. Qed.
  
  Fact nat_sorted_Forall x ll : nat_sorted (x::ll) -> Forall (lt x) ll.
  Proof. 
    rewrite Forall_forall; intros H y Hy.
    apply in_split in Hy.
    destruct Hy as (l & r & ?); subst.
    apply (H nil _ l _ r); auto.
  Qed.
  
  Fact nat_sorted_head_inv x y ll : nat_sorted (x::y::ll) -> x < y.
  Proof. intros H; apply (H nil _ nil _ ll); solve list eq. Qed.

  Variable P : list nat -> Type.
  
  Hypothesis (HP0 : P nil).
  Hypothesis (HP1 : forall x, P (x::nil)).
  Hypothesis (HP2 : forall x y l, x < y -> P (y::l) -> P (x::y::l)).
  
  Theorem nat_sorted_rect l : nat_sorted l -> P l.
  Proof.
    induction l as [ [ | x [ | y l ] ] IHl ] using (measure_rect (@length _)).
    intro; apply HP0.
    intro; apply HP1.
    intros H; apply HP2. 
    revert H; apply nat_sorted_head_inv.
    apply IHl.
    rew length; lia.
    revert H; apply nat_sorted_cons_inv.
  Qed.
  
End nat_sorted.

Fact nat_sorted_injective ll : nat_sorted ll -> list_injective ll.
Proof.
  intros H l a m b r E; generalize (H _ _ _ _ _  E); lia.
Qed.

Fixpoint nat_list_insert x l :=
  match l with
    | nil  => x::nil
    | y::l => if x <? y then x::y::l else
              if y <? x then y::nat_list_insert x l else y::l
  end.

Fact nat_list_insert_length x l : length (nat_list_insert x l) <= S (length l).
Proof.
  induction l as [ | y l IHl ]; simpl.
  lia.
  destruct (x <? y); simpl; try lia.
  destruct (y <? x); simpl; lia.
Qed.
  
Fact nat_list_insert_incl x l : incl (nat_list_insert x l) (x::l)
                             /\ incl (x::l) (nat_list_insert x l).
Proof.
  split. 
  
  induction l as [ | y l IHl ]; simpl.
  intro; auto.
  destruct (x <? y); destruct (y <? x).
  intro; auto.
  intro; auto.
  intros ? [ [] | H ]; simpl; auto.
  apply IHl in H; simpl in H; tauto.
  intro; simpl; tauto.

  induction l as [ | y l IHl ]; simpl.
  intro; auto.
  generalize (Nat.ltb_lt x y) (Nat.ltb_lt y x).
  destruct (x <? y); destruct (y <? x); intros H1 H2 z; auto.
  intros [ Hz | [ Hz | Hz ] ]; subst.
  right; apply IHl; left; auto.
  left; auto.
  right; apply IHl; right; auto.
  destruct (lt_eq_lt_dec x y) as [ [ H | ] | H ].
  apply H1 in H; discriminate.
  2: apply H2 in H; discriminate.
  intros [ Hz | [ Hz | Hz ] ]; subst; auto.
  left; auto.
  left; auto.
  right; auto.
Qed.
  
Fact nat_list_insert_Forall (P : nat -> Prop) x l : 
      P x -> Forall P l -> Forall P (nat_list_insert x l).
Proof.
  do 2 rewrite Forall_forall; intros H1 H2 y Hy.
  apply nat_list_insert_incl in Hy.
  destruct Hy; subst; auto.
Qed.
  
Fact nat_list_insert_sorted x l : nat_sorted l -> nat_sorted (nat_list_insert x l).
Proof.
  induction l as [ | y l IHl ]; simpl.
  intro; apply in_nat_sorted_1.
  intros H.
  generalize (Nat.ltb_lt x y) (Nat.ltb_lt y x).
  destruct (x <? y); destruct (y <? x); intros H1 H2.
  apply proj1 in H1; spec in H1; auto.
  apply proj1 in H2; spec in H2; auto.
  lia.
  apply in_nat_sorted_2; auto; tauto.
  apply in_nat_sorted_3.
  apply nat_list_insert_Forall.
  tauto.
  apply nat_sorted_Forall; auto.
  apply IHl; revert H; apply nat_sorted_cons_inv.
  auto.
Qed.

Definition nat_sort := fold_right (nat_list_insert) nil.

Fact nat_sort_length l : length (nat_sort l) <= length l.
Proof.
  induction l as [ | x l IHl ]; simpl.
  lia.
  apply le_trans with (1 := nat_list_insert_length _ _); lia.
Qed.

Fact nat_sort_eq l : incl (nat_sort l) l /\ incl l (nat_sort l).
Proof.
  induction l as [ | x l IHl ]; simpl; split; intros y Hy; auto.
  apply nat_list_insert_incl in Hy; simpl.
  destruct Hy as [ | Hy ]; auto; right; apply IHl; auto.
  apply nat_list_insert_incl.
  destruct Hy; [ left | right ]; auto.
  apply IHl; auto.
Qed.

Fact nat_sort_sorted l : nat_sorted (nat_sort l).
Proof.
  induction l as [ | x l IHl ].
  apply in_nat_sorted_0.
  simpl; apply nat_list_insert_sorted; auto.
Qed.

Fact nat_sinc (f : nat -> nat) a b : 
      (forall x, a <= x < b -> f x < f (S x)) 
   -> (forall x y, a <= x < y /\ y <= b -> f x < f y).
Proof.
  intros H1.
  assert (forall n m, n <= m <= b - a -> f (a+n) <= f (a+m)) as H2.
    intros n m (H2 & H3); revert H2 H3.
    induction 1 as [ | m Hm IH ]; auto.
    intros H. spec in IH. lia.
    apply le_trans with (1 := IH).
    replace (a+S m) with (S (a+m)) by lia.
    apply lt_le_weak, H1; lia.
  assert (forall n m, n < m <= b - a -> f (a+n) < f (a+m)) as H3.
    unfold lt at 1; intros n m H.
    specialize (H1 (a+n)).
    spec in H1.
    lia.
    apply lt_le_trans with (1 := H1).
    replace (S (a+n)) with (a+S n) by lia.
    apply H2; auto.
  intros x y H4.
  replace x with (a+(x-a)) by lia.
  replace y with (a+(y-a)) by lia.
  apply H3.
  lia.
Qed.

Fact nat_sinc_inj f a b : 
      (forall x y,  a <= x < y /\ y <= b -> f x < f y) 
   -> (forall x y,  a <= x <= b -> a <= y <= b -> f x = f y -> x = y).
Proof.
  intros H0 x y Hx Hy.
  destruct Hx; destruct Hy.
  destruct (lt_eq_lt_dec x y) as [ [ ? | ? ] | ? ]; auto.
  specialize (H0 x y).
  spec in H0; repeat split; auto; intro; lia.
  specialize (H0 y x).
  spec in H0; repeat split; auto; intro; lia.
Qed.

Theorem nat_rev_ind (P : nat -> Prop) (HP : forall n, P (S n) -> P n) x y : x <= y -> P y -> P x.
Proof. induction 1; auto. Qed.

Section nat_rev_bounded_ind.

  Variables (k : nat) (P : nat -> Prop) (HP : forall n, S n <= k -> P (S n) -> P n).
  
  Fact nat_rev_bounded_ind x y : x <= y <= k -> P y -> P x.
  Proof.
    intros H1 H2.
    refine (proj1 (@nat_rev_ind (fun n => P n /\ n <= k) _ x y _ _)).
    clear x y H1 H2; intros n (H1 & H2); split; auto; lia.
    lia.
    split; auto; lia.
  Qed.

End nat_rev_bounded_ind.

Section nat_minimize.

  Variable P : nat -> Prop.
  Hypothesis HP : forall n, { P n } + { ~ P n }.

  Inductive bar_min (n : nat) : Prop :=
    | in_bar_min_0 : P n -> bar_min n
    | in_bar_min_1 : bar_min (S n) -> bar_min n.

  Section nat_min.

    Let min_rec : forall n, bar_min n -> { m | P m /\ forall x, P x -> x < n \/ m <= x }.
    Proof.
      refine (fix loop n Hn := match HP n with
        | left H  => exist _ n _
        | right H => match loop (S n) _ with
          | exist _ m Hm => exist _ m _
        end
      end).
      * split; auto; intros; lia.
      * destruct Hn; auto; destruct H; auto.
      * destruct Hm as [ H1 H2 ]; split; auto.
        intros x Hx; specialize (H2 x Hx).
        destruct (eq_nat_dec x n).
        - subst; tauto.
        - lia.
    Qed.

    Definition min_dec : (exists n, P n) -> { m | P m /\ forall x, P x -> m <= x }.
    Proof.
      intros H.
      destruct (@min_rec 0) as (m & H1 & H2).
      * destruct H as (n & Hn).
        apply in_bar_min_0 in Hn.
        revert Hn; apply nat_rev_ind.
        apply in_bar_min_1.
        lia.
      * exists m; split; auto.
        intros x Hx; specialize (H2 _ Hx); lia.
    Defined.

  End nat_min.

  Fact first_which : (exists x, P x) -> { m | P m /\ forall x, x < m -> ~ P x }.
  Proof.
    intros H.
    destruct (min_dec H) as (m & H1 & H2).
    exists m; split; auto.
    intros x Hx H3.
    apply H2 in H3.
    lia.
  Qed.

End nat_minimize.

Section first_which_ni.

  Variable P : nat -> Prop.

  Fact bounded_search_ni n : (forall i, i < n -> P i \/ ~ P i) -> (forall i, i < n -> ~ P i) \/ exists i, i < n /\ P i /\ forall j, j < i -> ~ P j.
  Proof.
    revert P; induction n as [ | n IHn ]; intros P HP.
    + left; intros; lia.
    + destruct (HP 0) as [ H | H ]; try lia.
      - right; exists 0; split; try lia; split; auto; intros; lia.
      - destruct IHn with (P := fun n => P (S n)) as [ H1 | (x & H1 & H2 & H3) ].
        * intros; apply HP; lia.
        * left; intros [] ?; auto; apply H1; lia.
        * right; exists (S x); split; try lia; split; auto.
          intros [] ?; auto; apply H3; lia.
  Qed.
  
  Hypothesis HP : forall n, P n \/ ~ P n.

  Fact first_which_ni : (exists x, P x) -> exists m, P m /\ forall x, x < m -> ~ P x.
  Proof.
    intros (n & Hn).
    destruct (@bounded_search_ni (S n)) as [ H1 | (m & H1 & H2 & H3) ].
    + intros; auto.
    + contradict Hn; apply H1; lia.
    + exists m; auto.
  Qed.

End first_which_ni.
