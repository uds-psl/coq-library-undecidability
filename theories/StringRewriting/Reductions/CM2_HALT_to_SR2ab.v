Require Import List Relation_Operators Operators_Properties Lia.
Import ListNotations.

Require Import Undecidability.StringRewriting.SR01.
Require Import Undecidability.CounterMachines.CM2.

Require Import ssreflect ssrbool ssrfun.

Set Default Proof Using "Type".

Arguments rt_trans {A R x y z}.

Module Facts.
(* induction principle wrt. a decreasing measure f *)
(* example: elim /(measure_ind length) : l. *)
Lemma measure_ind {X : Type} (f : X -> nat) (P : X -> Prop) : 
  (forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
  apply : well_founded_ind.
  apply : Wf_nat.well_founded_lt_compat. move => *. by eassumption.
Qed.
Arguments measure_ind {X}.

(* duplicates argument *)
Lemma copy {A : Prop} : A -> A * A.
Proof. done. Qed.

(* transforms a goal (A -> B) -> C into goals A and B -> C *)
Lemma unnest : forall (A B C : Type), A -> (B -> C) -> (A -> B) -> C.
Proof. auto. Qed.

Lemma iter_plus {X: Type} {f: X -> X} {x: X} {n m: nat} : 
  Nat.iter (n + m) f x = Nat.iter n f (Nat.iter m f x).
Proof. by rewrite /Nat.iter nat_rect_plus. Qed.

Section ForallNorm.
Context {X : Type} {P : X -> Prop}.

Lemma ForallE {l} : Forall P l -> if l is x :: l then P x /\ Forall P l else True.
Proof. by case. Qed.

Lemma Forall_nilI : Forall P [].
Proof. by constructor. Qed.

Lemma Forall_consI {x l} : P x -> Forall P l -> Forall P (x :: l).
Proof. by constructor. Qed.

Lemma Forall_nilP : Forall P [] <-> True.
Proof. by constructor. Qed.

Lemma Forall_consP {x l} : Forall P (x :: l) <-> P x /\ Forall P l.
Proof. by constructor=> [/ForallE | [/Forall_consI H] /H]. Qed.

Lemma Forall_singletonP {x} : Forall P [x] <-> P x.
Proof. rewrite Forall_consP Forall_nilP. by constructor=> [[? ?] | ?]. Qed.

Lemma Forall_appP {l1 l2}: Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
Proof.
  elim: l1; first by (constructor; by [|case]).
  move=> ? ? IH /=. by rewrite ?Forall_consP IH and_assoc.
Qed.

Lemma Forall_repeatP {x n} : Forall P (repeat x n) <-> (n = 0 \/ P x).
Proof.
  elim: n; first by (constructor => *; [by left | by constructor]).
  move=> n IH /=. rewrite Forall_consP IH.
  constructor; first by (move=> [? _]; right).
  case; [done | constructor; [done | by right]].
Qed. 

Definition Forall_norm := (@Forall_appP, @Forall_singletonP, @Forall_consP, @Forall_nilP).
End ForallNorm.

Lemma repeat_appP {X: Type} {x: X} {n m: nat} : 
  repeat x n ++ repeat x m = repeat x (n+m).
Proof. by elim: n; [| move=> ? /= ->]. Qed.

Lemma In_appl {X : Type} {x: X} {l1 l2: list X} : In x l1 -> In x (l1 ++ l2).
Proof. move=> ?. apply: in_or_app. by left. Qed.

Lemma In_appr {X : Type} {x: X} {l1 l2: list X} : In x l2 -> In x (l1 ++ l2).
Proof. move=> ?. apply: in_or_app. by right. Qed.

Arguments nth_error_In {A l n x}.

Lemma nth_error_Some_in_combine {X: Type} {l: list X} {i x}:
  nth_error l i = Some x -> 
  In (i, x) (combine (seq 0 (length l)) l).
Proof.
  move Hk: (0) => k Hi. have ->: (i = i + k) by lia.
  elim: l i k {Hk} Hi; first by case.
  move=> y l IH [|i] k.
  - move=> /= [<-]. by left.
  - move=> /IH {}IH /=. right. by have ->: (S (i + k) = i + S k) by lia.
Qed.
End Facts.

Import Facts.

Module SR_facts.
Import StringRewriting.SR01.
Lemma stepI {srs u v a b c d s t} : 
  s = (u ++ a :: b :: v) -> t = (u ++ c :: d :: v) -> In ((a, b), (c, d)) srs ->
  step srs s t.
Proof. move=> -> ->. by constructor. Qed.

Lemma reachable_appI {srs u v s t} : reachable srs s t -> reachable srs (u ++ s ++ v) (u ++ t ++ v).
Proof.
  elim; [| move=> *; by apply: rt_refl | move=> *; apply: rt_trans; by eassumption ].
  move=> {}s {}t [] u' v' > ?. 
  apply /rt_step /(stepI (u := u ++ u') (v := v' ++ v)); last by eassumption.
  all: by rewrite -?app_assoc.
Qed.

Lemma reachable_applI {srs u s t} : reachable srs s t -> reachable srs (u ++ s) (u ++ t).
Proof. move=> /reachable_appI => /(_ u []). by rewrite ?app_nil_r. Qed.

Lemma reachable_apprI {srs v s t} : reachable srs s t -> reachable srs (s ++ v) (t ++ v).
Proof. by move=> /reachable_appI => /(_ [] v). Qed.
End SR_facts.

Module CM_facts.
Lemma haltingP {cm c} : halting cm c <-> length cm <= state c.
Proof.
  move:c => [p a b]. rewrite /halting /=.
  move Hoi: (nth_error cm p) => oi.
  case: oi Hoi; last by move=> /nth_error_None.
  move=> [] x => [|?] Hp /=.
  - constructor; [by case; lia | by rewrite -nth_error_None Hp].
  - move: x a b Hp => [] [|?] [|?]; 
      (constructor; [by case; lia | by rewrite -nth_error_None Hp]).
Qed.

Lemma halting_eq {cm c n} : halting cm c -> Nat.iter n (step cm) c = c.
Proof.
  move=> Hc. elim: n; first done.
  move=> ? /= ->. by rewrite Hc.
Qed. 

Lemma values_ub cm c n : 
  value1 (Nat.iter n (CM2.step cm) c) + value2 (Nat.iter n (CM2.step cm) c) <= n + value1 c + value2 c.
Proof.
  move Hk : (n + value1 c + value2 c) => k.
  have : n + value1 c + value2 c <= k by lia.
  elim: n k c {Hk}; first done.
  move=> n IH k [p a b]. have ->: S n = n + 1 by lia.
  rewrite iter_plus /=. 
  case: (nth_error cm p).
  - move=> [] [] => [||?|?]; move: a b => [|?] [|?] /= ?; apply: IH => /=; by lia.
  - move=> ?. apply: IH => /=. by lia.
Qed.

End CM_facts.

Module Argument.
Import Facts SR_facts CM_facts.
Section Reduction.
(* given two-counter machine *)
Context (cm : Cm2).

Local Notation sb := ((0, @None nat)). (* blank *)
Local Notation sl := ((1, @None nat)). (* left marker *)
Local Notation sr := ((2, @None nat)). (* right marker *)
Local Notation sm := ((3, @None nat)). (* middle marker *)

Local Notation sz := ((4, @None nat)). (* 0 *)
Local Notation so := ((5, @Some nat 0)). (* 1 *)
Local Notation st := ((6, @None nat)). (* temporary marker *)

Local Notation sb' p := ((0, @Some nat p)). (* blank *)
Local Notation sl' p := ((1, @Some nat p)). (* left marker *)
Local Notation sr' p := ((2, @Some nat p)). (* right marker *)
Local Notation sm' p := ((3, @Some nat p)). (* middle marker *)

Definition states := map (fun i => if i is dec _ q then q else 0) cm.
Definition sum : list nat -> nat := fold_right Nat.add 0. 

Definition state_bound := 1 + length cm + sum states.

Lemma state_boundP {p i} : nth_error cm p = Some i -> 
  (if i is dec _ q then q else 0) + 1 + p < state_bound.
Proof.
  rewrite /state_bound /states.
  elim: (cm) p; first by case.
  move=> ? l IH [|p] /= => [[->] | /IH]; last by lia.
  by case: (i); lia.
Qed.

(* encode instruction i at position n *)
Definition enc_Instruction (ni: (nat * Instruction)) : Srs :=
  match ni with
  | (p, inc b) => if b then [((sr' p, sz), (sb, sr' (S p)))] else [((sz, sl' p), (sl' (S p), sb))]
  | (p, dec b q) => 
      if b then [((sm, sr' p), (sm, sr' (S p))); ((sb, sr' p), (sr' q, sz))] 
      else [((sl' p, sm), (sl' (S p), sm)); ((sl' p, sb), (sz, sl' q))]
  end.

(* constructed string rewriting system *)
Definition srs : Srs := 
  (* initialization *)
  [ ((sz, sz), (st, sr)); (* 00 -> tr *)
    ((sz, st), (sl' 0, sm)) (* 0t -> l_0 m *) ] ++
  (* simulation *)
  flat_map enc_Instruction (combine (seq 0 (length cm)) cm) ++
  (* state movement to the right *)
  flat_map (fun p => [
    ((sl' p, sb), (sl, sb' p)); ((sl' p, sm), (sl, sm' p)); 
    ((sb' p, sb), (sb, sb' p)); ((sb' p, sm), (sb, sm' p)); ((sb' p, sr), (sb, sr' p));
    ((sm' p, sb), (sm, sb' p)); ((sm' p, sr), (sm, sr' p))]) (seq 0 state_bound) ++
  (* state movement to the left *)
  flat_map (fun p => [
    ((sb, sr' p), (sb' p, sr)); ((sm, sr' p), (sm' p, sr)); 
    ((sb, sb' p), (sb' p, sb)); ((sm, sb' p), (sm' p, sb)); ((sl, sb' p), (sl' p, sb));
    ((sb, sm' p), (sb' p, sm)); ((sl, sm' p), (sl' p, sm))]) (seq 0 state_bound) ++
  (* finalization *)
  map (fun p => ((sz, sl' p), (so, so))) (seq (length cm) (state_bound - length cm)) ++
  [((sz, so), (so, so)); ((so, sb), (so, so)); ((so, sm), (so, so)); ((so, sr), (so, so)); ((so, sz), (so, so))]
  .

Lemma move_sb_right {p n} : p < state_bound -> reachable srs ((sb' p) :: repeat sb n) ((repeat sb n) ++ [sb' p]).
Proof.
  move=> Hp. elim: n; first by apply: rt_refl.
  move=> n IH /=. apply: rt_trans; 
    [apply: rt_step | apply: (reachable_applI (u := [sb])); exact: IH].
  apply: (stepI (u := []) (v := repeat sb n)); [by reflexivity | by reflexivity |].
  rewrite /srs. apply /In_appr /In_appr /In_appl /in_flat_map.
  exists p. constructor; [apply /in_seq; by lia | move=> /=; by tauto].
Qed.

Lemma move_sb_left {p n} : p < state_bound -> reachable srs ((repeat sb n) ++ [sb' p]) ((sb' p) :: repeat sb n).
Proof.
  move=> Hp. elim: n; first by apply: rt_refl.
  move=> n IH /=. apply: rt_trans; 
    [apply: (reachable_applI (u := [sb])); exact: IH | apply: rt_step].
  apply: (stepI (u := []) (v := repeat sb n)); [by reflexivity | by reflexivity |].
  rewrite /srs. apply /In_appr /In_appr /In_appr /In_appl /in_flat_map.
  exists p. constructor; [apply /in_seq; by lia | move=> /=; by tauto].
Qed.

Section Transport.
(* number of steps until halting *)
Context (n_cm: nat).
Definition c0 := {| state := 0; value1 := 0; value2 := 0 |}.
Context (H_n_cm: halting cm (Nat.iter n_cm (CM2.step cm) c0)).

Lemma cm_value1_ub n : value1 (Nat.iter n (CM2.step cm) c0) <= n_cm.
Proof using H_n_cm.
  have [|->] : n <= n_cm \/ n = ((n - n_cm) + n_cm) by lia.
  - move=> ?. have := values_ub cm c0 n.
    rewrite /c0 /=. by lia.
  - rewrite iter_plus halting_eq; first done.
    have := values_ub cm c0 n_cm.
    rewrite /c0 /=. by lia.
Qed.

Lemma cm_value2_ub n : value2 (Nat.iter n (CM2.step cm) c0) <= n_cm.
Proof using H_n_cm.
  have [|->] : n <= n_cm \/ n = ((n - n_cm) + n_cm) by lia.
  - move=> ?. have := values_ub cm c0 n.
    rewrite /c0 /=. by lia.
  - rewrite iter_plus halting_eq; first done.
    have := values_ub cm c0 n_cm.
    rewrite /c0 /=. by lia.
Qed.

Lemma cm_state_ub n : state (Nat.iter n (CM2.step cm) c0) < state_bound.
Proof.
  elim: n; first by (rewrite /= /state_bound; lia).
  move=> n /=. move: (Nat.iter _ _ c0) => [p a b] /=.
  move Hoi: (nth_error cm p) => oi. case: oi Hoi; last done.
  case.
  - by move=> > /state_boundP.
  - move: a b => [|?] [|?] [] > /state_boundP /=; by lia.
Qed.

Definition d := 5 + n_cm + n_cm. (* maximal space requirement *)

(* s is (0^(n-a) l_p _^a m _^b r 0^(n-b)) with a unique state annotation *)
Definition enc_Config : Config -> list Symbol :=
  fun '{| state := p; value1 := a; value2 := b |} => 
    (repeat sz (1 + n_cm-a)) ++ [sl' p] ++ (repeat sb a) ++ [sm] ++ 
    (repeat sb b) ++ [sr] ++ (repeat sz (1 + n_cm-b)).

(* s is (0^(n-a) l _^a m _^b r_p 0^(n-b)) with a unique state annotation *)
Definition enc_Config' : Config -> list Symbol :=
  fun '{| state := p; value1 := a; value2 := b |} => 
    (repeat sz (1 + n_cm-a)) ++ [sl] ++ (repeat sb a) ++ [sm] ++ 
    (repeat sb b) ++ [sr' p] ++ (repeat sz (1 + n_cm-b)).

Arguments List.app : simpl never.

Lemma reachable_enc_c0 : reachable srs (repeat sz d) (enc_Config c0).
Proof using.
  apply: (rt_trans (y := (repeat sz (1 + n_cm)) ++ [sz] ++ [st] ++ [sr] ++ (repeat sz (1 + n_cm)))).
  - have ->: d = 1 + n_cm + 1 + 1 + 1 + 1 + n_cm by (rewrite /d; lia).
    rewrite -?repeat_appP -?app_assoc. do ? apply: reachable_applI.
    apply /rt_step /(stepI (u := [])); [done | done |].
    apply /In_appl. rewrite /=. by tauto.
  - apply /rt_step /(stepI (u := repeat sz (1 + n_cm))); [done | done |].
    apply /In_appl. rewrite /=. by tauto.
Qed.

Lemma move_sb_right' {p n x y} : p < state_bound -> ((x, y) = (1, 3) \/ (x, y) = (3, 2)) ->
  reachable srs ([(x, Some p)] ++ repeat sb n ++ [(y, None)]) ([(x, None)] ++ repeat sb n ++ [(y, Some p)]).
Proof.
  move=> ? /= Hxy. case: n.
  - apply: rt_step. apply: (stepI (u := []) (v := [])); [done | done |].
    rewrite /srs. apply /In_appr /In_appr /In_appl /in_flat_map. exists p.
    constructor; [apply /in_seq; by lia | move: Hxy => /= [] [-> ->]; by tauto].
  - move=> n. apply: (rt_trans (y := [(x, None)] ++ [sb' p] ++ (repeat sb n) ++ [(y, None)])).
    + rewrite /= -/([sb] ++ _) ?app_assoc. do 2 apply: reachable_apprI. 
      apply /rt_step /(stepI (u := []) (v := [])); [by reflexivity| by reflexivity | ].
      apply /In_appr /In_appr /In_appl /in_flat_map. exists p.
      constructor; [apply /in_seq; by lia | move: Hxy => /= [] [-> _]; by tauto].
    + rewrite -?app_assoc. apply: reachable_applI. 
      apply: (rt_trans (y := (repeat sb n) ++ [sb' p] ++ [(y, None)])).
      * rewrite ?app_assoc. apply: reachable_apprI. by apply: move_sb_right.
      * apply: rt_step. 
        apply: (stepI (u := repeat sb n) (v := [])); [by reflexivity | |].
        ** by rewrite (ltac:(lia) : S n = n + 1) -repeat_appP -?app_assoc.
        ** apply /In_appr /In_appr /In_appl /in_flat_map. exists p.
          constructor; [apply /in_seq; by lia | move: Hxy => /= [] [_ ->]; by tauto].
Qed.

Lemma move_sb_left' {p n x y} : p < state_bound -> ((x, y) = (1, 3) \/ (x, y) = (3, 2)) ->
  reachable srs ([(x, None)] ++ repeat sb n ++ [(y, Some p)]) ([(x, Some p)] ++ repeat sb n ++ [(y, None)]).
Proof.
  move=> ? /= Hxy. case: n.
  - apply: rt_step. apply: (stepI (u := []) (v := [])); [done | done |].
    rewrite /srs. apply /In_appr /In_appr /In_appr /In_appl /in_flat_map. exists p.
    constructor; [apply /in_seq; by lia | move: Hxy => /= [] [-> ->]; by tauto].
  - move=> n. apply: (rt_trans (y := [(x, None)] ++ (repeat sb n) ++ [sb' p] ++ [(y, None)])).
    + rewrite (ltac:(lia) : S n = n + 1) -repeat_appP -?app_assoc. do ? apply: reachable_applI. 
      apply /rt_step /(stepI (u := []) (v := [])); [by reflexivity| by reflexivity | ].
      apply /In_appr /In_appr /In_appr /In_appl /in_flat_map. exists p.
      constructor; [apply /in_seq; by lia | move: Hxy => /= [] [_ ->]; by tauto].
    + rewrite ?app_assoc. apply: reachable_apprI.
      apply: (rt_trans (y := [(x, None)] ++ [sb' p] ++ (repeat sb n))).
      * rewrite -?app_assoc. apply: reachable_applI. by apply: move_sb_left.
      * apply: rt_step. 
        apply: (stepI (u := [])); [by reflexivity | by reflexivity |].
        apply /In_appr /In_appr /In_appr /In_appl /in_flat_map. exists p.
        constructor; [apply /in_seq; by lia | move: Hxy => /= [] [-> _]; by tauto].
Qed.

Lemma move_right n : let c := (Nat.iter n (CM2.step cm) c0) in 
  reachable srs (enc_Config c) (enc_Config' c). 
Proof.
  move=> c. subst c.
  move Hc: (Nat.iter n _ c0) => c.
  case: c Hc => p a b Hc /=.
  apply: (reachable_applI (u := repeat sz _)).
  rewrite ?app_assoc. apply: reachable_apprI.
  have := cm_state_ub n. rewrite Hc /= => ?.
  apply: (rt_trans (y := [sl] ++ (repeat sb a) ++ [sm' p] ++ (repeat sb b) ++ [sr])).
  - rewrite ?app_assoc. do 2 apply: reachable_apprI.
    apply: move_sb_right'; by tauto.
  - rewrite -?app_assoc. do 2 apply: reachable_applI.
    apply: move_sb_right'; by tauto.
Qed.

Lemma move_left n : let c := (Nat.iter n (CM2.step cm) c0) in 
  reachable srs (enc_Config' c) (enc_Config c). 
Proof.
  move=> c. subst c.
  move Hc: (Nat.iter n _ c0) => c.
  case: c Hc => p a b Hc /=.
  apply: (reachable_applI (u := repeat sz _)).
  rewrite ?app_assoc. apply: reachable_apprI.
  have := cm_state_ub n. rewrite Hc /= => ?.
  apply: (rt_trans (y := [sl] ++ (repeat sb a) ++ [sm' p] ++ (repeat sb b) ++ [sr])).
  - rewrite -?app_assoc. do 2 apply: reachable_applI.
    apply: move_sb_left'; by tauto.
  - rewrite ?app_assoc. do 2 apply: reachable_apprI.
    apply: move_sb_left'; by tauto.
Qed.

Arguments Nat.sub : simpl never.
Arguments repeat : simpl never.

Lemma simulate_cm_step {n} : let c := (Nat.iter n (CM2.step cm) c0) in
  reachable srs (enc_Config c) (enc_Config (CM2.step cm c)).
Proof using H_n_cm.
  move=> c. subst c.
  have := cm_value2_ub n. have := cm_value1_ub n.
  have := move_right n. have := move_left (1+n). move=> /=.
  case: (Nat.iter n _ _) => p a b /=.
  move Hoi: (nth_error cm p) => oi.
  case: oi Hoi; last by (move=> *; apply: rt_refl). case; case.
  (* inc b *)
  - move=> /nth_error_Some_in_combine Hp /= Hr Hl ? ?.
    apply: rt_trans; first by eassumption.
    apply: rt_trans; last by eassumption.
    rewrite -/(repeat sb (S b)) (ltac:(lia) : S b = b + 1) -repeat_appP -?app_assoc.
    do 5 apply: reachable_applI. rewrite ?app_assoc.
    rewrite (ltac:(lia) : (S n_cm - b) = 1 + ((S n_cm - (b + 1)))) -repeat_appP ?app_assoc.
    apply: reachable_apprI.
    apply /rt_step /(stepI (u := []) (v := [])); [done | done |].
    apply /In_appr /In_appl /in_flat_map.
    eexists. constructor; [by eassumption | by left].
  (* inc a *)
  - move=> /nth_error_Some_in_combine Hp _ _ ? ?. apply: rt_step.
    apply: (stepI (u := repeat sz (n_cm-a)) (a := sz) (b := sl' p) (c := sl' (S p)) (d := sb)).
    + by rewrite (ltac:(lia) : S n_cm - a = (n_cm - a) + 1) -repeat_appP /= -app_assoc /=.
    + done.
    + rewrite /srs. apply /In_appr /In_appl /in_flat_map.
      eexists. constructor; [by eassumption | by left].
  (* dec b q *)
  - move=> q /nth_error_Some_in_combine Hp /= Hr Hl _ Hb.
    apply: rt_trans; first by eassumption.
    apply: rt_trans; last by eassumption.
    case: (b) Hb => [_ | b' Hb'] /=.
    + do 3 apply: reachable_applI. apply: rt_step. 
      apply: (stepI (u := [])); [done | done |].
      rewrite /srs. apply /In_appr /In_appl /in_flat_map.
      eexists. constructor; [by eassumption | by left].
    + rewrite -/(repeat sb (S b')) (ltac:(lia) : S b' = b' + 1) (ltac:(lia) : S n_cm - b' = 1 + (S n_cm - (b' + 1))).
      rewrite -?repeat_appP -?app_assoc.
      do 5 apply: reachable_applI. apply: rt_step. 
      apply: (stepI (u := [])); [done | done |].
      rewrite /srs. apply /In_appr /In_appl /in_flat_map.
      eexists. constructor; [by eassumption | right; by left].
  (* dec a q*)
  - move=> q /nth_error_Some_in_combine Hp _ _ Ha _. apply: rt_step.
    case: (a) Ha => [_ | a' Ha'] /=.
    + apply: (stepI (u := repeat sz (1+n_cm))); [done | done |].
      rewrite /srs. apply /In_appr /In_appl /in_flat_map.
      eexists. constructor; [by eassumption | by left].
    + rewrite (ltac:(lia) : (S n_cm - a' = (n_cm - a') + 1)) -repeat_appP -?app_assoc.
      apply: (stepI (u := repeat sz (n_cm - a'))); [done | done |].
      rewrite /srs. apply /In_appr /In_appl /in_flat_map.
      eexists. constructor; [by eassumption | right; by left].
Qed.

Lemma reachable_repeat_solI n : reachable srs (repeat sz n ++ [so]) (repeat so (n+1)).
Proof.
  elim: n; first by apply: rt_refl.
  move=> n IH. rewrite -repeat_appP. 
  have ->: S n = n + 1 by lia.
  apply: (rt_trans (y := repeat sz n ++ [so] ++ [so]));
    last by (rewrite ?app_assoc; apply: reachable_apprI).
  rewrite -repeat_appP -?app_assoc. apply: reachable_applI.
  apply /rt_step /(stepI (u := [])); [done| done |].
  do 5 apply /In_appr. rewrite /=. by tauto.
Qed.

Lemma reachable_repeat_sorI {n x} : x = sb \/ x = sz -> 
  reachable srs ([so] ++ repeat x n) ([so] ++ repeat so n).
Proof.
  move=> Hx. elim: n; first by apply: rt_refl.
  move=> n IH. 
  apply: (rt_trans (y := ([so] ++ [so] ++ repeat x n))); last by apply: reachable_applI.
  apply: rt_step. apply: (stepI (u := [])); [done | done |].
  do 5 apply /In_appr. by move: Hx => /= [->|->]; tauto.
Qed.

Lemma reachable_repeat_sorI' {s t n x} : x = sb \/ x = sz -> 
  reachable srs ([so] ++ s) ([so] ++ t) ->
  reachable srs ([so] ++ repeat x n ++ s) ([so] ++ repeat so n ++ t).
Proof.
  move=> /reachable_repeat_sorI H1 H2.
  apply: (rt_trans (y := ([so] ++ repeat so n ++ s))).
  - rewrite ?app_assoc. by apply: reachable_apprI.
  - have ->: [so] = repeat so 1 by done. rewrite ?app_assoc repeat_appP.
    have ->: 1 + n = n + 1 by lia. rewrite -repeat_appP -?app_assoc.
    by apply: reachable_applI.
Qed.

Lemma simulate_cm_halting {n} : let c := (Nat.iter n (CM2.step cm) c0) in
  halting cm c -> reachable srs (enc_Config c) (repeat so d).
Proof using H_n_cm.
  move=> c /haltingP. subst c.
  have := cm_value1_ub n. have := cm_value2_ub n. have := cm_state_ub n.
  move: (Nat.iter _ _ c0) => [p a b] /= *.
  apply: (rt_trans (y := (repeat sz (n_cm - a)) ++ [so] ++ [so] ++ _)).
  - apply: rt_step. rewrite (ltac:(lia) : S n_cm - a = (n_cm - a) + 1) -repeat_appP -?app_assoc.
    apply: (stepI (u := repeat sz (n_cm - a))); [done | done |].
    rewrite /srs. apply /In_appr /In_appr /In_appr /In_appr /In_appl.
    apply /in_map_iff. exists p. constructor; first done.
    apply /in_seq. by lia.
  - apply: (rt_trans (y := (repeat so (n_cm - a + 1) ++ [so] ++
      repeat sb a ++ [sm] ++ repeat sb b ++ [sr] ++ repeat sz (S n_cm - b)))).
    + rewrite ?app_assoc. do 6 apply: reachable_apprI. by apply: reachable_repeat_solI.
    + have ->: d = (n_cm - a + 1) + 1 + a + 1 + b + 1 + (S n_cm - b) by (rewrite /d; lia).
      rewrite -?repeat_appP -?app_assoc. do 2 apply: reachable_applI.
      apply: reachable_repeat_sorI'; first by left.
      apply: (rt_trans (y := ([so] ++ [so] ++ repeat sb b ++ [sr] ++ repeat sz (S n_cm - b)))).
      * apply: rt_step. apply: (stepI (u := [])); [done | done|].
        do 5 apply /In_appr. rewrite /=. by tauto.
      * apply: reachable_applI. apply: reachable_repeat_sorI'; first by left.
        apply: (rt_trans (y := ([so] ++ [so] ++ repeat sz (S n_cm - b)))).
        ** apply: rt_step. apply: (stepI (u := [])); [done | done|].
           do 5 apply /In_appr. rewrite /=. by tauto.
        ** apply: reachable_applI. apply: reachable_repeat_sorI. by right.
Qed.
End Transport.

Lemma transport : CM2_HALT cm -> SR2ab (srs, sz, so).
Proof.
  move=> [n /copy [Hn] /(simulate_cm_halting n Hn) H]. exists (@d n - 1).
  apply: rt_trans; last by eassumption.
  apply: rt_trans; first by apply: (reachable_enc_c0).
  elim: (n in Nat.iter n); first by apply: rt_refl.
  move=> m IH {H}. apply: rt_trans; [by exact: IH | by apply: simulate_cm_step].
Qed.

Section InverseTransport.
Context (N: nat). (* number of 0s / 1s *)
Context (HN: reachable srs (repeat sz (1+N)) (repeat so (1+N))). (* 0^N ->> 1^N *)

Local Definition rt_rt1n {A R x y} := @clos_rt_rt1n_iff A R x y.

(* s is (0^n1 l _^a m _^b r 0^n2) with a unique state annotation *)
Definition encodes : Config -> list Symbol -> Prop :=
  fun '{| state := p; value1 := a; value2 := b |} s => 
  exists u v t, s = u ++ t ++ v /\
    map fst t = map fst ([sl] ++ repeat sb a ++ [sm] ++ repeat sb b ++ [sr]) /\
    exists n1 n2, map snd t = repeat None n1 ++ [Some p] ++ repeat None n2.

    (*exists n, nth_error (map snd t) n = Some (Some p) /\ 
      forall m, m <> n -> nth m (map snd t) None = None.*)

Lemma In_srs_stE {a b c d} : In ((a, b), (c, d)) srs ->
  ((sz, sz), (st, sr)) = ((a, b), (c, d)) \/
  ((sz, st), (sl' 0, sm)) = ((a, b), (c, d)) \/
  if a is (_, None) then (if b is (_, None) then False else True) else True.
Proof.
  move=> /in_app_iff []; first by (rewrite /=; tauto).
  move=> H. right. right. move: H.
  move=> /in_app_iff [|/in_app_iff [|/in_app_iff [|/in_app_iff []]]].
  - move=> /in_flat_map [[? i]] [_] /=.
    move: i => [] [|] => [||?|?] /=; 
    firstorder (match goal with H : _ = _ |- _ => move: H => [] *; by subst end).
  - move=> /in_flat_map [?] [_] /=.
    firstorder (match goal with H : _ = _ |- _ => move: H => [] *; by subst end).
  - move=> /in_flat_map [?] [_] /=.
    firstorder (match goal with H : _ = _ |- _ => move: H => [] *; by subst end).
  - move=> /in_map_iff [?] [[]] *. by subst.
  - firstorder (match goal with H : _ = _ |- _ => move: H => [] *; by subst end).
Qed.



(* working but many cases *)
Lemma init_encodes : exists s, encodes c0 s /\ reachable srs s (repeat so (1+N)).
Proof using HN.
  have [s] : exists s, 
    reachable srs s (repeat so (1+N)) /\ 
    Forall (fun x => snd x = None) s /\
    forall n, nth n s sz = st -> nth (1+n) s sz = sr.
  { eexists. constructor; [|constructor]; [by eassumption | apply /Forall_repeatP; by tauto |].
    move: (1+N) => m n H. exfalso. elim: n m H; first by case.
    move=> n IH [|m]; [done | by apply: IH]. }
  move Ht: (repeat so (1+N)) => t [/rt_rt1n Hst] [].
  elim: Hst Ht; first by move=> ? <- /ForallE [].
  move=> {}s {}t > Hst Ht IH /IH {IH}.
  case: Hst Ht => u v a b c d /In_srs_stE [|[]].
  - move=> [] <- <- <- <- _ IH.
    move=> /Forall_appP [Hu] /ForallE [_] /ForallE [_ Ht] Huv.
    apply: IH.
    + apply /Forall_appP. constructor; first done.
      constructor; [done | by constructor].
    + move=> n. have := Huv n. elim: (u) n; first by move=> [|[|n]].
      clear. move=> x {}u IH [|n]; last by move/IH.
      move: (u) => [|? ?]; [by move=> H /H | done].
  - move=> [] <- <- <- <- /rt_rt1n Ht _ _ /(_ (1 + length u)).
    do 2 (rewrite app_nth2; first by lia).
    rewrite (ltac:(lia) : 1 + length u - length u = 1) (ltac:(lia) : 1 + (1 + length u) - length u = 2).
    move=> /(_ ltac:(done)) Hv. eexists. constructor; last by eassumption.
    move: (v) Hv => [|? v']; first done.
    move=> /= ->. exists u, v', [sl' 0; sm; sr].
    do 2 (constructor; first done). by exists 0, 2.
  - move=> H _ _ /Forall_appP [_] /ForallE [+] /ForallE [+] _.
    by move: a b H => [? [?|]] [? [?|]].
Qed.

(* possibilities to split two symbols among one app *)
Lemma eq2_app {u v a b} {s t: list Symbol} : u ++ a :: b :: v = s ++ t ->
  (exists v1, v = v1 ++ t /\ s = u ++ a :: b :: v1) \/
  (s = u ++ [a] /\ t = b :: v) \/
  (exists u2, u = s ++ u2 /\ t = u2 ++ a :: b :: v).
Proof.
  elim: u s.
  - move=> [|y1 [|y2 s]].
    + move=> /= <-. right. right. by exists [].
    + move=> [] <- <- /=. right. by left.
    + move=> [] <- <- ->. left. by exists s.
  - move=> x1 u IH [|y1 s].
    + move=> /= <-. right. right. by exists (x1 :: u).
    + move=> [] <- /IH [|[|]].
      * move=> [?] [-> ->]. left. by eexists.
      * move=> [-> ->]. right. by left.
      * move=> [?] [-> ->]. right. right. by eexists.
Qed.

(* possibilities to split two symbols among one twp apps *)
TODO: I want three possibilities with maybe richer s +1 left right
Lemma eq2_app_app {u a b v u' v'} {s: list Symbol} : length s > 1 ->
  u ++ a :: b :: v = u' ++ s ++ v' ->
  (exists u'2, v = u'2 ++ s ++ v') \/ 
  (exists s2, u' = u ++ [a] /\ s = b :: s2 /\ v = s2 ++ v') \/
  (exists s1 s2, s = s1 ++ a :: b :: s2 /\ u = u' ++ s1 /\ v = s2 ++ v') \/
  (exists s1, s = s1 ++ [a] /\ v' = b :: v) \/
  (exists v'1, u = u' ++ s ++ v'1).
Proof.
  move=> Hs /eq2_app [|[|]].
  - move=> [?] [-> ->]. left. by eexists.
  - move=> [->]. move: s Hs => [|? s] /=; first by lia.
    move=> _ [] <- <-. right. left. by eexists.
  - move=> [?] [->] /esym /eq2_app [|[|]].
    + move=> [?] [-> ->]. right. right. left. by do 2 eexists.
    + move=> [-> ->]. do 3 right. left. by eexists.
    + move=> [?] [-> ->]. do 4 right. by eexists.
Qed.


(* each srs step is sound *)
Lemma simulate_srs_step {c s t} : SR01.step srs s t -> encodes c s -> 
  halting cm c \/ encodes c t \/ encodes (CM2.step cm c) t.
Proof.
  move: c => [p a b] [] u v a' b' c' d' H [u'] [v'] [{}t].
  case=>  H /=.
  
  rewrite /encodes.

Admitted.

Lemma halting_cmI : exists n, halting cm (Nat.iter n (CM2.step cm) c0).
Proof using HN.
  have [s [H1s H2s]] := init_encodes.
  move Ht: (repeat so (1+N)) (c0) H2s H1s => t c Hst.
  have {}Ht : Forall (fun x => fst so = x) (map fst t).
  { subst t. elim: (N); by constructor. }
  move: Hst Ht c. move=> /rt_rt1n. elim.
  - move=> {}s Hs [? ? ?] /= [?] [?] [{}t] [?] [H]. subst s.
    move: Hs. rewrite ?map_app ?Forall_appP H.
    by move=> [_] [/ForallE] [].
  - move=> > /simulate_srs_step H _ IH /IH {}IH c /H {H} [|[]].
    + move=> ?. by exists 0.
    + by move=> /IH.
    + move=> /IH [n Hn]. exists (n + 1). by rewrite iter_plus.
Qed.

End InverseTransport.

Lemma inverse_transport : SR2ab (srs, sz, so) -> CM2_HALT cm.
Proof. move=> [n Hn]. apply: halting_cmI. by eassumption. Qed.

End Reduction.
End Argument.

Require Import Undecidability.Synthetic.Definitions.

Theorem reduction : CM2_HALT ⪯ SR2ab.
Proof.
  exists (fun cm => (Argument.srs cm, (4, None), (5, Some 0))).
  intro cm. constructor.
  - exact (Argument.transport cm).
  - exact (Argument.inverse_transport cm).
Qed.

Print Assumptions reduction.
