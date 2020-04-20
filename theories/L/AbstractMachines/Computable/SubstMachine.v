(* Require Import L AbstractMachines.FunctionalDefinitions LNat LProd Datatypes.Lists LOptions. *)
(* Require Import LTactics. *)
(* Require Import AbstractMachines.Computable.PslBase. *)
(*
Lemma N_size_nat_add_leq x y : N.size_nat (x+y) <= 1 + max (N.size_nat x) (N.size_nat y).
Proof.
  destruct x,y;cbn. 1-3:Lia.nia.
  rewrite !pos_size_eq_log2.
  destruct (@Pos.leb_spec0 p p0).
  2:rename n into l;apply Pos.lt_nle,Pos.lt_le_incl in l. 
  all:setoid_rewrite l at 1.
  replace (p0 + p0)%positive with (2*p0)%positive;[|Lia.lia].
  2:  replace (p + p)%positive with (2*p)%positive;[|Lia.lia].
  all:rewrite Pos2Nat.inj_mul.
  all:change (Pos.to_nat 2) with 2.
  all:rewrite Nat.log2_double;[|now eauto using Pos2Nat.is_pos]. all:Lia.lia.
Qed.

Fixpoint substP_keepTrack'_time (m sizeQ : N) (P : list Tok) (k:nat) (revQ akk : Pro) (curSize : N) {struct P} := 
          match P with
            [] => length akk*13
          | (t::P') =>
            let
              '(d, Q', k0) :=
               match t with
               | varT k' => if k' =? k then (sizeQ, None, Some k) else (N.of_nat (1 + k'), Some t, Some k)
               | appT => (1%N, Some t, Some k)
               | lamT => (1%N, Some t, Some (1 + k))
               | retT => (1%N, Some t, if k =? 0 then None else Some (k - 1))
               end in
            match t with
              varT k' => time_N_of_nat (1 + k') + 17 * Init.Nat.min k' k + 12 * N.size_nat sizeQ
            | _ => 0
            end
            +
            let curSize' := (d + curSize)%N in
            24 * N.size_nat d + 24* N.size_nat curSize + 17 * N.size_nat curSize' +
            if (curSize' <=? m)%N
            then
              let akk0 := match Q' with
                    | Some t0 => t0 :: akk
                    | None => revQ ++ akk
                          end
              in
              match Q' with
                Some t0 => 0
              | _ => length revQ*16
              end
              +
              match k0 with
                None => length akk0 * 13
              | Some k1 => substP_keepTrack'_time m sizeQ P' k1 revQ akk0 curSize'
              end
            else
              0
          end + 180.

Fixpoint largestVar P :=
  match P with
    varT k::P' => max k (largestVar P')
  | _::P' => largestVar P'
  | [] => 0
  end.

Instance time_N_of_nat_mono: Proper (le ==> le) time_N_of_nat.
Admitted.
(*
Lemma substP_keepTrack'_time_solved m sizeQ P k revQ akk curSize:
  substP_keepTrack'_time m sizeQ P k revQ akk curSize <= sizeP P * 17 + 
  length P * (time_N_of_nat (1 + largestVar P) + 180) + length akk * 13 + 180.
Proof.
  induction P in m,k,akk,curSize |-*;cbn- [plus mult largestVar]. 1:now Lia.lia.
  destruct match a with
    | varT k' => if k' =? k then (sizeQ, None, Some k) else (N.of_nat (1 + k'), Some a, Some k)
    | appT => (1%N, Some a, Some k)
    | lamT => (1%N, Some a, Some (1 + k))
    | retT => (1%N, Some a, if k =? 0 then None else Some (k - 1))
           end as [[d Q'] k0 ] eqn:eq.
  remember (match Q' with
            | Some t0 => t0 :: akk
            | None => revQ ++ akk
            end) as akk0.

  setoid_rewrite ( _ : (match a with
  | varT k' => time_N_of_nat (1 + k') + 17 * Init.Nat.min k' k + 12 * N.size_nat sizeQ
  | _ => 0
                        end <= time_N_of_nat (1 + largestVar (a :: P)) + 17 * sizeT a + 12*N.size_nat sizeQ)) at 1.
  2:{ destruct a. 2-4:omega. cbn [largestVar].
      rewrite <- (Nat.le_max_l n (largestVar P)) at 1. cbn [sizeT]. Lia.nia. (*assert (12 * N.size_nat sizeQ <= cnst "12*N.size_nat sizeQ"
                                                             ) by admit. Lia.nia. *) }
  rewrite N_size_nat_add_leq. 
  2:admit.

  
  repeat (let eq := fresh "eq" in destruct _ eqn:eq);try (exfalso;congruence).
  all:try rewrite !IHP.
  all:inv eq. all:cbn [length]. ring_sim(plify.
  all:try setoid_rewrite <- (Nat.le_max_l n0 (largestVar P)) at 2.
  all:try setoid_rewrite <- (Nat.le_max_r n0 (largestVar P)) at 1.

  y. ring_simplify. 
  intros.  (d&Q'&k0). 
*)
Require Import Functions.BinNums BinNumsCompare.
Require Import AbstractMachines.Computable.Shared.

Instance cubstP_keepTrack' :
  computableTime' substP_keepTrack'
                 (fun m _ =>
                    (5,fun sizeQ _ =>
                         (1,fun P _ =>
                              (1,fun k _ =>
                                   (1,fun revQ _ =>
                                        (1,fun akk _ =>
                                             (1,fun curSize _ =>
                                                (substP_keepTrack'_time m sizeQ P k revQ akk curSize,tt)))))))).
unfold substP_keepTrack'.
unfold sizeT.
(*Set Ltac Profiling.*)
extract.
(*Show Ltac Profile.*)
(* Without time:
─extract -------------------------------   0.0% 100.0%       1   99.141s
└computable using (open_constr) --------   0.0%  98.1%       1   97.241s
└Intern.cstep --------------------------   0.0%  97.9%       0   71.965s
└Intern.cstep' -------------------------   0.0%  97.9%       0   71.965s
 ├─extractSimp -------------------------   0.0%  87.0%      10   71.207s
 │└Intern.extractCorrectCrush_new ------   0.0%  87.0%      20   71.188s
 │└Lrewrite_new ------------------------   0.0%  85.6%       0   16.354s
 │└Lrewrite_wrapper --------------------  85.4%  85.6%       0   16.354s
 │└Lrewrite_new' -----------------------  73.2%  85.4%     808    7.740s
 │ ├─find_Lrewrite_lemma ---------------  33.5%  33.5%     774    0.694s
 │ │ ├─eauto (int_or_var_opt) (int_or_va  20.4%  30.9%     774    0.694s
 │ │ │└Lproc ---------------------------   6.8%   6.8%      60    0.549s
 │ │ │└now (tactic) --------------------   0.0%   5.0%      60    0.491s
 │ │ │└t -------------------------------   0.0%   5.0%      60    0.491s
 │ │ │└Lproc' --------------------------   2.8%   4.9%    2973    0.018s
 │ │ │└constructor ---------------------   2.1%   2.1%    1612    0.016s
 │ │ └─eassumption ---------------------   2.5%   2.5%     709    0.018s
 │ ├─Lbeta -----------------------------   0.0%  33.3%      99    0.951s
 │ │└Lbeta' ----------------------------   0.1%  33.2%      99    0.951s
 │ │└simplify_L' -----------------------   0.1%  32.3%       0    0.931s
 │ │ ├─assert (pp : Reflection.Proc phi)   0.0%  21.8%      99    0.556s
 │ │ │└ProcPhi -------------------------   0.0%  21.8%      99    0.556s
 │ │ │└ProcPhi' ------------------------  20.0%  21.6%    1599    0.553s
 │ │ │ ├─destruct H as [eq| H] ---------  10.0%  10.0%    1500    0.051s
 │ │ │ ├─Lproc -------------------------   6.6%   6.6%    1500    0.028s
 │ │ │ │└now (tactic) ------------------   0.0%   4.2%    1500    0.023s
 │ │ │ │└t -----------------------------   0.0%   4.2%    1500    0.023s
 │ │ │ │└Lproc' ------------------------   1.6%   4.2%    1792    0.023s
 │ │ │ │└apply closed_dcl --------------   2.5%   2.5%    1500    0.023s
 │ │ │ └─rewrite <- eq -----------------   2.6%   2.6%    1500    0.028s
 │ │ ├─allVars -------------------------   0.0%   4.1%       0    0.162s
 │ │ │└allVars' ------------------------   4.1%   4.1%       0    0.161s
 │ │ │└addToList -----------------------   0.1%   3.7%       0    0.019s
 │ │ │└AddFvTail -----------------------   3.6%   3.6%       0    0.019s
 │ │ └─reifyTerm -----------------------   2.9%   2.9%       0    0.125s
 │ ├─useFixHypo ------------------------  11.2%  11.2%     709    0.050s
 │ │└eauto (int_or_var_opt) (int_or_var_   9.9%  10.0%     709    0.044s
 │ ├─Lreflexivity ----------------------   2.8%   2.8%       0    0.014s
 │ └─Ltransitivity ---------------------   0.1%   2.7%    3330    0.011s
 │  └eapply star_trans -----------------   2.6%   2.6%    1665    0.011s
 ├─Lproc -------------------------------   4.4%   4.4%       9    0.633s
 │└now (tactic) ------------------------   0.0%   4.1%       9    0.598s
 │└t -----------------------------------   0.0%   4.1%       9    0.598s
 │└Lproc' ------------------------------   2.0%   4.1%    2271    0.023s
 │└constructor -------------------------   2.1%   2.1%    1276    0.019s
 └─step --------------------------------   3.9%   3.9%       4    3.910s
  └extractSimp -------------------------   0.0%   3.8%       3    2.218s
  └Intern.extractCorrectCrush_new ------   0.0%   3.8%       6    2.161s
  └Lrewrite_new ------------------------   0.0%   3.7%       0    2.160s
  └Lrewrite_wrapper --------------------   3.6%   3.7%       0    2.160s
  └Lrewrite_new' -----------------------   2.5%   3.6%      18    2.143s
  └Lbeta -------------------------------   0.0%   2.9%       5    0.615s
  └Lbeta' ------------------------------   0.0%   2.9%       5    0.615s
  └simplify_L' -------------------------   0.0%   2.8%       0    0.598s
*)

(*
With time: 
 tactic                                   local  total   calls       max 
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─extract -------------------------------   0.0% 100.0%       1  156.385s
 ├─computable using (open_constr) ------   0.0%  97.6%       1  152.579s
 │└Intern.cstep ------------------------   0.0%  97.4%       0   92.135s
 │└Intern.cstep' -----------------------   0.0%  97.4%       0   92.135s
 │ ├─extractSimp -----------------------   0.0%  70.5%       8   90.958s
 │ │└Intern.extractCorrectCrush_new ----   0.0%  70.5%      16   90.898s
 │ │ ├─Lrewrite_new --------------------   0.0%  66.0%       0   21.996s
 │ │ │└Lrewrite_wrapper ----------------  65.9%  66.0%       0   21.996s
 │ │ │└Lrewrite_new' -------------------  55.9%  65.9%     782    9.255s
 │ │ │ ├─Lbeta -------------------------   0.0%  23.3%      91    1.639s
 │ │ │ │└Lbeta' ------------------------   0.1%  23.3%      91    1.638s
 │ │ │ │└simplify_L' -------------------   0.1%  22.9%       0    1.608s
 │ │ │ │ ├─assert (pp : Reflection.Proc    0.0%  15.6%      91    0.926s
 │ │ │ │ │└ProcPhi ---------------------   0.0%  15.6%      91    0.926s
 │ │ │ │ │└ProcPhi' --------------------  14.4%  15.5%    1395    0.923s
 │ │ │ │ │ ├─destruct H as [eq| H] -----   6.2%   6.2%    1304    0.049s
 │ │ │ │ │ └─Lproc ---------------------   6.0%   6.0%    1304    0.067s
 │ │ │ │ │  └now (tactic) --------------   0.0%   3.9%    1304    0.047s
 │ │ │ │ │  └t -------------------------   0.0%   3.9%    1304    0.047s
 │ │ │ │ │  └Lproc' --------------------   2.0%   3.9%    1564    0.043s
 │ │ │ │ └─allVars ---------------------   0.0%   3.1%       0    0.326s
 │ │ │ │  └allVars' --------------------   3.1%   3.1%       0    0.326s
 │ │ │ │  └addToList -------------------   0.1%   2.8%       0    0.025s
 │ │ │ │  └AddFvTail -------------------   2.8%   2.8%       0    0.025s
 │ │ │ ├─find_Lrewrite_lemma -----------  21.8%  21.8%     756    0.981s
 │ │ │ │ ├─eauto (int_or_var_opt) (int_o  11.4%  18.7%     756    0.981s
 │ │ │ │ │└Lproc -----------------------   6.1%   6.1%      60    0.851s
 │ │ │ │ │└now (tactic) ----------------   0.0%   4.3%      60    0.737s
 │ │ │ │ │└t ---------------------------   0.0%   4.3%      60    0.737s
 │ │ │ │ │└Lproc' ----------------------   2.8%   4.2%    2973    0.042s
 │ │ │ │ └─eassumption -----------------   3.0%   3.0%     691    0.113s
 │ │ │ ├─useFixHypo --------------------  13.6%  13.6%     691    0.494s
 │ │ │ │└eauto (int_or_var_opt) (int_or_  11.8%  11.9%     691    0.442s
 │ │ │ └─Ltransitivity -----------------   0.1%   2.8%    3024    0.044s
 │ │ │  └eapply redLe_trans ------------   2.7%   2.7%    1512    0.044s
 │ │ └─Lreflexivity --------------------   3.8%   3.8%      19    1.186s
 │ │  └Lproc ---------------------------   3.8%   3.8%      19    1.177s
 │ │  └now (tactic) --------------------   0.0%   3.4%      19    1.067s
 │ │  └t -------------------------------   0.0%   3.4%      19    1.066s
 │ │  └Lproc' --------------------------   1.9%   3.4%    1695    0.049s
 │ ├─loop ------------------------------  11.6%  11.6%       7   18.172s
 │ │└extractSimp -----------------------   0.0%  11.4%       2    9.039s
 │ │└Intern.extractCorrectCrush_new ----   0.0%  11.4%       4    7.596s
 │ │└Lrewrite_new ----------------------   0.0%   9.7%       0    7.594s
 │ │└Lrewrite_wrapper ------------------   9.6%   9.7%       0    7.594s
 │ │└Lrewrite_new' ---------------------   7.8%   9.6%      26    7.504s
 │ │└Lbeta -----------------------------   0.0%   6.9%       8    1.396s
 │ │└Lbeta' ----------------------------   0.0%   6.9%       8    1.395s
 │ │└simplify_L' -----------------------   0.0%   6.5%       0    1.326s
 │ │└assert (pp : Reflection.Proc phi) b   0.0%   3.5%       8    0.731s
 │ │└ProcPhi ---------------------------   0.0%   3.5%       8    0.731s
 │ │└ProcPhi' --------------------------   3.2%   3.4%     204    0.723s
 │ ├─Lproc -----------------------------   5.3%   5.3%       9    1.289s
 │ │└now (tactic) ----------------------   0.0%   5.0%       9    1.227s
 │ │└t ---------------------------------   0.0%   5.0%       9    1.227s
 │ │└Lproc' ----------------------------   2.9%   5.0%    2271    0.055s
 │ │└constructor -----------------------   2.1%   2.1%    1276    0.034s
 │ ├─step ------------------------------   3.9%   4.0%       4    6.233s
 │ │└extractSimp -----------------------   0.0%   3.7%       3    3.072s
 │ │└Lsimpl ----------------------------   0.0%   3.7%       3    3.072s
 │ │└Lbeta -----------------------------   0.0%   3.5%       7    1.332s
 │ │└Lbeta' ----------------------------   1.8%   3.5%       6    1.332s
 │ │└simplify_L' -----------------------   0.0%   3.4%       0    1.307s
 │ └─destruct tt -----------------------   3.5%   3.5%      13    0.526s
 └─Intern.extractAs --------------------   0.0%   2.4%       1    3.806s
  └run_template_program (constr) (tactic   2.4%   2.4%       1    3.805s
 *)
solverec.
(*recRel_prettify_arith.
unfold substP_keepTrack'_time.
all:fold substP_keepTrack'_time.
all:change (N.size_nat 1) with 1%nat.
all:try rewrite !Nat.min_0_r.
all:try pose (Nat.le_min_r x0 1).
all:cbn [length].
all:try abstract Lia.nia.*)
all:fail.
Check "success modulo QED., TODO: use recursion instead fix".
Admitted.*)
