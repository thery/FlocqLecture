(******************************************************************************)
(*                                                                            *)
(*      LECTURE :  Floating-point numbers and formal proof                    *)
(*                       Laurent.Thery@inria.fr       12/04/2013              *)
(*                                                                            *)
(******************************************************************************)

(* Solutions of lecture 4 *)

Require Import Psatz.
From Flocq Require Import FTZ Core Operations.

Open Scope R_scope.

Section Solution4.

Variable r : radix.
Variable phi : Z -> Z.
Hypothesis vPhi : Valid_exp phi.
Variable rnd : R -> Z.
Hypothesis vRound : Valid_rnd rnd.
Variable choice : Z -> bool.

(*                                                                              
  Prove that if phi is monotone so is ulp                                       
*)

Fact ex1 x y :
  x <> 0 -> Monotone_exp phi -> 
   Rabs x <= Rabs y -> ulp r phi x <= ulp r phi y.
Proof.
intros NZx Mphi Rxy.
assert (NZy : y <> 0) by (split_Rabs; lra).
rewrite !ulp_neq_0; auto.
apply bpow_le.
apply Mphi.
apply mag_le_abs; assumption.
Qed.

(*                                                                              
Hints:                                                                          
                                                                                
Check mag_le_abs.                                                           
Check bpow_le.                                                                  
                                                                                
*)

(*                                                                              
  Reprove round_UP_DN_ulp                                                             
*)

Fact ext2 x : 
  ~ generic_format r phi x ->
  round r phi Zceil x = round r phi Zfloor x + ulp r phi x.
Proof.
intros H.
assert (NZx : x <> 0).
  contradict H; rewrite H; apply generic_format_0.
rewrite ulp_neq_0; auto.
unfold round, F2R; simpl.
rewrite Zceil_floor_neq; rewrite ?plus_IZR; simpl; try ring.
contradict H.
unfold generic_format, F2R; simpl.
rewrite <- H, Ztrunc_IZR, H.
rewrite scaled_mantissa_mult_bpow; auto.
Qed.

(*                                                                              
Hints:                                                                          
                                                                                
Check scaled_mantissa_mult_bpow.                                                
Check Zceil_floor_neq.                                                          
Check Ztrunc_IZR.                                                               
                                                                                
*)

(*                                                                              
  Reprove error_lt_ulp                                                          
*)


Fact ext3 x : x <> 0 -> Rabs (round r phi rnd x - x) < ulp r phi x.
Proof.
intro NZx.
assert (H : generic_format r phi x \/ ~ generic_format r phi x).
  unfold generic_format, F2R; simpl.
  set (y := _ * _); case (Req_dec x y); auto.
destruct H.
  set (y := _ - _); replace y with 0.
    rewrite Rabs_R0, ulp_neq_0; auto; apply bpow_gt_0.
  unfold y; rewrite round_generic; auto; ring.
assert (H1 := round_DN_UP_lt _ _ _ H).
assert (H2 := round_UP_DN_ulp _ _ _ H).
destruct (round_DN_or_UP r phi rnd x).
split_Rabs; lra.
split_Rabs; lra.
Qed.

(*                                                                              
Hints :                                                                         
                                                                                
Check round_DN_UP_lt.                                                           
Check round_DN_or_UP.                                                           
Check round_UP_DN_ulp.                                                                
                                                                                
*)

(*                                                                              
  Reprove error_le_half_ulp                                                     
*)

Fact ext4 x :
    Rabs (round r phi (Znearest choice) x - x) <=
         / 2 * ulp r phi x.
Proof.
assert (H : generic_format r phi x \/ ~ generic_format r phi x).
  unfold generic_format, F2R; simpl.
  set (y := _ * _); case (Req_dec x y); auto.
destruct H.
  set (y := _ - _); replace y with 0.
    rewrite Rabs_R0.
    apply Rmult_le_pos; try lra; apply ulp_ge_0.
  unfold y; rewrite round_generic; auto; try ring.
  apply valid_rnd_N.
destruct (round_N_pt r phi choice x) as (Hr1, Hr2).
assert (H1 := generic_format_round r phi Zfloor x).
assert (H2 := generic_format_round r phi Zceil x).
assert (H3 := Hr2 _ H1).
assert (H4 := Hr2 _ H2).
assert (H5 := round_UP_DN_ulp _ _ _ H).
assert (H6 := round_DN_UP_lt _ _ _ H).
destruct (round_DN_or_UP r phi (Znearest choice) x).
revert H3 H4.
split_Rabs; try lra.
split_Rabs; try lra.
Qed.

(*                                                                              
Hints:                                                                          
                                                                                
Check round_N_pt.                                                               
Check generic_format_round.                                                     
Check round_DN_UP_lt.                                                           
Check round_DN_or_UP.                                                           
Check round_UP_DN_ulp.                                                                
                                                                                
*)

End Solution4.