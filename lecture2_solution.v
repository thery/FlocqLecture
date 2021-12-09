(******************************************************************************)
(*                                                                            *)
(*      LECTURE :  Floating-point numbers and formal proof                    *)
(*                       Laurent.Thery@inria.fr       10/27/2013              *)
(*                                                                            *)
(******************************************************************************)

(* Solutions of lecture 2 *)

Require Import Psatz Reals.
From Flocq Require Import Core.

Section Solution2.

Open Scope R_scope.

Variable F : R -> Prop.                     (* The predicate "to be a float"  *)

Variable P : R -> R -> Prop.                (* The relation                     
                                                 "to be a rounded value of"   *)

Fact ex2 : round_pred_monotone (Rnd_DN_pt F).   (*  Rnd_Dn_pt monotone        *)
Proof.
intros x y f g Rxf Rxg xLy.
destruct Rxf as [Ff [fLx fdown]].
destruct Rxg as [Fg [gLy gdown]].
apply gdown; try lra; assumption.
Qed.

(*                                                                              
  Prove that UP is also idempotent and monotone                                 
*)

Fact ex3 : forall x, F x -> Rnd_UP_pt F x x.
Proof.
intros x Fx; repeat split; try lra; auto.
Qed.

Fact ex4 : round_pred_monotone (Rnd_UP_pt F).
Proof.
intros x y f g [Ff [xLf Hf]] [Fg [yLg Hg]] xLy.
apply Hf; try lra; auto.
Qed.

(*
  Prove that ZR is idempotent but only monotone if 0 is a floating point number 
*)

Fact ex5 :  forall x, F x -> Rnd_ZR_pt F x x.
Proof.
intros x Fx; repeat split; try lra; auto.
Qed.

Fact ex6 : F 0 -> round_pred_monotone (Rnd_ZR_pt F).
Proof.
intros F0 x y f g [HPf HNf] [HPg HNg] xLy.
destruct (Rle_lt_dec 0 x) as [xPos | xNPos];
 destruct (Rle_lt_dec 0 y) as [yPos | yNPos]; try lra.
- apply (ex2 x y); auto.
- assert (xNeg : x <= 0) by lra.
  assert (f <= 0).
    destruct (HNf xNeg) as [_ [_ H1f]].
    apply H1f; auto.
  assert (0 <= g).
    destruct (HPg yPos) as [_ [_ H1g]].
    apply H1g; auto.
  lra.
- assert (xNeg : x <= 0) by lra.
  assert (yNeg : y <= 0) by lra.
  apply (ex4 x y); auto.
Qed.

(*                                                                              
Hint:                                                                           
 In order to perform a case analysis on the fact that x is smaller to y or not  
 one can use the tactic "destruct (Rle_lt_dec x y) as [xLy | yLx]"              
                                                                                
*)

Hypothesis SAF : satisfies_any F.

(*                                                                              
   Prove that DN, UP, ZR are rounding predicates                                
*)

Fact ex8  : round_pred (Rnd_DN_pt F).
Proof.
destruct SAF as [F0 Fsym DNtotal]; split; auto.
apply ex2.
Qed.

Fact ex9  : round_pred (Rnd_UP_pt F).
Proof.
destruct SAF as [F0 Fsym DNtotal].
split.
- intros x.
  destruct (DNtotal (-x)) as [f [Ff [fLNx Pf]]].
  exists (- f); repeat split; try lra.
  apply Fsym; auto.
  intros g Fx xLg.
  assert (-g <= f).
    apply Pf; try lra.
    apply Fsym; auto.
  lra.
- apply ex4.
Qed.

Fact ex10 : round_pred (Rnd_ZR_pt F).
Proof.
split.
- intros x.
  destruct (Req_dec x 0) as [xE0 | xD0].
    exists 0; rewrite xE0.
    apply ex5; destruct SAF; auto.
  destruct ex8 as [DP _].
  destruct (DP x) as [f1 Hf1].
  destruct ex9 as [UP _].
  destruct (UP x) as [f2 Hf2].
  destruct (Rle_dec 0 x) as [xPos | xNPos].
  exists f1; split; try lra; auto.
  exists f2; split; try lra; auto.
- apply ex6; destruct SAF; auto.
Qed.

(*                                                                              
  Prove that N is idempotent, that it is either UP or DOWN and that it is       
  strictly monotone                                                             
*)

Fact ex11 : forall x, F x -> Rnd_N_pt F x x.
Proof.
intros x Fx; split; auto.
intros g Fg.
assert (H : x - x = 0) by lra.
rewrite H, Rabs_R0.
apply Rabs_pos.
Qed.

Fact ex12 : forall x f, Rnd_N_pt F x f -> Rnd_DN_pt F x f \/ Rnd_UP_pt F x f.
Proof.
intros x f [Ff Pf].
destruct (Rle_dec x f) as [xLf|xGf].
- right; repeat split; auto.
  intros g Fg xLg.
  assert (Hg := Pf g Fg).
  rewrite !Rabs_right in Hg; lra.
- left; repeat split; try lra; auto.
  intros g Fg gLx.
  assert (Hg := Pf g Fg).
  rewrite !Rabs_left1 in Hg; lra.
Qed.

Fact ex13 : forall x y f g, 
  Rnd_N_pt F x f -> Rnd_N_pt F y g -> x < y -> f <= g.
Proof.
intros x y f g [Ff Pf] [Fg Pg] xLy.
assert (Hg := Pf g Fg).
assert (Hf := Pg f Ff).
destruct (Rle_dec f g) as [fLg|fGg]; try lra.
destruct (Rle_dec f x) as [fLx|fGx].
- rewrite !Rabs_left1 in Hg; try lra.
  rewrite !Rabs_left1 in Hf; try lra.
- rewrite Rabs_right in Hg; try lra.
  destruct (Rle_dec g x) as [gLx|gGx]; try lra.
  rewrite Rabs_left1 in Hg; try lra.
  rewrite Rabs_left1 in Hf; try lra.
  destruct (Rle_dec f y) as [fLy|fGy]; try lra.
  rewrite Rabs_left1 in Hf; try lra.
  rewrite Rabs_right in Hf; try lra.
  rewrite Rabs_right in Hg; try lra.
Qed. 

(*                                                                              
Hints : some theorems about absolute values                                     
Check Rabs_R0.                                                                  
Check Rabs_pos.                                                                 
Check Rabs_right.                                                               
Check Rabs_left.                                                                
                                                                                
*)
  

Variable T : R -> R -> Prop.                            (* Tie-break rule     *)

Definition Taway x f := Rabs f >= Rabs x.


(* 
  Prove that Taway verifies the two condition that are needed to build a        
  rounding mode                                                                 
*)

Fact ex14 : NG_existence_prop F Taway.
Proof.
intros x d u NFx DNd UPu.
destruct (Rle_dec 0 x) as [xPos|xNPos].
- left; red.
  destruct (UPu) as [Fu [xLu _]].
  rewrite !Rabs_right; lra.
- right; red.
  destruct (DNd) as [Fd [dLx _]].
  rewrite !Rabs_left1; lra.
Qed.

Fact ex15 : F 0 -> Rnd_NG_pt_unique_prop F Taway.
Proof.
intros F0 x d u [Fd [dLx Pd]] [_ Nd] [Fu [xLu Pu]] [_ Nu].
unfold Taway.
destruct (Rle_dec 0 x) as [xPos|xNPos].
- rewrite (Rabs_right x); try lra.
  assert (dPos : 0 <= d).
    apply Pd; try lra; auto.
  rewrite Rabs_right; try lra.
  intros dGx _.
  assert (xEd : x = d); try lra.
  assert (HH := Nu d Fd).
  rewrite !Rabs_right in HH; lra.
- rewrite (Rabs_left1 x); try lra.
  assert (uNeg : u <= 0).
  apply Pu; try lra; auto.
  rewrite (Rabs_left1 u); try lra.
  intros _ uLx.
  assert (xEu : x = u); try lra.
  assert (HH := Nd u Fu).
  rewrite !Rabs_left1 in HH; lra.
Qed.

End Solution2.