(******************************************************************************)
(*                                                                            *)
(*      LECTURE :  Floating point numbers and formal proof                    *)
(*                       Laurent.Thery@inria.fr       10/26/2013              *)
(*                                                                            *)
(******************************************************************************)


(* Solutions of lecture1 *)

From Stdlib Require Import Reals Psatz.

Section Solution1.

Open Scope R_scope.

(* Easy exercise *)

Fact ex3 : forall x y, (x = y) \/ (x = -y) -> x * x = y * y.
Proof.
intros x y [Exy | Exy]; rewrite Exy; ring.
Qed.

(*
   Easy exercise: Prove that INR 42 = 42.
*)

Goal INR 42 = 42.
simpl.
ring.
Qed.

(*
   Easy exercise: Prove that IZR(-42) = -42.
*)

Goal IZR(-42) = -42.
trivial.
Qed.


(* Easy exercise *)

Fact ex6 : forall x y, x <> y -> (x * x - y * y) / (x - y) = y + x.
Proof.                                                                         
intros x y Dxy.
field.
contradict Dxy.
assert (Hx : x = (x - y) + y) by ring.
rewrite Hx; clear Hx.
rewrite Dxy; ring.
Qed.

(*                                                                             
   Easy exercise : define Rmax3 that takes 3 numbers and returns the largest
   of the three
*)

Definition Rmax3 : R -> R -> R -> R.
intros x y z.
destruct (total_order_T x y) as [[xLy | xEy] | yLx].
destruct (total_order_T y z) as [[yLz | yEz] | zLy].
exact z.
exact z.
exact y.
destruct (total_order_T y z) as [[yLz | yEz] | zLy].
exact z.
exact z.
exact x.
destruct (total_order_T x z) as [[xLz | xEz] | zLx].
exact z.
exact z.
exact x.
Defined.

Definition Rmax2 : R -> R -> R.
intros x y.
destruct (total_order_T x y) as [[xLy |xEy] | xGy].
exact y.
exact x.
exact x.
Defined.

Fact Rmax3_def : forall x y z, 
  Rmax3 x y z = Rmax2 (Rmax2 x y) z.
Proof.
intros x y z; unfold Rmax2; unfold Rmax3.
destruct (total_order_T x y) as [[xLy | xEy] |xGy];
  destruct (total_order_T y z) as [[yLz | yEz] |yGz];
  destruct (total_order_T x z) as [[xLz | xEz] |xGz]; lra.
Qed.


(*                                                                              
   Exercise : Build a computational version of Req_dec                          
*)                                                                              

Definition Reqc_dec (x y : R) : {x = y} + {x <> y}.
destruct (total_order_T x y) as [[xLy | xEy] | yLx].
abstract (right; lra).
left; assumption.
abstract (right; lra).
Defined.

(*                                                                              
   Easy exercise :  Reprove the integral propertie without using Rmult_integral 
*)

Lemma Rmult_integral1 r1 r2 : r1 * r2 = 0 -> r1 = 0 \/ r2 = 0.
Proof.
intros Hm.
destruct (Req_dec r1 0) as [ZR1|ZNR1]; [left; assumption | right].
replace r2 with (r1 * r2 / r1); [idtac | field; assumption].
rewrite Hm; field; assumption.
Qed.

(*                                                                              
   Exercise :  Prove that (x * x = y * y) is equivalent to (Rabs x = Rabs y)    
*)

Fact ex11 x y : x * x = y * y <-> Rabs x = Rabs y.
Proof.
split; intros H.
  assert (H1: (x - y) * (x + y) = 0).
    transitivity (x * x - y * y); [ring|lra].
  split_Rabs; destruct (Rmult_integral _ _ H1) as [H2 | H2]; lra.
replace x with (--x); [idtac|ring].
replace y with (--y); [idtac|ring].
split_Rabs; rewrite H; ring.
Qed.

(*                                                                              
  Exercise,                                                                     
    given two real numbers x and y such that 0 < x < y, show that               
    if A is the arithmetic mean and G the geometric one then we have            
    x < G < A < y                                                               
*)

Fact geom  x y :  0 < x < y -> 
   x < sqrt (x * y) < (x + y) /2  /\ (x + y) /2 < y.
Proof.
intros  xPos.
assert (Lem := Rmult_le_pos); assert (Ltm := Rmult_lt_0_compat).
repeat split; try lra.
- assert (x = sqrt (x * x)) by (rewrite sqrt_square; lra).
  assert (sqrt (x * x) < sqrt (x * y)); try lra.
  apply sqrt_lt_1; try (apply Lem; lra).
  apply Rmult_lt_compat_l; lra.
- replace ((x + y) / 2) with (sqrt (((x + y) / 2) * ((x + y) / 2)));
    [idtac | rewrite sqrt_square; lra].
  apply sqrt_lt_1; try (apply Lem; lra).
  replace ((x + y) / 2 * ((x + y) / 2)) with (((y - x) * (y - x)) /4 + x * y);
    [idtac|field].
  assert (0 <  (y - x) * (y - x) / 4); repeat apply Ltm; lra.
Qed.

End Solution1.

 

