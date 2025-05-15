(******************************************************************************)
(*                                                                            *)
(*      LECTURE :  Floating-point numbers and formal proof                    *)
(*                       Laurent.Thery@inria.fr       12/05/2016              *)
(*                                                                            *)
(******************************************************************************)

(*                                                                              
                                                                                
  How to define floating point numbers ?                                        
                                                                                
  We are going to use the flocq library at http://flocq.gforge.inria.fr/        
                                                                                
*)

From Stdlib Require Import Psatz Reals.
From Flocq Require Import Core.

Section Lecture2.

Open Scope R_scope.

Axiom todo : forall P, P.
Ltac todo := apply todo.

(* We start very abstractly                                                   *)

Variable F : R -> Prop.                     (* The predicate "to be a float"  *)

Variables vx vy : R.                        (* Some values for our examples   *)

Check F vx.                                 (* vx is a floating-point number  *)

Variable P : R -> R -> Prop.                (* The relation                     
                                                "to be a rounded value"       *)

Check P vx vy.                              (* vy is a rounded value of vx    *)


(******************************************************************************)
(*                         ROUNDING RELATION                                  *)
(******************************************************************************)

(* What do we require for our relation "to be a rounded value"?               *)

Lemma round_pred_P : round_pred P.
Proof.
split; red.
todo.                                       (* - to be total                  *)
todo.                                       (* - to be monotone               *)
Qed.

Definition rnd := let (f, _) := round_fun_of_pred P round_pred_P in f.

Check rnd.                                  (* the function associated with the 
                                               relation                       *)

Lemma rndP : forall x, P x (rnd x).         (* its associated relation        *)
Proof. unfold rnd; destruct (round_fun_of_pred P round_pred_P); auto. Qed.


(******************************************************************************)
(*                        ROUNDING DOWN, UP, TO ZERO                          *)
(******************************************************************************)

(* DOWN *)
Check Rnd_DN_pt F vx vy.
Eval lazy beta delta [Rnd_DN_pt] in Rnd_DN_pt F vx vy.

Check Rnd_DN F rnd.
Eval lazy beta delta [Rnd_DN] in Rnd_DN F rnd.

(* UP   *)
Check Rnd_UP_pt F vx vy.
Eval lazy beta delta [Rnd_UP_pt] in Rnd_UP_pt F vx vy.

Check Rnd_UP F rnd.
Eval lazy beta delta [Rnd_UP] in Rnd_UP F rnd.

(* ZERO *)
Check Rnd_ZR_pt F vx vy.
Eval lazy beta delta [Rnd_ZR_pt] in Rnd_ZR_pt F vx vy.

Check Rnd_ZR F rnd.
Eval lazy beta delta [Rnd_ZR] in Rnd_ZR F rnd.

(******************************************************************************)
(*                       IDEMPOTENCE AND MONOTONY                             *)
(******************************************************************************)

Fact ex1 : forall x, F x -> Rnd_DN_pt F x x.    (* Rnd_Dn_pt idempotent on F  *)
Proof. 
intros x Fx; repeat split.
- assumption.
- lra.
- intros g Fg gLx; assumption.
Qed.

Fact ex2 : round_pred_monotone (Rnd_DN_pt F).   (*  Rnd_Dn_pt monotone        *)
Proof.
intros x y f g Rxf Rxg xLy.
destruct Rxf as [Ff [fLx fdown]].
destruct Rxg as [Fg [gLy gdown]].
apply gdown; try lra; assumption.
Qed.

(*                                                                              
  Prove that UP is also idempotent and monotone                                 
                                                                                
Fact ex3 : forall x, F x -> Rnd_UP_pt F x x.                                    
Proof.                                                                          
...                                                                             
Qed.                                                                            
                                                                                
Fact ex4 : round_pred_monotone (Rnd_UP_pt F).                                   
Proof.                                                                          
...                                                                             
Qed.                                                                            
                                                                                
  Prove that ZR is idempotent but only monotone if 0 is a float                 
                                                                                
Fact ex5 :  forall x, F x -> Rnd_ZR_pt F x x.                                   
Proof.                                                                          
...                                                                             
Qed.                                                                            
                                                                                
Fact ex6 : F 0 -> round_pred_monotone (Rnd_ZR_pt F).                            
Proof.                                                                          
...                                                                             
Qed.                                                                            
                                                                                
Hint:                                                                           
 In order to perform a case analysis on the fact that x is smaller to y or not  
 one can use the tactic "destruct (Rle_lt_dec x y) as [xLy | yLx]"              
                                                                                
*)

(******************************************************************************)
(*                              TOTALITY                                      *)
(******************************************************************************)


Fact ex7 : (forall x, F x -> F (-x)) ->          (* the format is symmetric   *)
   round_pred_total (Rnd_DN_pt F) -> round_pred_total (Rnd_UP_pt F).
Proof.
intros sym tDN.
intros x.
destruct (tDN (-x)) as [y [Fy [yLx yM]]].
exists (-y); repeat split.
- apply sym; auto.
- lra.
- intros g Fg xLg.
  assert (HH := yM _ (sym _ Fg)).
  lra.
Qed.

Print satisfies_any.

Hypothesis SAF : satisfies_any F.

(*                                                                              
   Prove that DN, UP, ZR are rounding predicates                                
                                                                                
Fact ex8  : round_pred (Rnd_DN_pt F).                                           
Proof.                                                                          
...                                                                             
Qed.                                                                            
                                                                                
Fact ex9  : round_pred (Rnd_UP_pt F).                                           
Proof.                                                                          
...                                                                             
Qed.                                                                            
                                                                                
Fact ex10 : round_pred (Rnd_ZR_pt F).                                           
Proof.                                                                          
...                                                                             
Qed.                                                                            
                                                                                
*)


(******************************************************************************)
(*                         ROUNDING TO THE CLOSEST                            *)
(******************************************************************************)

Check Rnd_N_pt F vx vy.
Eval lazy beta delta [Rnd_N_pt] in Rnd_N_pt F vx vy.

Check Rnd_N.
Eval lazy beta delta [Rnd_N] in Rnd_N F rnd.

(*                                                                              
                                                                                
  Prove that N is idempotent, that is either UP or DOWN and that it is strictly 
  monotone                                                                      
                                                                                
Fact ex11 : forall x, F x -> Rnd_N_pt F x x.                                    
Proof.                                                                          
...                                                                             
Qed.                                                                            
                                                                                
Fact ex12 : forall x f, Rnd_N_pt F x f -> Rnd_DN_pt F x f \/ Rnd_UP_pt F x f.   
Proof.                                                                          
...                                                                             
Qed.                                                                            
                                                                                
Fact ex13 : forall x y f g,                                                     
  Rnd_N_pt F x f -> Rnd_N_pt F y g -> x < y -> f <= g.                          
Proof.                                                                          
...                                                                             
Qed.                                                                            
                                                                                
Hints : some theorems about absolute values                                     
Check Rabs_R0.                                                                  
Check Rabs_pos.                                                                 
Check Rabs_right.                                                               
Check Rabs_left.                                                                
                                                                                
*)
  

Variable T : R -> R -> Prop.                            (* Tie-break rule     *)

Check Rnd_NG_pt F T vx vy.
Eval lazy beta delta [Rnd_NG_pt] in Rnd_NG_pt F T vx vy.

Check NG_existence_prop F T.            (* condition to ensure existance      *)
Eval lazy beta delta [NG_existence_prop] in NG_existence_prop F T.

Search NG_existence_prop.

Check Rnd_NG_pt_unique_prop F T.
Eval lazy beta delta [Rnd_NG_pt_unique_prop] in Rnd_NG_pt_unique_prop F T.

Check Rnd_NG_pt_monotone F T.

Search Rnd_NG_pt_unique_prop.

Definition Taway x f := Rabs f >= Rabs x.


(*                                                                              
  Prove that Taway verifies the two properties to build a rounding mode         
                                                                                

Fact ex14 : NG_existence_prop F Taway.                                          
Proof.                                                                          
...                                                                             
Qed.                                                                            
                                                                                
Fact ex15 : F 0 -> Rnd_NG_pt_unicity_prop F Taway.                              
Proof.                                                                          
...                                                                             
Qed.                                                                            
                                                                                
*)


(*
 Resume                                                                         
                                                                                
 - "generic" version of format and roundind modes                               
 - 4 rounding functions : up, down, to zero, to the nearest.                    
                                                                                
*)

End Lecture2.