(******************************************************************************)
(*                                                                            *)
(*      LECTURE :  Floating-point numbers and formal proof                    *)
(*                       Laurent.Thery@inria.fr       11/21/2016              *)
(*                                                                            *)
(******************************************************************************)


(*
                                                                                
  How to define real numbers?                                                   
                                                                                
  Wikipedia:                                                                    
                                                                                
 The discovery of a suitably rigorous definition of the real numbers            
  — indeed, the realization that a better definition was needed — was one of    
 the most important developments of 19th century mathematics. The currently     
 standard axiomatic definition is that real numbers form the unique Archimedean 
 complete totally ordered field (R,+,·,<), up to isomorphism,[1] whereas popular
 constructive definitions of real numbers include declaring them as equivalence 
 classes of Cauchy sequences of rational numbers, Dedekind cuts, or certain     
 infinite "decimal representations", together with precise interpretations for  
 the arithmetic operations and the order relation. These definitions are        
 equivalent in the realm of classical mathematics.                              
                                                                                
*)


(*                                                                              
  In Coq, real numbers are axiomatised                                          
*)

Require Import Reals.

Section Lecture1.

Check R.
Check Rplus.
Check Rmult.
Check Rgt.

(*
  We want to use the usual notations but the default interpretion is  the one   
  for natural numbers nat                                                       
*)

Check fun x => x + x.

(*  We change the default value                                               *)
Open Scope R_scope.

Check fun x => x + x.

Check fun x => (x + x)%nat.

Check fun x => (x + x)%R.


(******************************************************************************)
(* It is a ring                                                               *)
(******************************************************************************)

Check R.            (* the reals      *)
Check R0.           (*  zero          *)
Check R1.           (*  one           *)
Check Rplus.        (* addition       *)
Check Ropp.         (* opposite       *)
Print Rminus.       (* subtraction    *)
Check Rmult.        (* multiplication *)

(* Addition  4 axioms                                                         *)

Check Rplus_comm.   (* commutativity           *)
Check Rplus_assoc.  (* associativity           *)
Check Rplus_opp_l.  (* right inverse           *)
Check Rplus_0_l.    (* left neutral element    *)

(* We can already derive some facts                                           *)

Fact Rplus_0_r r : r + 0 = r.
Proof.
assert (Rc := Rplus_comm); assert (R0l := Rplus_0_l).
rewrite Rc.
apply R0l.
Qed.

(* Multiplication   4 axioms                                                  *)

Check Rmult_comm.              (* commutativity           *)
Check Rmult_assoc.             (* associativity           *)
Check Rmult_1_l.               (* left neutral element    *)
Check Rmult_plus_distr_l.      (* right distributivity    *)

(* Non triviality  1 axiome                                                   *)

Check R1_neq_R0.

(* The tactic "ring" let us prove equality on this ring                       *)

Fact ex1 x y : x * x - y * y = (x + y) * (x - y).
Proof. ring. Qed.

Fact ex2 : 121 = 11 * 11.
Proof. ring. Qed.


(* Easy exercise 

Fact ex3 : forall x y, (x = y) \/ (x = -y) -> x * x = y * y.
Proof.
....
Qed.

*)


(* About numbers                                                              *)

Check 11.
Check (IZR 11).

Compute IZR 11.

Check 0.
Check (IZR 0).
Compute IZR 0.


(* Turn a natural number into a real number                                   *)
Print INR.

Compute INR 11.
Check plus_INR.

(* Turn a relative number into a real number                                  *)
Print IZR.

Compute IZR (-11).
Check plus_IZR.

(*                                                                              
   Easy exercise:   Prove that INR 42 = 42.                                     
*)

(*                                                                              
   Easy exercise:   Prove that IZR(-42) = -42.                                  
*)

(******************************************************************************)
(* It is a field                                                              *)
(******************************************************************************)

Check Rinv.     (* inverse: Total function !!! *)
Check Rinv_l.   (* right inverse               *)
Print Rdiv.     (* division                    *)

(* field let us prove equalities on a field                                   *)

Fact ex4 x y : x <> 0 -> y <> 0 ->  1 / x + 1 / y = (x + y) / (x * y).
Proof. intros. field. auto. Qed.

Fact ex5 : 121 / 11 = 11.
Proof. intros. field. Qed.

(*                                                                              
   Exercise                                                                     
                                                                                
 Fact ex6 : forall x y, x <> y -> (x * x - y * y) / (x - y) = y + x.            
 Proof.                                                                         
 ....                                                                           
 Qed.                                                                           
                                                                                
   Hint : given a goal                                                          
                                                                                
   H : ~ a                                                                      
   -----------------                                                            
   ~ b                                                                          
                                                                                
   the tactic contradict returns the contrapose of a goal                   
                                                                                
   contradict H                                                                 
                                                                                
   H : b                                                                        
   -----------------                                                            
   a                                                                            
                                                                                
                                                                                
*)

(******************************************************************************)
(* Ordering                                                                   *)
(******************************************************************************)

Check Rlt.                               (* strictly smaller         *)
Print Rgt.                               (* strictly greater         *)
Print Rle.                               (* smaller or equal         *)
Print Rge.                               (* greater or equal         *)

Check Rlt_asym.                          (* antisymmetry             *)
Check Rlt_trans.                         (* transitivity             *)
Check Rplus_lt_compat_l.                 (* left compatibility       *)
                                         (*   with addition          *)
Check Rmult_lt_compat_l.                 (* left compatibility       *)
                                         (*   with multiplication    *)


(* The tactic "lra" let us prove linear inequalities                          *)

Require Import Psatz.

Fact ex7 x :  0 < x -> 2 * x - 1 < 6 * x + 7.
Proof. lra. Qed.

Fact ex8 : 12 / 15 < 37 / 45.
Proof. intros. lra. Qed.

Check total_order_T.                     (* The order is total     *)
Print sumbool.
Print sumor.

(* We can define functions                                                    *)
Definition Rmax2 : R -> R -> R.
intros x y.
destruct (total_order_T x y) as [[xLy |xEy] | xGy].
exact y.
exact x.
exact x.
Defined.

Print Rmax2.

(* We can prove some properties on them                                       *)
Lemma Rmax2_comm x y : Rmax2 x y = Rmax2 y x.
Proof.
unfold Rmax2.
destruct (total_order_T x y) as [[xLy |xEy] | xGy]; 
  destruct (total_order_T y x) as [[yLx |yEx] | yGx]; lra.
Qed.

(*                                                                              
   Exercise : define Rmax3 that takes 3 numbers and returns the greates of      
   three                                                                        
*)

(* We can test equality on real number. Propositional version                 *)
Check Req_dec.

(*                                                                              
   Exercise : Build a computation version of Req_dec                            
*)

(* Integrality of R can be proved                                             *)
Check Rmult_integral.

(*                                                                              
   Exercise :  Reprove integrality without using Rmult_integral                 
*)

Fact ex9 x : x ^ 2 - 2 * x + 1 = 0 <-> x = 1.
Proof.
split; intros H.
  set (V := _ - _ + _) in H.
  assert (H1 : V = (x - 1) * (x - 1)).
    unfold V; ring.
  rewrite H1 in H.
  destruct (Rmult_integral _ _ H); lra.
rewrite H; ring.
Qed.

(* Absolute value                                                             *)

Check Rabs.
Check Rcase_abs.
Print Rabs.

(*                                                                              
   The tactic split_Rabs let us remove the absolute value by generating         
   all the possible cases                                                       
*)

Fact ex10 x y z : Rabs (x - z) <= Rabs (x - y) + Rabs (y - z).
Proof. split_Rabs. lra. lra. lra. lra. lra. lra. lra. lra. Qed.

(*                                                                              
   Exercise :  Prove that (x * x = y * y) is equivalent to  (Rabs x = Rabs y)   
*)

(* Property of being archimedian                                               *)

Check up.         (* an uppper bound                  *)
Check archimed.   (* the characteristic property      *)

(* Completness                                                                 *)

Check is_upper_bound. (* to be an upper bound      *)
Print is_upper_bound.
Check bound.          (* to be bounded             *)
Print bound.
Check is_lub.         (* to be the smallest bound  *)
Print is_lub.
Check completeness.   (* completness               *)


(* From this 24 axioms we can build the usual functions *)

Check IVT.      (* intermediate value theorem          *)
Check cos_plus. (* some trigonometry                   *)

(* Searching in the library                                                   *)

Search sqrt. (* Everything on sqrt *)

Search sqrt (_ * _). (* Everything on sqrt and multiplication *)

Search (0 < _) (_ * _). (* Everything on sqrt and multiplication *)

Search _ (0 < _) (_ * _) outside Fourier_util. (* without fourier *)

SearchPattern (0 < _ * _). (* filtering the conclusion *)

(*                                                                              
 Resume                                                                         
 - we can play formally with the reals                                          
 - two automatic tactics                                                        
      field to prove equalities                                                 
      lra to prove linear inequalities                                          
 - split_Rabs to remove the absolute values                                     
 - set (x := ....) to name a subterm                                            
 - assert (H : ....) to introduce an intermediate result                        
 - Search, SearchPattern to search in the library                          
*)

(*                                                                              
  Exercise,                                                                     
    given two real numbers x and y such that 0 < x < y, show that               
    if A is the arithmetic mean and G the geometric one then we have            
    x < G < A < y                                                               
*)

End Lecture1.

