(******************************************************************************)
(*                                                                            *)
(*      LECTURE :  Floating-point numbers and formal proof                    *)
(*                       Laurent.Thery@inria.fr       12/05/2016              *)
(*                                                                            *)
(******************************************************************************)


(*                                                                              
  After having seeen the rounding mode, we are going to see the formats for     
  our floating point numbers. We start from a very generic representation       
*)

Require Import Psatz.
From Flocq Require Import FTZ Core Operations.

Open Scope R_scope.

Axiom todo : forall P, P.
Ltac todo := apply todo.

Section Lecture3.

Check radix.                                                   (* A basis     *)
Print radix.

Definition  radix2 : radix. exists  2%Z. auto. Defined. 
Definition radix10 : radix. exists 10%Z. auto. Defined.

Print Coercion Paths radix Z.
Compute (radix2 + 2)%Z.
 
Check float.
Check float radix2.                                 (* Floating point number as 
                                                       pair of integers       *)
Check float radix10.                               
Print float.

Definition val1 : float radix2  := {| Fnum := 7; Fexp := 1 |}.
Compute Fnum val1.
Compute Fexp val1.

Definition val2 : float radix2  := {| Fnum := 7; Fexp := 0 |}.
Compute Fnum val2.
Compute Fexp val2.

Definition val3 : float radix10 := {| Fnum := 7; Fexp := 10 |}.

Check F2R val1.                                   (* Converting float to real *)
Eval lazy beta delta [F2R] in F2R val1.
Compute F2R val1.
Compute F2R val2.
Compute F2R val3.

Variable r : radix.

(*                                                                              
  Prove that the positivity of a floating point number is the one of its matissa
                                                                                
Fact ex1 : forall (f : float r), (0 <= Fnum f)%Z <->  0 <= F2R f.               
Proof.                                                                          
...                                                                             
Qed.                                                                            
                                                                                
*)

(******************************************************************************)
(*                            OPERATIONS                                      *)
(******************************************************************************)

Check Fopp val1.
Eval lazy beta delta [Fopp] in Fopp val1.
Compute Fopp val1.
Search Fopp.

Check Fabs val1.
Eval lazy beta delta [Fabs] in Fabs val1.
Compute Fabs val1.
Search Fabs.

Check Falign val1 val2.
Eval lazy beta delta [Falign] in Falign val1 val2.
Compute Falign val1 val2.
Search Falign.

Check Fplus val1 val2.
Eval lazy beta delta [Fplus] in Fplus val1 val2.
Compute Fplus val1 val2.
Search Fplus.

Check Fminus val1 val2.
Eval lazy beta delta [Fminus] in Fminus val1 val2.
Compute Fminus val1 val2.
Search Fminus.

Check Fmult val1 val2.
Eval lazy beta delta [Fmult] in Fmult val1 val2.
Compute Fmult val1 val2.
Search Fmult.


(******************************************************************************)
(*                               FORMATS                                      *)
(******************************************************************************)


Variable e : Z.                                 (* Bound on the exponent      *)
Variable p : Z.                                 (* Precision for the mantissa *)
Variables x y : R.                             

(* Format with a fixed exponent                                               *)
Check FIX_format r e x.
Check FIX_spec.

(*                                                                              
  Prove that zero is in the FIX format and that this format is symmetric        
*)             
Fact ex2 : FIX_format r e 0.
Proof.
exists {| Fnum := 0; Fexp := e |}.
- unfold F2R.
  simpl.
  ring.
- simpl.
  trivial.
Qed.

Fact ex3 : FIX_format r e x -> FIX_format r e (- x).
Proof.
intros [f Hf].
exists (Fopp f).
- todo.
- todo.
Qed.

(* Format without bound on the exponent                                       *)
Check FLX_format r p x.
Check FLX_spec.

(*                                                                              
  Prove that zero is in the FLX format and that this format is symmetric        
                                                                                
Fact ex4 : (0 <= p)%Z ->  FLX_format r p 0.                                     
Proof.                                                                          
...                                                                             
Qed.                                                                            
                                                                                
Fact ex5 : FLX_format r p x -> FLX_format r p (- x).                            
Proof.                                                                          
...                                                                             
Qed.                                                                            
                                                                                
*)

(* Format with normalised numbers but without bound on the exponent           *)
Check FLXN_format r p x.
Check FLXN_spec.

(*                                                                              
  Prove that zero is in the FLXN format and that this format is symmetric       
                                                                                
Fact ex6 : FLXN_format r p 0.                                                   
Proof.                                                                          
...                                                                             
Qed.                                                                            
                                                                                
Fact ex7 : FLXN_format r p x -> FLXN_format r p (- x).                          
Proof.                                                                          
...                                                                             
Qed.                                                                            
                                                                                
*)

(* Format with denormalised numbers and with bound on the exponent            *)
Check FLT_format r e p x.
Check FLT_spec.

(*                                                                              
  Prove that zero is in the FLT format and that this format is symmetric        
                                                                                
Fact ex8 : (0 <= p)%Z -> FLT_format r e p 0.                                    
Proof.                                                                          
...                                                                             
Qed.                                                                            
                                                                                
Fact ex9 : FLT_format r e p x -> FLT_format r e p (- x).                        
Proof.                                                                          
...                                                                             
Qed.                                                                            
                                                                                
*)

(* Format without denormalised numbers but with bound on the exponent         *)

Check FTZ_format r e p x.
Check FTZ_spec.

(*                                                                              
  Prove that zero is in the FTZ format and that this format is symmetric        
                                                                                
Fact ex10 : (0 <= p)%Z -> FTZ_format r e p 0.                                   
Proof.                                                                          
...                                                                             
Qed.                                                                            
                                                                                
Fact ex11 : FTZ_format r e p x -> FTZ_format r e p (- x).                       
Proof.                                                                          
...                                                                             
Qed.                                                                            
                                                                                
*)

(******************************************************************************)
(*                 A more algorithmic version                                 *)
(******************************************************************************)

Check bpow radix2 10.
Eval lazy beta delta [bpow] in bpow radix2 10.
Compute bpow radix2 10.

Check (mag r x).          (* An exponent and the proof of the bound  *)
Print mag.

Check mag r x.                 (* The logarithm associated to a real      *)
Print Coercion Paths mag_prop Z.
Check (mag r x + 2)%Z.
Check (bpow_mag_gt r x).       (* lemma for the upper bound               *)

Check archimed.                    (* Archimedian property                    *)
Check Zfloor.                      (* The floor function                      *)
Print Zfloor.
Check Zceil.                       (* The ceiling function                    *)
Print Zceil.
Check Ztrunc.                      (* The truncating function                 *)
Print Ztrunc.

Variable phi : Z -> Z.             (* translating exponent                    *)

Check cexp r phi x.
Eval lazy beta delta [cexp] in cexp r phi x.

Check scaled_mantissa r phi x.
Eval lazy beta delta [scaled_mantissa] in scaled_mantissa r phi x.

Check generic_format r phi x. (* Generic format that depends only on phi      *)
Eval lazy beta delta [generic_format] in generic_format r phi x.
Eval lazy beta delta [generic_format F2R Fnum Fexp] iota in 
   generic_format r phi x.
Eval lazy beta delta [generic_format F2R scaled_mantissa Fnum Fexp] iota in 
   generic_format r phi x.


(*                                                                              
  Prove that the generic format contains zero and is symmetric                  
*)

Fact ex12 : generic_format r phi 0.
Proof.
unfold generic_format, F2R, scaled_mantissa; simpl.
todo.
Qed.

Fact ex13 : forall z,  z <> 0 -> mag r (- z) = mag r z :> Z.
Proof.
Search mag inside Raux.
todo.
Qed.

Fact ex14 : forall z, generic_format r phi z -> generic_format r phi (- z).
Proof.
intros z; unfold generic_format, scaled_mantissa, cexp, F2R; simpl.
todo.
Qed.

(*                                                                              
Hint : we can rely on the following properties of Ztrunc and mag            
                                                                                
Search Ztrunc inside Fcore_Raux.                                           
Search mag inside Fcore_Raux.                                          
                                                                                
*)

(* We can revisit the previous format using the algorithmic version           *)

Variable z : Z.

(* Format with fixed exponent                                                 *)
Check FIX_exp e z.
Eval lazy beta delta [FIX_exp] in FIX_exp e z.

Check generic_format_FIX r e x.
Check FIX_format_generic r e x.

(* Format without bound on the exponent                                       *)
Check FLX_exp p z.
Eval lazy beta delta [FLX_exp] in FLX_exp p z.

Check generic_format_FLX r p x.
Check FLX_format_generic r p x.

(* Format with denormalised numbers and with bound on the exponent            *)
Check FLT_exp e p z.
Eval lazy beta delta [FLT_exp] in FLT_exp e p z.

Check generic_format_FLT r e p x.
Check FLT_format_generic r e p x.

(* Format without denormalised numbers but with a bound on the exponent       *)
Check FTZ_exp e p z.
Eval lazy beta delta [FTZ_exp] in FTZ_exp e p z.

(*                                                                              
  Prove Sterbenz lemma using the only property that phi is monotone             
                                                                                
Fact ex15 :                                                                     
  Monotone_exp phi ->                                                           
  generic_format r phi x -> generic_format r phi y ->                           
  (y / 2 <= x <= 2 * y)%R ->                                                    
  generic_format r phi (x - y)%R.                                               
Proof.                                                                          
...                                                                             
Qed.                                                                            

For this proof, we use the following lemma that gives a simple criterion to     
ensure that a float is in the format                                            
                                                                                
Check generic_format_F2R.                                                       
                                                                                
Here is the informal proof :                                                    
 From (y / 2 <= x <= 2 * y) we deduce that                                      
    - 0 <= y       (1)                                                          
    - 0 <= x       (2)                                                          
    - x - y <= x   (3)                                                          
    - x - y <= y.  (4)                                                          
  generic_format r phi x can be rewritten as                                    
    x = F2R {| Fnum := mx; Fexp := phi (mag r x) |}                         
  generic_format r phi y can be rewritten as                                    
    y = F2R {| Fnum := my, Fexp := phi (mag r y) |}                         
  using Fopp, we can rewrite x - y as                                           
    x - y =                                                                     
     F2R {|Fnum := mz, Fexp := Z.min (phi (mag r x), phi (mag r y) |}   
  so in order to have generic_format r phi (x - y) using  generic_format_F2R,   
  it is sufficient that                                                         
                                                                                
   phi (mag r (x - y)) <= Z.min (phi (mag r x), phi (mag r y))      
                                                                                
  so that                                                                       
                                                                                
     phi (mag r (x - y)) <= phi (mag r x)                               
  and                                                                           
     phi (mag r (x - y)) <= phi (mag r y)                               
                                                                                
  but mag is monotone so is phi, it is then sufficient to prove that        
                                                                                
     x - y <= x                                                                 
  and                                                                           
     x - y <= y                                                                 
                                                                                
  that come from (3) and (4).                                                   
                                                                                
*)


(* We can derive a generic rounding function                                  *)

Variable rnd : R -> Z.                           (* Rounding on the mantissa  *)

Check round r phi rnd x.
Eval lazy beta delta [round] in round r phi rnd x.

Check round r phi Zfloor x.                      (* Rounding down             *)
Eval lazy beta delta [round] in round r phi Zfloor x.

Check round r phi Zceil x.                       (* Rounding up               *)
Eval lazy beta delta [round] in round r phi Zfloor x.

Check round r phi Ztrunc x.                      (* Rounding to zero          *)
Eval lazy beta delta [round] in round r phi Ztrunc x.

Variable choice : Z -> bool.
Check round r phi (Znearest choice) x.
Eval lazy beta delta [round] in round r phi (Znearest choice) x.
Eval lazy beta delta [Znearest] in round r phi (Znearest choice) x.

(* Which conditions on phi for this rounding to have good properties?         *)

Print Valid_exp.
Variable vExp : Valid_exp phi.

Check @generic_format_satisfies_any r phi.
Check @round_DN_pt r phi.
Check @round_UP_pt r phi.
Check @round_ZR_pt r phi.
Check @round_N_pt r phi.

Print Valid_rnd.

Check valid_rnd_DN.
Check valid_rnd_UP.
Check valid_rnd_ZR.
Check valid_rnd_N choice.


(*                                                                              
  Prove that the error resulting of an addition in rounded to the nearest      
  can always be represented exactly                                             
                                                                                
  We first prove a first general result on how a rounded value can be           
  represented                                                                   
                                                                                
  Fact ex16 :                                                                   
    forall (f : float r) rnd, Valid_rnd rnd ->                                  
    exists m',                                                                  
      round r phi rnd (F2R f) =                                                 
      F2R ({| Fnum := m'; Fexp := Fexp f |} : float r).                         
  Proof.                                                                        
  ...                                                                           
  Qed.                                                                          
                                                                                
  Informal proof                                                                
    we can rewrite the rounded value as:                                        
                                                                                
     round r phi rnd (F2R f) =                                                  
       F2R {| Fnum := m; Fexp := phi (mag r (Fexp f)) |}                    
                                                                                
     if phi (mag r (Fexp f)) <= Fexp f                                      
                                                                                
       we can choose m' = (Fnum f)                                              
                                                                                
    if phi (mag r (Fexp f)) > Fexp f                                        
                                                                                
       we can choose m' = m * r ^ (phi (mag r (Fexp f)) - Fexp f).          
                                                                                
  Fact ex17 :                                                                   
    Monotone_exp phi ->                                                         
    generic_format r phi x -> generic_format r phi y ->                         
    generic_format r phi (round r phi (Znearest choice) (x + y) - (x + y))%R.   
  Proof.                                                                        
  ....                                                                          
  Qed.                                                                          
                                                                                
  Informal proof                                                                
                                                                                
  generic_format r phi x can be rewritten as                                    
    x  = F2R {| Fnum := mx; Fexp := phi (mag r x) |}                        
                                                                                
  generic_format r phi y, can be rewritten as                                   
    y  = F2R {| Fnum := my; Fexp := phi (mag r y) |}                        
                                                                                
  without loss of generality we can suppose that                                
        phi (mag r x) <= phi (mag r y)                                  
                                                                                
  so using Fplus we have                                                        
    x + y = F2R {| Fnum := mx +                                                 
                           my * r ^ (phi (mag r y) - phi (mag r x));    
                   Fexp := phi (mag x) |}                                   
                                                                                
  applyin ex16 we get                                                           
    round r phi (Znearest choice) (F2R (x + y)) =                               
            F2R {| Fnum := m; Fexp := phi (mag r x) |}                      
                                                                                
  the definition of Fopp gives                                                  
    round r phi (Znearest choice) (x + y) - (x + y) =                           
       F2R {| Fnum := m - mx + my * r ^ (phi (mag r y) - phi (mag r x));
              Fexp := phi (mag r x) |}                                      
                                                                                
  using  generic_format_F2R, a sufficient condition for this float to be in     
  the format is :                                                               
                                                                                
    phi (mag r (round r phi (Znearest choice) (x + y) - (x + y))) <=        
    phi (mag r x)                                                           
                                                                                
   phi and mag are monotone so it is sufficient that                        
                                                                                
    |round r phi (Znearest choice) (x + y) - (x + y))| <= |x|                   
                                                                                
   so                                                                           
                                                                                
    |round r phi (Znearest choice) (x + y) - (x + y))| <= |y - (x + y)|         
                                                                                
  but y is a float so its distance to x + y must be greater or equal to the one 
  of the rounded value to the nearest of x + y.                                 
                                                                                
*)

End Lecture3.