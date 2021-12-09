(******************************************************************************)
(*                                                                            *)
(*      LECTURE :  Floating-point numbers and formal proof                    *)
(*                       Laurent.Thery@inria.fr       12/06/2016              *)
(*                                                                            *)
(******************************************************************************)

(*                                                                              
  we present the notion of ulp and the concrete IEEE 754 format                 
*)

Require Import Psatz ZArith Reals SpecFloat.
From Flocq Require Import FTZ Core Operations BinarySingleNaN Binary Bits.

Open Scope R_scope.

Section Lecture4.

(* Variables for our examples *)
Variable vx vy : R.
(* Basis *)
Variable r : radix.
(* Translating funtion for the exponent *)
Variable phi : Z -> Z.
Hypothesis vPhi : Valid_exp phi.
(* Rounding function *)
Variable rnd : R -> Z.
Hypothesis vRound : Valid_rnd rnd.
(* Choice function *)
Variable choice : Z -> bool.

Check ulp r phi vx.

Eval lazy beta delta [ulp] in ulp r phi vx.
Eval lazy beta delta [ulp cexp] in ulp r phi vx.

Check ulp_neq_0.

(*                                                                              
  Prove that if phi is monotone so is ulp                                       
                                                                                
Fact ex1 x y :                                                                  
  x <> 0 -> Monotone_exp phi -> Rabs x <= Rabs y -> ulp r phi x <= ulp r phi y. 
                                                                                
Hints:                                                                          
                                                                                
Check mag_le_abs.                                                           
Check bpow_le.                                                                  
                                                                                
*)

Check round_UP_DN_ulp.

Check round_UP_DN_ulp r phi vx.

(*                                                                              
  Reprove round_UP_DN_ulp                                                       
                                                                                
Fact ext2 x :                                                                   
  ~ generic_format r phi x ->                                                   
  round r phi Zceil x = round r phi Zfloor x + ulp r phi x.                     
                                                                                
Hints:                                                                          
                                                                                
Check scaled_mantissa_mult_bpow.                                                
Check Zceil_floor_neq.                                                          
Check Ztrunc_IZR.                                                               
                                                                                
*)

Check error_lt_ulp.

(*                                                                              
  Reprove error_lt_ulp :                                                        
  Fact ext3 x : x <> 0 -> Rabs (round r phi rnd x - x) < ulp r phi x.           
                                                                                
Hints :                                                                         
                                                                                
Check round_DN_UP_lt.                                                           
Check round_DN_or_UP.                                                           
Check round_UP_DN_ulp.                                                          
                                                                                
*)

Check error_le_half_ulp.

(*                                                                              
  Reprove error_le_half_ulp :                                                   
  Fact ext4 x :                                                                 
    Rabs (round r phi (Znearest choice) x - x) <= / 2 * ulp r phi x.            
                                                                                
Hints:                                                                          
                                                                                
Check round_N_pt.                                                               
Check generic_format_round.                                                     
Check round_DN_UP_lt.                                                           
Check round_DN_or_UP.                                                           
Check round_UP_DN_ulp.                                                          
                                                                                
*)

(* The IEEE 754 norm                                                          *)

(* Simple precision *)
Check binary32.
(* Addition *)
Check b32_plus.

(* Rounding mode *)
Print mode.

(* Double precision *)
Check binary64.
(* Addition *)
Check b64_plus.

(* Two instances of a generic construct *)
Print binary32.
Print binary64.
Check binary_float.


(* Generic float                              *)
(* Variables for the precision and the exponent range *)
Variable vp ve : Z.

(* A float : a sign, a mantissa, an exponent *)
Variable s : bool.
Variable m : positive.
Variable e : Z.
Variable H : bounded vp ve m e = true.

Let f := B754_finite vp ve s m e H.
Check f.
Check is_finite vp ve.
Compute is_finite vp ve f.

(* Checking bound *)
Eval lazy beta zeta iota delta [bounded] in 
  (bounded vp ve m e).

(* Test on the mantissa *)
Check  canonical_canonical_mantissa vp ve s m e.
Print canonical.
Print cexp.

(* Infinity *)

(* + inf *)

Let p_inf := B754_infinity vp ve false.
Check p_inf.

(* - inf *)

Let n_inf := B754_infinity vp ve true.
Check n_inf.

(* Zero *)

(* + zero *)

Let p_z := B754_zero vp ve false.
Check p_z.

(* - zero *)

Let n_z := B754_zero vp ve false.
Check n_z.

(* Nan *)


(* Pay load for Nan *)

Variable pl : positive.
Check nan_pl vp pl.
Eval lazy beta delta [nan_pl] in nan_pl vp pl.
Variable plT : nan_pl vp pl = true.

Let na := B754_nan vp ve s pl plT.

Check is_nan vp ve.
Compute is_nan vp ve.

(* From binary to R *)

Check B2R vp ve f.
Eval lazy beta iota zeta delta [B2R f] in B2R vp ve f.
Eval lazy beta iota zeta delta [B2R f cond_Zopp] in B2R vp ve f.

(* Opposite *)

Check Bopp vp ve.
Eval lazy beta delta [Bopp] in Bopp vp ve.

(* Instantiation for single precision *)
Print b32_opp.

(* Involutive *)
Check Bopp_involutive vp ve.

(* Value *)
Check B2R_Bopp vp ve.

(* Translating rounding modes *)

Check round_mode.
Print round_mode.

(* Addition *)
Check Bplus vp ve.
Eval lazy beta delta [Bplus] in Bplus vp ve.

(* Instantiation for single precision *)
Print b32_plus.
Print  binop_nan_pl32.

Search Bplus.

(* Involutive *)
Check Bplus_correct vp ve.

End Lecture4.