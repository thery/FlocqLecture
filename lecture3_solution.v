(******************************************************************************)
(*                                                                            *)
(*      LECTURE :  Floating-point numbers and formal proof                    *)
(*                       Laurent.Thery@inria.fr       12/03/2013              *)
(*                                                                            *)
(******************************************************************************)

(* Solutions of lecture 3 *)

Require Import Psatz ZArith Reals.
From Flocq Require Import FTZ Core Operations.

Open Scope R_scope.

Section Solution3.

Variable r : radix.
Variable e : Z.                                 (* Bound on the exponent      *)
Variable p : Z.                                 (* Precision on the mantissa  *)

(*                                                                              
  Prove that the positivity of a floating point number is the one of its matissa
                                                                                
*)

Fact ex1 : forall (f : float r), (0 <= Fnum f)%Z <->  0 <= F2R f.
Proof.
intros [mf ef]; unfold F2R; simpl; split; intro HH.
- apply Rmult_le_pos.
    apply (IZR_le 0); auto.
    apply bpow_ge_0.
- apply le_IZR; simpl.
  apply (Rmult_le_reg_r (bpow r ef)).
  apply bpow_gt_0.
  lra.
Qed.


(*                                                                              
  Prove that zero is in the FIX format and that this format is symmetric        
*)             
            
Fact ex2 : FIX_format r e 0.
Proof.
exists {| Fnum := 0; Fexp := e |}.
- unfold F2R; simpl; ring.
- auto.
Qed.

Fact ex3 x : FIX_format r e x -> FIX_format r e (- x).
Proof.
intros [f fE fExp].
exists {| Fnum := - Fnum f; Fexp := Fexp f |}.
- rewrite fE; unfold F2R; simpl; rewrite opp_IZR; ring.
- auto.
Qed.

(*                                                                              
  Prove that zero is in the FLX format and that this format is symmetric        
*)
         
Fact ex4 : (0 <= p)%Z ->  FLX_format r p 0.
Proof.
intros Pp; exists {| Fnum := 0; Fexp := 0 |}.
- unfold F2R; simpl; ring.
- apply Zpower_gt_0; auto.
Qed.

Fact ex5 x : FLX_format r p x -> FLX_format r p (- x).
Proof.
intros [f fE fExp].
exists {| Fnum := - Fnum f; Fexp := Fexp f |}.
- rewrite fE; unfold F2R; simpl; rewrite opp_IZR; ring.
- simpl; rewrite Z.abs_opp; auto.
Qed.

(*                                                                              
  Prove that zero is in the FLXN format and that this format is symmetric       
*)

Fact ex6 : FLXN_format r p 0.
Proof.
exists {| Fnum := 0; Fexp := 0 |}.
- unfold F2R; simpl; ring.
- intros HH; destruct HH; auto.
Qed.

Fact ex7 x : FLXN_format r p x -> FLXN_format r p (- x).
Proof.
intros [f fE fM].
exists {| Fnum := - Fnum f; Fexp := Fexp f |}; auto.
- unfold F2R; simpl; rewrite fE, opp_IZR; unfold F2R; ring.
- simpl; intros NxD0; rewrite Z.abs_opp.
  apply fM; lra.
Qed.

(*                                                                              
  Prove that zero is in the FLT format and that this format is symmetric        
*)
            
Fact ex8 : (0 <= p)%Z -> FLT_format r e p 0.
Proof.
intros Ppos.
exists {| Fnum := 0; Fexp := e |}; simpl.
- unfold F2R; simpl; ring.
- apply Zpower_gt_0; auto.
- lia.
Qed.

Fact ex9 x : FLT_format r e p x -> FLT_format r e p (- x).
Proof.
intros [f fE fM fExp].
exists {| Fnum := - Fnum f; Fexp := Fexp f |}; auto.
- unfold F2R; simpl; rewrite opp_IZR, fE; unfold F2R; ring.
- simpl; rewrite Z.abs_opp; auto.
Qed.

(*                                                                              
  Prove that zero is in the FTZ format and that this format is symmetric        
*)          
Fact ex10 : (0 <= p)%Z -> FTZ_format r e p 0.
Proof.
intros Ppos.
exists {| Fnum := 0; Fexp := e |}; simpl.
- unfold F2R; simpl; ring.
- intro HH; destruct HH; auto.
- lia.
Qed.

Fact ex11 x : FTZ_format r e p x -> FTZ_format r e p (- x).
Proof.
intros [f fE fM fExp].
exists {| Fnum := - Fnum f; Fexp := Fexp f |}; simpl; auto.
- rewrite fE; unfold F2R; simpl; rewrite opp_IZR; ring.
- intros H; rewrite Z.abs_opp; auto.
  apply fM; lra.
Qed.

Variable phi : Z -> Z.             (* translating exponent                    *)


(*                                                                              
  Prove that the generic format contains zero and is symmetric                  
*)
Fact ex12 : generic_format r phi 0.
Proof.
unfold generic_format, F2R, scaled_mantissa; simpl.
assert (H : 0 * bpow r (- cexp r phi 0) = 0).
  simpl; ring.
rewrite H, Ztrunc_IZR; simpl; ring.
Qed.

Fact ex13 : forall z,  z <> 0 -> mag r (- z) = mag r z :> Z.
Proof.
intros z zNZ.
apply mag_unique.
rewrite Rabs_Ropp.
destruct (mag r z); auto.
Qed.

Fact ex14 : forall z, generic_format r phi z -> generic_format r phi (- z).
Proof.
intros z Gz.
destruct (Req_dec z 0) as [zZ|zNZ].
 rewrite zZ in *; rewrite Ropp_0; auto.
unfold generic_format, F2R, scaled_mantissa, cexp; simpl.
rewrite ex13; auto.
assert (H :- z * bpow r (- phi (mag r z)) = 
             - (z * bpow r (- phi (mag r z)))) by ring.
rewrite H, Ztrunc_opp, opp_IZR.
unfold generic_format, F2R, scaled_mantissa, cexp in Gz; simpl in Gz.
lra.
Qed.

(*                                                                              
Hint : we can rely on the following properties of Ztrunc and mag            
                                                                                
Search Ztrunc inside Fcore_Raux.                                           
Search mag inside Fcore_Raux.                                          
                                                                                
*)

(*                                                                              
  Prove Sterbenz lemma using the only property that phi is monotone             
*)

Fact ex15 x y :
  Monotone_exp phi ->
  generic_format r phi x -> generic_format r phi y ->
  (y / 2 <= x <= 2 * y)%R ->
  generic_format r phi (x - y)%R.
Proof.
intros mPhi Hx Hy (Hxy1, Hxy2).
destruct (Req_dec (x - y) 0) as [xEy | xNEy].
  rewrite xEy; apply generic_format_0.
unfold generic_format, cexp in Hx, Hy.
assert (Hx1 := bpow_mag_gt r x).
rewrite Rabs_right in Hx1; try lra.
set (ex  := (mag r x) : Z) in *.
set (mx := Ztrunc (_ _ x)) in *.
set (fx := {| Fnum := mx; Fexp := _ |}) in *.
assert (Hy1 := bpow_mag_gt r y).
rewrite Rabs_right in Hy1; try lra.
set (ey := (mag r y) : Z) in *.
set (my := Ztrunc (_ _ y)) in *.
set (fy := {| Fnum := my; Fexp := _ |}) in *.
rewrite Hx, Hy, <- F2R_minus.
assert (Fm := F2R_minus fx fy).
rewrite <-Hx, <-Hy in Fm.
assert (Hxy : Fexp (Fminus fx fy) = Z.min (phi ex) (phi ey)).
  apply Fexp_Fplus.
destruct (Fminus fx fy) as [mxy exy].
apply generic_format_F2R; simpl.
intros _.
rewrite Fm; simpl in Hxy.
unfold cexp.
rewrite Hxy.
destruct (Zmin_spec (phi ex) (phi ey)) as [(H1,H2)|(H1,H2)]; 
  rewrite H2; apply mPhi; apply mag_le_abs; try lra;
  split_Rabs; lra.
Qed.

(*                                                                              
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
    x = F2R {| Fnum = mx, Fexp = phi (mag x) |}                             
  generic_format r phi y can be rewritten as                                    
    y = F2R {| Fnum = my, Fexp = phi (mag y) |}                             
  using Fopp, we can rewrite x - y as                                           
    x - y = F2R {|Fnum = mz, Fexp = Z.min (phi (mag x), phi (mag y) |}  
  so in order to have generic_format r phi (x - y) using  generic_format_F2R,   
  it is sufficient that                                                         
                                                                                
   phi (mag (x - y)) <= Z.min (phi (mag x), phi (mag y))            
                                                                                
  so that                                                                       
                                                                                
     phi (mag (x - y)) <= phi (mag x)                                   
  and                                                                           
     phi (mag (x - y)) <= phi (mag y)                                   
                                                                                
  but mag is monotone so is phi, it is then sufficient to prove that        
                                                                                
     x - y <= x                                                                 
  and                                                                           
     x - y <= y                                                                 
                                                                                
  that come from (3) and (4).                                                   
                                                                                
*)

Variable choice : Z -> bool.
Variable vExp : Valid_exp phi.

(*                                                                              
  Prove that the error resulting of an addition in rounded to the nearest      
  can always be represented exactly                                             
                                                                                
  We first prove a first general result on how a rounded value can be           
  represented                                                                   
*)

Fact ex16 : forall (f : float r) rnd,
  Valid_rnd rnd ->
    exists m',
      round r phi rnd (F2R f) = 
      F2R ({| Fnum := m'; Fexp := Fexp f |} : float r).
Proof.
intros [mx ex] rnd Vrnd.
unfold round, scaled_mantissa.
set (ex' := cexp r phi (F2R {| Fnum := mx; Fexp := ex |})).
unfold F2R; simpl.
destruct (Zle_or_lt ex' ex) as [ex'Lex | exLex'].
  exists mx.
  replace (IZR mx * bpow r ex * bpow r (- ex')) with 
          (IZR (mx * r ^ (ex + - ex'))).
    destruct Vrnd as [_ HH]; rewrite HH.
    rewrite mult_IZR, IZR_Zpower, bpow_plus; try lia.
    rewrite bpow_opp; field.
    assert (HH1 := bpow_gt_0 r ex'); lra.
  rewrite mult_IZR, IZR_Zpower, bpow_plus; try lia; lra.
exists ((rnd (IZR mx * bpow r (ex - ex'))%R) * Zpower r (ex' - ex))%Z.
rewrite mult_IZR, IZR_Zpower; try lia.
replace (IZR mx * bpow r ex * bpow r (- ex')) with 
        (IZR mx * bpow r (ex - ex')).
replace (bpow r ex') with (bpow r (ex + (ex' - ex))).
rewrite bpow_plus; lra.
replace (ex + (ex' - ex))%Z with ex'; try lia; auto.
replace (ex - ex')%Z with (ex + -ex')%Z; try lia; auto.
rewrite bpow_plus; lra.
Qed.

Fact ex17 x y : Monotone_exp phi ->
  generic_format r phi x -> generic_format r phi y ->
  generic_format r phi (round r phi (Znearest choice) (x + y) - (x + y))%R.
Proof.
intros mPhi Hx Hy.
assert (forall x1 y1, 
  (cexp r phi x1 <= cexp r phi y1)%Z ->
  generic_format r phi x1 -> generic_format r phi y1 ->
  generic_format r phi (round r phi (Znearest choice) (x1 + y1) - (x1 + y1))%R).
2 : destruct (Z_le_dec (cexp r phi x) (cexp r phi y)%Z) as [xLy|yLx].
2:  apply H; auto.
2 : replace (x + y) with (y + x); try lra.
2 : apply H; try lia; auto.
clear x y Hx Hy.
intros x y He Hx Hy.
set (rnd := round r phi (Znearest choice)).
destruct (Req_dec (rnd (x + y) - (x + y)) 0) as [xpyZ | xpyNZ].
  rewrite xpyZ.
  apply generic_format_0.
unfold generic_format in Hx, Hy.
set (mx := Ztrunc (_ _ _ x)) in *.
set (ex := cexp _ _ x) in *.
set (my := Ztrunc (_ _ _ y)) in *.
set (ey := cexp _ _ y) in *.
pose (f := {| Fnum := mx + my * r ^ (ey - ex); Fexp := ex |} : float r).
assert (Hxy: (x + y)%R = F2R f).
  rewrite Hx, Hy, <- F2R_plus.
  unfold Fplus; simpl; rewrite Zle_imp_le_bool with (1 := He); auto.
rewrite Hxy.
destruct (ex16 {| Fnum := mx + my * r ^ (ey - ex); Fexp := ex |}
               (Znearest choice) (valid_rnd_N choice)) as [m Hm].
simpl in Hm.
unfold rnd, f; rewrite Hm.
rewrite <-F2R_minus, Fminus_same_exp.
apply generic_format_F2R.
intros HH.
apply mPhi.
apply mag_le_abs.
  apply F2R_neq_0; auto.
replace x with (-(y - (x + y)))%R by ring.
rewrite Rabs_Ropp.
assert (HRN : Rnd_N_pt (generic_format r phi) (x + y)
                       (round r phi (Znearest choice) (x + y))).
  apply round_N_pt; auto.
rewrite <- Fminus_same_exp, F2R_minus, <- Hm. 
fold f; rewrite <- Hxy.
destruct HRN as [_ PN]; auto.
Qed.

(*
  Informal proof                                                                
    we can rewrite the rounded value as:                                        
                                                                                
     round r phi rnd (F2R f) =                                                  
       F2R {| Fnum = m; Fexp := phi (mag (Fexp f)) |}                       
                                                                                
     if phi (mag (Fexp f)) <= Fexp f                                        
                                                                                
       we can choose m' = (Fnum f)                                              
                                                                                
    if phi (mag (Fexp f)) > Fexp f                                          
                                                                                
       we can choose m' = m * r ^ ( phi (mag (Fexp f)) - Fexp f).           
                                                                                
  Fact ex17 :                                                                   
    Monotone_exp phi ->                                                         
    generic_format r phi x -> generic_format r phi y ->                         
    generic_format r phi (round r phi (Znearest choice) (x + y) - (x + y))%R.   
  Proof.                                                                        
  ....                                                                          
  Qed.                                                                          
                                                                                
  Informal proof                                                                
                                                                                
  generic_format r phi x can be rewritten as                                    
    x  = F2R {| Fnum = mx; Fexp = phi (mag x) |}                            
                                                                                
  generic_format r phi y, can be rewritten as                                   
    y  = F2R {| Fnum = my; Fexp = phi (mag y) |}                            
                                                                                
  without loss of generality we can suppose that                                
        phi (mag x) <= phi (mag y)                                      
                                                                                
  so using Fplus we have                                                        
    x + y = F2R {| Fnum := phi (mag xmx +                                   
                                my * r ^ (phi (mag y) - phi (mag x));   
                   Fexp := phi (mag x) |}                                   
                                                                                
  applyin ex16 we get                                                           
    round r phi (Znearest choice) (F2R (x + y)) =                               
            F2R {| Fnum = m; Fexp := phi (mag x) |}                         
                                                                                
  the definition of Fopp gives                                                  
    round r phi (Znearest choice) (x + y) - (x + y) =                           
       F2R {| Fnum = m - mx + my * r ^ (phi (mag y) - phi (mag x));     
              Fexp := phi (mag x) |}                                        
                                                                                
  using  generic_format_F2R, a sufficient condition for this float to be in     
  the format is :                                                               
                                                                                
    phi (mag (round r phi (Znearest choice) (x + y) - (x + y))) <=          
       phi (mag x)                                                          
                                                                                
   phi and mag are monotone so it is sufficient that                        
                                                                                
    |round r phi (Znearest choice) (x + y) - (x + y))| <= |x|                   
                                                                                
   so                                                                           
                                                                                
    |round r phi (Znearest choice) (x + y) - (x + y))| <= |y - (x + y)|         
                                                                                
  but y is a float so its distance to x + y must be greater or equal to the one 
  of the rounded value to the nearest of x + y.                                 
                                                                                
*)

End Solution3.