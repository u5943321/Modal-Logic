open HolKernel Parse boolLib bossLib;
open combinTheory;
open chap1Theory;
open pred_setTheory;
open relationTheory;
open arithmeticTheory;
open set_relationTheory;
open finite_mapTheory;
open chap1Theory;

open folModelsTheory
open folLangTheory


val _ = ParseExtras.tight_equality()

val _ = new_theory "chap2_4revised";

val mm2folm_def = Define`
  mm2folm M = <| Dom := M.frame.world ;
                 Fun := \n args. CHOICE (M.frame.world);
		 Pred := \p zs. 
                            case zs of
                              | [w] => w IN M.frame.world /\ M.valt p w
                              | [w1;w2] => p = 0 ∧ M.frame.rel w1 w2 ∧ 
                                           w1 IN M.frame.world /\ w2 IN M.frame.world
                              |  _ => F 
              |>`;

val expansion_def = Define`
  expansion M0 A M <=> A SUBSET M0.domain /\
                       ?ns f. ns INTER (FDOM M0.consts) = {} /\
		       BIJ f ns A /\
		       FINITE A /\
		       M = M0 with consts := FUNION M0.consts (FUN_FMAP f ns)`;
                       



val _ = overload_on ("fEXISTS", “folLang$Exists”);
val _ = overload_on ("fDISJ", “folLang$Or”);
val _ = overload_on ("fAND", “folLang$And”);
val _ = overload_on ("fNOT", “folLang$Not”);
val _ = overload_on ("fFALSE", “folLang$False”);
val _ = overload_on ("fP", “λp t. Pred p [t]”);
val _ = overload_on ("fR", “λw1 w2. Pred 0 [w1; w2]”);
val _ = overload_on ("fV", “folLang$V”);

Theorem feval_def = holds_def
Theorem fAND_def = And_def
Theorem fDISJ_def = Or_def
Theorem fNOT_def = Not_def



Definition ST_def[simp]:
  (ST x (VAR p) = fP p (fV x)) /\
  (ST x (FALSE) = fFALSE) /\
  (ST x (NOT phi) = fNOT (ST x phi)) /\
  (ST x (DISJ phi psi) = fDISJ (ST x phi) (ST x psi)) /\
  (ST x (DIAM phi) =
     fEXISTS (x + 1) (fAND (fR (fV x) (fV (x + 1))) (ST (x + 1) phi)))
End

Definition fsatis_def:
  fsatis M σ fform <=> valuation M σ ∧ feval M σ fform
End

(*
val _ = overload_on ("feval", ``holds``)
*)


val prop_2_47_i = store_thm(
  "prop_2_47_i",
  ``!M w:'b phi σ x. (IMAGE σ univ(:num)) SUBSET M.frame.world
                       ==> (satis M (σ x) phi <=> fsatis (mm2folm M) σ (ST x phi))``,
  Induct_on `phi` >> rw[] (* 5 *)
  >- (rw[feval_def,ST_def,fsatis_def] >> eq_tac >> rw[] (* 3 *)
     >- (fs[mm2folm_def,valuation_def,IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
     >- (fs[satis_def] >> rw[termval_def] >> fs[mm2folm_def,IN_DEF])
     >- (rw[satis_def] >- (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
                       >- (fs[termval_def] >> fs[mm2folm_def,IN_DEF])))
  >- (rw[satis_def,feval_def,ST_def,fsatis_def] >> metis_tac[])
  >- (rw[satis_def,feval_def,ST_def,fsatis_def])
  >- (rw[satis_def,feval_def,ST_def,fsatis_def] >> eq_tac >> rw[] (* 5 *)
     >- (fs[mm2folm_def,valuation_def,IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
     >- (fs[mm2folm_def,valuation_def,IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
     >- (fs[mm2folm_def,valuation_def,IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
     >- rw[]
     >- (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]))
  >- (rw[satis_def,feval_def,ST_def,fsatis_def] >> eq_tac >> rw[] (* 4 *)
     >- (fs[mm2folm_def,valuation_def,IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
     >- (qexists_tac `v` >> rw[fAND_def,feval_def,APPLY_UPDATE_THM] (* 3 *)
        >- fs[mm2folm_def]
	>- (fs[termval_def,APPLY_UPDATE_THM] >> rw[mm2folm_def])
	>- (`((x + 1 =+ v) σ) (x + 1) = v` by rw[APPLY_UPDATE_THM] >>
           `IMAGE ((x + 1 =+ v) σ) 𝕌(:num) ⊆ M.frame.world`
	   by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x'' = x + 1` (* 2 *)
	      >> rw[APPLY_UPDATE_THM] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
	   `() = u` by fs[] >>
           metis_tac[fsatis_def]))
     >- (fs[SUBSET_DEF,IMAGE_DEF,mm2folm_def] >> metis_tac[])
     >- (qexists_tac `a` >> rw[] (* 3 *)
        >- fs[feval_def,fAND_def,fsatis_def,termval_def,APPLY_UPDATE_THM,mm2folm_def]
	>- fs[mm2folm_def]
	>- (fs[feval_def,fAND_def,fsatis_def] >>
	   `IMAGE ((x + 1 =+ a) σ) 𝕌(:num) ⊆ M.frame.world`
	   by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x'' = x + 1` (* 2 *)
	      >- (rw[APPLY_UPDATE_THM] >> fs[mm2folm_def])
	      >- (rw[APPLY_UPDATE_THM] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])) >>
	   `((x + 1 =+ a) σ) (x + 1) = a` by fs[APPLY_UPDATE_THM] >>
	   `(mm2folm M).Dom = M.frame.world` by fs[mm2folm_def] >>
	   first_x_assum (qspecl_then [`M`,`σ(|x+1|->a|)`,`x+1`] mp_tac) >>
           rw[APPLY_UPDATE_THM]))));



val fFORALL_def = Define`
  fFORALL n ff = fNOT (fEXISTS n (fNOT ff))`;


val prop_2_47_ii = store_thm(
  "prop_2_47_ii",
  ``!phi M. universal_true M phi <=> (!σ. IMAGE σ univ(:num) SUBSET M.frame.world ==> (fsatis (mm2folm M) σ (fFORALL x (ST x phi))))``,
  rw[universal_true_def,fFORALL_def,fsatis_def,feval_def] >> rw[EQ_IMP_THM] (* 3 *)
  >- (fs[mm2folm_def,valuation_def,IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
  >- (`!x'. x' IN (mm2folm M).Dom ==> feval (mm2folm M) ((x =+ x') σ) (ST x phi)` suffices_by metis_tac[] >> rw[] >>
     `fsatis (mm2folm M) ((x =+ x') σ) (ST x phi)` suffices_by metis_tac[fsatis_def] >>
     `x' IN M.frame.world` by fs[mm2folm_def] >>
     `satis M x' phi` by metis_tac[] >>
     `IMAGE ((x =+ x') σ) 𝕌(:num) ⊆ M.frame.world`
         by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x''' = x` >> rw[APPLY_UPDATE_THM] >> fs[SUBSET_DEF,IMAGE_DEF] >> metis_tac[]) >>
     `((x =+ x') σ) x = x'` by fs[APPLY_UPDATE_THM] >> metis_tac[prop_2_47_i])
  >- (`IMAGE (\n.w) 𝕌(:num) ⊆ M.frame.world`
         by (rw[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
     `∀x'.
            x' IN (mm2folm M).Dom ==>
            feval (mm2folm M) ((x =+ x') (\n.w)) (ST x phi)` by metis_tac[] >>
     `w IN (mm2folm M).Dom` by fs[mm2folm_def] >>
     `feval (mm2folm M) ((x =+ w) (λn. w)) (ST x phi)` by metis_tac[] >>
     `IMAGE ((x =+ w) (λn. w)) 𝕌(:num) ⊆ M.frame.world`
         by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x'' = x` >> rw[APPLY_UPDATE_THM]) >>
     `fsatis (mm2folm M) ((x =+ w) (λn. w)) (ST x phi)` by metis_tac[fsatis_def] >>
     `((x =+ w) (λn. w)) x = w` by fs[APPLY_UPDATE_THM] >>
     imp_res_tac prop_2_47_i >> metis_tac[]));
     
  


val ST_alt_def = Define`
  (ST_alt x (VAR p) = fP p (fV x)) /\
  (ST_alt x (FALSE) = fFALSE) /\
  (ST_alt x (NOT phi) = fNOT (ST_alt x phi)) /\
  (ST_alt x (DISJ phi psi) = fDISJ (ST_alt x phi) (ST_alt x psi)) /\
  (ST_alt x (DIAM phi) = fEXISTS (1 - x) (fAND (fR (fV x) (fV (1 - x))) (ST_alt (1 - x) phi)))`;


val prop_2_47_i_alt = store_thm(
  "prop_2_47_i_alt",
  ``!M w:'b phi σ. (IMAGE σ univ(:num)) SUBSET M.frame.world
                       ==> (satis M (σ 1) phi <=> fsatis (mm2folm M) σ (ST_alt 1 phi)) /\
		           (satis M (σ 0) phi <=> fsatis (mm2folm M) σ (ST_alt 0 phi))``,
  Induct_on `phi` >> rw[] (* 10 *)
  >- (rw[feval_def,ST_alt_def,fsatis_def] >> eq_tac >> rw[] (* 3 *)
     >- (fs[mm2folm_def,valuation_def,IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
     >- (rw[mm2folm_def,termval_def] (* 2 *)
        >> metis_tac[satis_def,IN_DEF])
     >- (fs[mm2folm_def,termval_def] >> rw[satis_def] >> metis_tac[IN_DEF]))
  >- (rw[feval_def,ST_alt_def,fsatis_def,mm2folm_def,termval_def] >> eq_tac >> rw[] (* 4 *)
     >- (fs[mm2folm_def,valuation_def,IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
     >- metis_tac[satis_def,IN_DEF]
     >- metis_tac[satis_def,IN_DEF]
     >- (rw[satis_def] >> metis_tac[IN_DEF]))
  >- (fs[satis_def,feval_def,ST_alt_def,fsatis_def,mm2folm_def,termval_def,valuation_def,IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
  >- (fs[satis_def,feval_def,ST_alt_def,fsatis_def,mm2folm_def,termval_def,valuation_def,IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
  >- (fs[satis_def,feval_def,ST_alt_def,fsatis_def,mm2folm_def,termval_def,valuation_def,IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
  >- (fs[satis_def,feval_def,ST_alt_def,fsatis_def,mm2folm_def,termval_def,valuation_def,IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
  >- (rw[satis_def,feval_def,ST_alt_def,fsatis_def] >> eq_tac >> rw[] (* 5 *) >>
     fs[mm2folm_def,valuation_def,IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
  >- (rw[satis_def,feval_def,ST_alt_def,fsatis_def] >> eq_tac >> rw[] (* 5 *) >>
     fs[mm2folm_def,valuation_def,IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
  >- (rw[satis_def,feval_def,ST_alt_def,fsatis_def] >> eq_tac >> rw[] (* 4 *)
     >- (fs[mm2folm_def,valuation_def,IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
     >- (qexists_tac `v` >> rw[fAND_def,feval_def,APPLY_UPDATE_THM] (* 3 *)
        >- (fs[mm2folm_def,valuation_def,IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
	>- rw[mm2folm_def,termval_def,APPLY_UPDATE_THM] 
	>- (fs[fsatis_def] >>
           `((0 =+ v) σ) 0 = v` by rw[APPLY_UPDATE_THM] >>
           `IMAGE ((0 =+ v) σ) 𝕌(:num) ⊆ M.frame.world`
	       by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x' = 0` (* 2 *)
	           >> rw[APPLY_UPDATE_THM] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
	   metis_tac[]))
     >- (fs[SUBSET_DEF,IMAGE_DEF] >> metis_tac[])
     >- (qexists_tac `a` >> rw[] (* 3 *)
        >- fs[feval_def,fAND_def,fsatis_def,mm2folm_def,termval_def,APPLY_UPDATE_THM]
        >- fs[mm2folm_def]
	>- (fs[feval_def,fAND_def,fsatis_def] >>
	   `IMAGE ((0 =+ a) σ) 𝕌(:num) ⊆ M.frame.world`
	   by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x' = 0` (* 2 *)
	      >> rw[APPLY_UPDATE_THM] >> fs[IMAGE_DEF,SUBSET_DEF,mm2folm_def] >> metis_tac[]) >>
	   `((0 =+ a) σ) 0 = a` by fs[APPLY_UPDATE_THM] >>
	   `IMAGE ((0 =+ a) σ) 𝕌(:num) ⊆ (mm2folm M).Dom` by fs[mm2folm_def] >>
	   first_x_assum (qspecl_then [`M`,`σ(|0|->a|)`] mp_tac) >> 
           rw[APPLY_UPDATE_THM])))
  >- (rw[satis_def,feval_def,ST_alt_def,fsatis_def] >> eq_tac >> rw[] (* 4 *)
     >- (fs[mm2folm_def,valuation_def,IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
     >- (qexists_tac `v` >> rw[fAND_def,feval_def,APPLY_UPDATE_THM] (* 3 *)
        >- fs[mm2folm_def]
	>- rw[mm2folm_def,termval_def,APPLY_UPDATE_THM] 
        >- (fs[fsatis_def] >>
           `((1 =+ v) σ) 1= v` by rw[APPLY_UPDATE_THM] >>
           `IMAGE ((1 =+ v) σ) 𝕌(:num) ⊆ M.frame.world`
	       by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x' = 1` (* 2 *)
	          >> rw[APPLY_UPDATE_THM] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
           metis_tac[]))
     >- (fs[SUBSET_DEF,IMAGE_DEF] >> metis_tac[])
     >- (qexists_tac `a` >> rw[] (* 3 *)
        >- fs[feval_def,fAND_def,fsatis_def,mm2folm_def,termval_def,APPLY_UPDATE_THM]
        >- fs[mm2folm_def]
        >- (fs[feval_def,fAND_def,fsatis_def] >>
	   `IMAGE ((1 =+ a) σ) 𝕌(:num) ⊆ M.frame.world`
	   by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x'' = 0` (* 2 *)
	      >> rw[APPLY_UPDATE_THM] >> fs[IMAGE_DEF,SUBSET_DEF,mm2folm_def] >> metis_tac[]) >>
	   `((1 =+ a) σ) 1 = a` by fs[APPLY_UPDATE_THM] >>
	   `IMAGE ((1 =+ a) σ) 𝕌(:num) ⊆ (mm2folm M).Dom` by fs[mm2folm_def] >>
	   first_x_assum (qspecl_then [`M`,`σ(|1|->a|)`] mp_tac) >> 
           rw[APPLY_UPDATE_THM]))));


val ST_alt_two_var = store_thm(
  "ST_alt_two_var",
  ``!phi. FV (ST_alt 0 phi) SUBSET {0;1} /\ FV (ST_alt 1 phi) SUBSET {0;1}``,
  Induct_on `phi` >> rw[] >> fs[ST_alt_def,FV_def,SUBSET_DEF,FVT_def,fDISJ_def,fNOT_def,fAND_def] >> rw[] >> metis_tac[]);





val fequiv_def = Define`
  fequiv (μ:'b itself) ff1 ff2 <=>
  (!M (σ:num -> 'b). (IMAGE σ univ(:num)) SUBSET M.frame.world
                                                        ==> (fsatis (mm2folm M) σ ff1 <=> fsatis (mm2folm M) σ ff2))`;



val ST_ST_alt_fequiv = store_thm(
  "ST_ST_alt_fequiv",
  ``!phi. fequiv μ (ST 0 phi) (ST_alt 0 phi) /\ fequiv μ (ST 1 phi) (ST_alt 1 phi)``,
  rw[ST_alt_def,ST_def,fequiv_def] (* 2 *)
  >- (eq_tac >> rw[] (* 2 *)
     >- (`satis M (σ 0) phi` by metis_tac[prop_2_47_i] >>
        metis_tac[prop_2_47_i_alt])
     >- metis_tac[prop_2_47_i_alt,prop_2_47_i])
  >- metis_tac[prop_2_47_i,prop_2_47_i_alt]);




  
val prop_2_49_i = store_thm(
  "prop_2_49_i",
  ``!phi. ?fphi. (FV fphi) SUBSET {0;1} /\
                 fequiv μ (ST 0 phi) fphi``,
  rw[] >> qexists_tac `(ST_alt 0 phi)` >>
  metis_tac[ST_alt_two_var,ST_ST_alt_fequiv]);

val _ = export_theory();
	          
	    
	 
