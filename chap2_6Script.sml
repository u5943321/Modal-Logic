open HolKernel Parse boolLib bossLib;
open chap1Theory;
open pred_setTheory;
open relationTheory;
open arithmeticTheory;
open set_relationTheory;

open chap2_1Theory;
open chap2_2Theory;
open chap2_4revisedTheory;
open chap2_5Theory
open equiv_on_partitionTheory;
open IBCDNFrevisedTheory;
open prim_recTheory;
open listTheory;
open finite_mapTheory;
open combinTheory;

val _ = new_theory "chap2_6";



val ftype_def = Define`
  ftype x G <=> G ⊆ {phi | freevars phi SUBSET {x}}`;

val frealizes_def = Define`
  frealizes M x G <=> ?w. ftype x G /\ w IN M.domain /\
                          !σ phi. (IMAGE σ univ(:num)) SUBSET M.domain /\ phi IN G ==> fsatis M ((x=+w)σ) phi`;



val ok_form_def = Define`ok_form M phi <=> fconsts phi ⊆ FDOM M.consts`


val consistent_def = Define`
  consistent M G <=>
      !G0. FINITE G0 /\ G0 ⊆ G ==> ?σ. IMAGE σ univ(:num) SUBSET M.domain /\ !phi. phi ∈ G0 ==> fsatis M σ phi `;
  
val n_saturated_def = Define`
  n_saturated M n <=>
     !A M' G x.
        FINITE A /\ CARD A <= n /\ A SUBSET M.domain /\
        expansion M A M' /\ G SUBSET { phi | ok_form M' phi} /\
        ftype x G /\ consistent M' G 
         ==>
        frealizes M' x G`;

val countably_saturated_def = Define`
  countably_saturated M <=> !n. n_saturated M n`;



val no_constant_fsatis_lemma = store_thm(
  "no_constant_fsatis_lemma",
  ``!M1 M2. (M1.domain = M2.domain /\
            M1.predsyms = M2.predsyms /\
	    M1.relsyms = M2.relsyms)
            ==> !phi σ. fconsts phi = {} ==>
            fsatis M1 σ phi = fsatis M2 σ phi``,
  strip_tac >> strip_tac >> strip_tac >> 
  Induct_on `phi` >> rw[fsatis_def,feval_def] (* 6 *)
  >- (Cases_on `f` >> rw[] (* 2 *)
     >- (Cases_on `f0` >> rw[] (* 2 *)
        >- fs[interpret_def]
	>- fs[fconsts_def,tconsts_def])
     >- fs[fconsts_def,tconsts_def])
  >- (Cases_on `f` >> rw[] (* 2 *)
     >- fs[interpret_def]
     >- fs[fconsts_def,tconsts_def])
  >- (fs[fconsts_def] >> metis_tac[fsatis_def])
  >- (fs[fconsts_def] >> metis_tac[fsatis_def])
  >- (fs[fconsts_def,fsatis_def] >> rw[EQ_IMP_THM] (* 2 same *)
     >- (qexists_tac `x` >> rw[] >>
        `IMAGE ((n =+ x) σ) 𝕌(:num) ⊆ M1.domain` suffices_by metis_tac[] >>
	rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x'' = n` >> rw[] (* 2 *)
	>- fs[APPLY_UPDATE_THM]
	>- (fs[APPLY_UPDATE_THM,IMAGE_DEF,SUBSET_DEF] >> metis_tac[]))
     >- (qexists_tac `x` >> rw[] >>
        `IMAGE ((n =+ x) σ) 𝕌(:num) ⊆ M1.domain` suffices_by metis_tac[] >>
	rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x'' = n` >> rw[] (* 2 *)
	>- fs[APPLY_UPDATE_THM]
	>- (fs[APPLY_UPDATE_THM,IMAGE_DEF,SUBSET_DEF] >> metis_tac[])))
  >- (fs[fconsts_def] >> Cases_on `f` >> rw[] (* 2 *)
     >- (Cases_on `f0` >> rw[] (* 2 *)
        >- fs[interpret_def]
	>- fs[tconsts_def])
     >- fs[tconsts_def]));





val ST_no_constant = store_thm(
  "ST_no_constant",
  ``!f x u. fconsts (ST x u f) = {}``,
  Induct_on `f` >> rw[ST_def,fconsts_def,tconsts_def] (* 5 *) >>
  `() = u` by fs[] >> fs[fAND_def,fconsts_def,tconsts_def,ST_def]);
  
                      
val ST_one_freevar = store_thm(
  "ST_one_freevar",
  ``!f x u. freevars (ST x u f) SUBSET {x}``,
  Induct_on `f` >> rw[ST_def,freevars_def,fvars_def,tvars_def,fAND_def] >>
  `(freevars (ST (x + 1) () f)) SUBSET {x + 1}` by metis_tac[] >> fs[DELETE_DEF,DIFF_DEF,SUBSET_DEF] >> metis_tac[]);


val diff_form_diff_ST = store_thm(
  "diff_form_diff_ST",
  ``!f1 f2. f1 <> f2 ==> !x u. ST x u f1 <> ST x u f2``,
  Induct_on `f1` >> rw[] (* 5 *)
  >- (Cases_on `f2` >> rw[ST_def])
  >- (Cases_on `f2` >> rw[ST_def] (* 2 *) >>
     `() = u` by fs[] >> metis_tac[])
  >- (Cases_on `f2` >> rw[ST_def] >> Cases_on `f` >> fs[ST_def])
  >- (Cases_on `f2` >> rw[ST_def] >> Cases_on `f1` >> fs[ST_def])
  >- (Cases_on `f2` >> rw[ST_def,fAND_def] >> metis_tac[]));
  
  
val ST_INJ_univ = store_thm(
  "ST_INJ_univ",
  ``∀x u. INJ (ST x u) 𝕌(:α form) 𝕌(:(α, unit) fform)``,
  rw[INJ_DEF] >> metis_tac[diff_form_diff_ST]);


val ST_INJ = store_thm(
  "ST_INJ",
  ``!x u s1 s2. (!f. f IN s1 ==> (ST x u f) IN s2) ==> INJ (ST x u) s1 s2``,
  rw[INJ_DEF] >> metis_tac[diff_form_diff_ST]);


  

val thm_2_65 = store_thm(
  "thm_2_65",
  ``!M. countably_saturated (mm2folm M) ==> M_sat M``,
  rw[countably_saturated_def,n_saturated_def,M_sat_def] >>
  qabbrev_tac `Σ' = {fRrel u (fConst 0) (fVar x)} UNION (IMAGE (ST x u) Σ)` >>
  qabbrev_tac `MA = <| domain := M.frame.world ;
                       consts := FEMPTY |+ (0,w);
                       fnsyms := \x y. ARB;
		       predsyms := \p w. (w IN M.frame.world /\ M.valt p w);
		       relsyms := \ (u:unit) w1 w2. (M.frame.rel w1 w2 /\ w1 IN M.frame.world /\ w2 IN M.frame.world) |>` >>
  `consistent MA Σ'`
      by (rw[consistent_def] >> fs[fin_satisfiable_in_def] >>
         Cases_on `(fRrel () (fConst 0) (fVar x)) IN G0` (* 2 *)
	 >- (`G0 =  (fRrel () (fConst 0) (fVar x)) INSERT (G0 DELETE (fRrel () (fConst 0) (fVar x)))` by metis_tac[INSERT_DELETE] >>
	    `!f. f IN G0 ==> f = fRrel () (fConst 0) (fVar x) \/ f IN (IMAGE (ST x ()) Σ)`
	       by (rpt strip_tac >>
	          `f <> fRrel () (fConst 0) (fVar x) ==> f ∈ IMAGE (ST x ()) Σ` suffices_by metis_tac[] >>
		  strip_tac >>
	          `f IN Σ'` by fs[SUBSET_DEF] >> fs[Abbr`Σ'`] (* 2 *)
	          >- fs[] >- metis_tac[]) >>
            fs[satisfiable_in_def] >>
	    qabbrev_tac `ps = {x' | x' IN Σ /\ ?f. f IN G0 /\ f = ST x () x'}` >>
            `ps SUBSET Σ` by fs[Abbr`ps`,SUBSET_DEF] >>
	    `FINITE ps` 
	        by (`(IMAGE (ST x ()) ps) SUBSET G0`
		       by (fs[Abbr`ps`,SUBSET_DEF] >> metis_tac[]) >>
	           `INJ (ST x ()) ps G0`
	               by (irule ST_INJ >> rw[Abbr`ps`]) >>
		   SPOSE_NOT_THEN ASSUME_TAC >>
		   metis_tac[INFINITE_INJ]) >>
	    `∃x. (x ∈ M.frame.world ∧ M.frame.rel w x) ∧ ∀form. form ∈ ps ⇒ satis M x form` by metis_tac[] >>
	    qexists_tac `\n. x'` >> rw[fsatis_def] (* 3 *)
	    >- (rw[Abbr`MA`] >> rw[IMAGE_DEF,SUBSET_DEF])
	    >- fs[IMAGE_DEF,SUBSET_DEF,Abbr`MA`]
	    >- (`IMAGE (λn. x') 𝕌(:num) ⊆ MA.domain` by (rw[Abbr`MA`] >> rw[IMAGE_DEF,SUBSET_DEF]) >>
	       Cases_on `phi = fRrel () (fConst 0) (fVar x)` (* 2 *)
	       >- (fs[] >> rw[feval_def,interpret_def,Abbr`MA`])
	       >- (`∃t. phi = ST x () t ∧ t ∈ ps`
	               by (`phi IN Σ'` by fs[SUBSET_DEF] >>
		          fs[Abbr`ps`,Abbr`Σ'`]
			  >- fs[] >- metis_tac[]) >>
	          `satis M x' t` by metis_tac[] >>
		  `(λn. x') x = x'` by fs[] >>
		  `() = u` by fs[] >>
		  `IMAGE (λn. x') 𝕌(:num) ⊆ M.frame.world` by fs[Abbr`MA`] >>
		  imp_res_tac prop_2_47_i >>
		  `satis M ((λn. x') x) t` by metis_tac[] >>
                  `fsatis (mm2folm M) (λn. x') (ST x u t)` by fs[] >>
		  `fconsts (ST x u t) = {}` by metis_tac[ST_no_constant] >>
		  `(mm2folm M).domain = MA.domain` by fs[mm2folm_def,Abbr`MA`] >>
		  `(mm2folm M).predsyms = MA.predsyms` by fs[mm2folm_def,Abbr`MA`] >>
		  `(mm2folm M).relsyms = MA.relsyms` by fs[mm2folm_def,Abbr`MA`] >>
		  `fsatis MA (λn. x') phi` by metis_tac[no_constant_fsatis_lemma] >>
		  fs[fsatis_def])))
	  >-  (`!f. f IN G0 ==> f IN (IMAGE (ST x ()) Σ)`
	       by (rpt strip_tac >>
	          `f IN Σ'` by fs[SUBSET_DEF] >> fs[Abbr`Σ'`] (* 2 *)
	          >- fs[] >- metis_tac[]) >>
	       fs[satisfiable_in_def] >>
	       qabbrev_tac `ps = {x' | x' IN Σ /\ ?f. f IN G0 /\ f = ST x () x'}` >>
               `ps SUBSET Σ` by fs[Abbr`ps`,SUBSET_DEF] >>
	       `FINITE ps` 
	           by (`(IMAGE (ST x ()) ps) SUBSET G0`
		           by (fs[Abbr`ps`,SUBSET_DEF] >> metis_tac[]) >>
	               `INJ (ST x ()) ps G0`
	                   by (irule ST_INJ >> rw[Abbr`ps`]) >>
		        SPOSE_NOT_THEN ASSUME_TAC >>
		        metis_tac[INFINITE_INJ]) >>
	       `∃x. (x ∈ M.frame.world ∧ M.frame.rel w x) ∧ ∀form. form ∈ ps ⇒ satis M x form` by metis_tac[] >>
	        qexists_tac `\n. x'` >> rw[fsatis_def] (* 2 *)
		>- (rw[Abbr`MA`] >> rw[IMAGE_DEF,SUBSET_DEF])
		>- fs[IMAGE_DEF,SUBSET_DEF,Abbr`MA`]
		>- (`IMAGE (λn. x') 𝕌(:num) ⊆ MA.domain` by (rw[Abbr`MA`] >> rw[IMAGE_DEF,SUBSET_DEF]) >>
		   `∃t. phi = ST x () t ∧ t ∈ ps`
	               by (`phi IN Σ'` by fs[SUBSET_DEF] >>
		          fs[Abbr`ps`,Abbr`Σ'`]
			  >- fs[] >- metis_tac[]) >>
	          `satis M x' t` by metis_tac[] >>
		  `(λn. x') x = x'` by fs[] >>
		  `() = u` by fs[] >>
		  `IMAGE (λn. x') 𝕌(:num) ⊆ M.frame.world` by fs[Abbr`MA`] >>
		  imp_res_tac prop_2_47_i >>
		  `satis M ((λn. x') x) t` by metis_tac[] >>
                  `fsatis (mm2folm M) (λn. x') (ST x u t)` by fs[] >>
		  `fconsts (ST x u t) = {}` by metis_tac[ST_no_constant] >>
		  `(mm2folm M).domain = MA.domain` by fs[mm2folm_def,Abbr`MA`] >>
		  `(mm2folm M).predsyms = MA.predsyms` by fs[mm2folm_def,Abbr`MA`] >>
		  `(mm2folm M).relsyms = MA.relsyms` by fs[mm2folm_def,Abbr`MA`] >>
		  `fsatis MA (λn. x') phi` by metis_tac[no_constant_fsatis_lemma] >>
		  fs[fsatis_def]))) >>
   `FINITE {w}` by fs[] >>
   `CARD {w} <= 1` by fs[] >>
   `{w} SUBSET (mm2folm M).domain` by fs[SUBSET_DEF,mm2folm_def] >>
   `expansion (mm2folm M) {w} MA`
       by (rw[expansion_def] >> map_every qexists_tac [`{0}`,`\n.w`] >> rw[] (* 3 *)
          >- fs[mm2folm_def]
	  >- fs[BIJ_DEF,INJ_DEF,SURJ_DEF]
	  >- (fs[Abbr`MA`,mm2folm_def] >> rw[fmap_EXT] >> `FINITE {0}` by fs[] >> fs[FUN_FMAP_DEF])) >>
   `Σ' SUBSET {phi |ok_form MA phi}`
       by (rw[SUBSET_DEF,ok_form_def,Abbr`MA`] >>
          fs[Abbr`Σ'`] (* 2 *)
	  >- (`fconsts (fRrel () (fConst 0) (fVar x)) = {0}` by fs[fconsts_def,tconsts_def] >>
	     `fconsts x' = {0}` by metis_tac[] >> fs[])
	  >- (`fconsts (ST x () x''') = {}` by metis_tac[ST_no_constant] >>
	     `fconsts x' = {}` by metis_tac[] >> metis_tac[NOT_IN_EMPTY])) >>
   `ftype x Σ'`
       by (rw[ftype_def,SUBSET_DEF] >> fs[Abbr`Σ'`] (* 2 *)
          >- (`freevars (fRrel () (fConst 0) (fVar x)) = {x}`
	         by rw[freevars_def,tvars_def] >>
	     `x'' IN {x}` by metis_tac[] >> fs[])
	  >- (`freevars (ST x () x''') SUBSET {x}` by metis_tac[ST_one_freevar] >>
	     `x'' IN {x}` by metis_tac[SUBSET_DEF] >> fs[])) >>
   `frealizes MA x Σ'` by metis_tac[] >>
   fs[frealizes_def] >>
   rw[satisfiable_in_def] (* 2 *)
   >- rw[SUBSET_DEF]
   >- (qexists_tac `w'` >> rw[] (* 3 *)
      >- fs[Abbr`MA`]
      >- (`(fRrel () (fConst 0) (fVar x)) IN Σ'` by fs[Abbr`Σ'`] >>
         `IMAGE (\n. w') univ(:num) SUBSET MA.domain`
	     by fs[SUBSET_DEF,IMAGE_DEF,Abbr`MA`,mm2folm_def] >>
	 `fsatis MA ((x =+ w') (λn. w')) (fRrel () (fConst 0) (fVar x))` by metis_tac[] >>
	 fs[fsatis_def,feval_def,APPLY_UPDATE_THM,interpret_def,Abbr`MA`])
      >- (`IMAGE (\n. w') univ(:num) SUBSET MA.domain`
	     by fs[SUBSET_DEF,IMAGE_DEF,Abbr`MA`,mm2folm_def] >>
	 `(ST x () form) IN Σ'` by fs[Abbr`Σ'`] >>
	 `fsatis MA ((x =+ w') (λn. w')) (ST x () form)` by metis_tac[] >>
	 `(IMAGE ((x =+ w') (λn. w')) univ(:num)) SUBSET M.frame.world`
	     by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x'' = x` (* 2 *) >> rw[] >>
	         fs[APPLY_UPDATE_THM,Abbr`MA`]) >>
	 `fconsts (ST x u form) = ∅` by metis_tac[ST_no_constant] >>
	 `fsatis (mm2folm M) ((x =+ w') (λn. w')) (ST x () form)`
	     by (`u = ()` by fs[] >>
	        `(mm2folm M).domain = MA.domain /\ (mm2folm M).predsyms = MA.predsyms /\
		(mm2folm M).relsyms = MA.relsyms` by fs[Abbr`MA`,mm2folm_def] >>
		`IMAGE ((x =+ w') (λn. w')) 𝕌(:num) ⊆ MA.domain` by fs[Abbr`MA`] >>
		metis_tac[no_constant_fsatis_lemma]) >>
	 `(x =+ w') (λn. w') x = w'` by fs[APPLY_UPDATE_THM] >>
	 metis_tac[prop_2_47_i])));


val thm_2_65_corollary = store_thm(
  "thm_2_65_corollary",
  ``∀M M' w:'b w':'c.
       countably_saturated (mm2folm M) /\ countably_saturated (mm2folm M') ∧ w ∈ M.frame.world ∧ w' ∈ M'.frame.world ⇒
       modal_eq M M' w w' ⇒
       bisim_world M M' w w'``,
   rw[] >> `M_sat M /\ M_sat M'` by metis_tac[thm_2_65] >> metis_tac[prop_2_54_DIST_TYPE]);




val _ = export_theory();

