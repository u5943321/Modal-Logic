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
open rich_listTheory;
open finite_mapTheory;
open combinTheory;
open folModelsTheory;
open folLangTheory;


val _ = new_theory "chap2_6";




val ftype_def = Define`
  ftype x G <=> G ⊆ {phi | FV phi SUBSET {x}}`;

val frealizes_def = Define`
  frealizes M x G <=> ?w. ftype x G /\ w IN M.Dom /\
                          !σ phi. (IMAGE σ univ(:num)) SUBSET M.Dom /\ phi IN G ==> fsatis M ((x=+w)σ) phi`;


(*
val ok_form_def = Define`ok_form M phi <=> fconsts phi ⊆ FDOM M.consts`
*)

val expansion_def = Define`
expansion M A M' f <=> (M'.Dom = M.Dom) /\
                        (BIJ f (count (CARD A)) A) /\
                        (M'.Fun = \n args. if n < CARD A /\ args = [] then f n
                                           else CHOICE M.Dom) /\
                        M'.Pred = M.Pred`


val consistent_def = Define`
  consistent M G <=>
      !G0. FINITE G0 /\ G0 ⊆ G ==> ?σ. IMAGE σ univ(:num) SUBSET M.Dom /\ !phi. phi ∈ G0 ==> fsatis M σ phi `;
  
val n_saturated_def = Define`
  n_saturated M n <=>
     !A M' G x f.
        (FINITE A /\ CARD A <= n /\ A SUBSET M.Dom /\
        expansion M A M' f /\ (* G SUBSET { phi | ok_form M' phi} /\ *)
        ftype x G /\ consistent M' G)
         ==>
        frealizes M' x G`;

val countably_saturated_def = Define`
  countably_saturated M <=> !n. n_saturated M n`;


Definition FCT_def[simp]:
  (FCT (V v) = {}) /\
  (FCT (Fn s ts) = if ts = [] then {s} else (LIST_UNION (MAP FCT ts)))
Termination
  WF_REL_TAC `(measure (term_size))` >> rw[term_size_lemma]
End

Definition FC_def[simp]:
  (FC False = {}) /\
  (FC (Pred n ts) = LIST_UNION (MAP FCT ts)) /\
  (FC (IMP f1 f2) = FC f1 ∪ FC f2) /\
  (FC (FALL x f) = FC f)
End


Theorem MAP_LIST_EQ :
  !l f g. (!m. MEM m l ==> f m = g m) ==> MAP f l = MAP g l
Proof
  rw[] >> irule LIST_EQ >> rw[EL_MAP] >> metis_tac[EL_MEM]
QED


Theorem LIST_UNION_EMPTY:
  !l. (LIST_UNION l = {}) <=> (!s. MEM s l ==> s = {})
Proof
  rw[EQ_IMP_THM] 
  >- (SPOSE_NOT_THEN ASSUME_TAC >>
  `?x. x IN s` by metis_tac[MEMBER_NOT_EMPTY] >> 
  `x IN (LIST_UNION l)` by metis_tac[IN_LIST_UNION] >>
  metis_tac[MEMBER_NOT_EMPTY])
  >- (`¬(?s. s IN (LIST_UNION l))` suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
     `!s. MEM s l ==> (!x. x NOTIN s)` by metis_tac[MEMBER_NOT_EMPTY] >> 
     SPOSE_NOT_THEN ASSUME_TAC >> metis_tac[IN_LIST_UNION])
QED

Theorem FC_EMPTY_termval:
  !M1 M2. (M1.Dom = M2.Dom /\
           M1.Pred = M2.Pred /\
           (!n l. l <> [] ==> M1.Fun n l = M2.Fun n l))
            ==> !t σ. FCT t = {} ==>
            termval M1 σ t = termval M2 σ t
Proof
  strip_tac >> strip_tac >> strip_tac >> completeInduct_on `term_size t` >> rw[] >>
  Cases_on `t` >> fs[FCT_def,termval_def] >> Cases_on `l = []` >> fs[] >>
  `(MAP (termval M1 σ) l) = (MAP (termval M2 σ) l)` suffices_by metis_tac[] >>
  irule MAP_LIST_EQ >> rw[] >> Cases_on `m` >> rw[termval_def] >> 
  `term_size (Fn n' l') < 1 + (n + term1_size l)` by fs[term_size_lemma] >>
  first_x_assum (qspec_then `term_size (Fn n' l')` assume_tac) >>
  `1 + (n + term1_size l) = n + (term1_size l + 1)` by fs[] >>
  fs[] >> first_x_assum drule >> rw[] >> 
  first_x_assum (qspec_then `Fn n' l'` assume_tac) >> fs[term_size_def] >> 
  Cases_on `l' = []` 
  >- (fs[] >> `MEM (FCT (Fn n' [])) (MAP (λa. FCT a) l)` by (fs[MEM_MAP] >> 
     qexists_tac `Fn n' []` >> fs[FCT_def]) >>
     `(FCT (Fn n' [])) = {}` by metis_tac[LIST_UNION_EMPTY] >> fs[FCT_def])
  >- (first_x_assum irule >> rw[] >> 
     `MEM (FCT (Fn n' l')) (MAP (λa. FCT a) l)` by (fs[MEM_MAP] >> 
     qexists_tac `Fn n' l'` >> fs[FCT_def]) >>
     `(FCT (Fn n' l')) = {}` by metis_tac[LIST_UNION_EMPTY] >>
     fs[FCT_def] >> Cases_on `l' = []` >> fs[])
QED


Theorem FC_EMPTY_feval:
   !M1 M2. (M1.Dom = M2.Dom /\
            M1.Pred = M2.Pred /\
            (!n l. l <> [] ==> M1.Fun n l = M2.Fun n l))
            ==> !phi σ. FC phi = {} ==>
            feval M1 σ phi = feval M2 σ phi
Proof
  strip_tac >> strip_tac >> strip_tac >> 
  Induct_on `phi` >> rw[fsatis_def,feval_def,valuation_def] >>
  `(MAP (termval M1 σ) l) = (MAP (termval M2 σ) l)` suffices_by metis_tac[] >>
  irule MAP_LIST_EQ >> rw[] >> irule FC_EMPTY_termval >> rw[] >> 
  `MEM (FCT m) (MAP FCT l)` suffices_by metis_tac[LIST_UNION_EMPTY] >>
  fs[MEM_MAP] >> metis_tac[]
QED


Theorem FC_EMPTY_fsatis:
   !M1 M2. (M1.Dom = M2.Dom /\
            M1.Pred = M2.Pred /\
            (!n l. l <> [] ==> M1.Fun n l = M2.Fun n l))
            ==> !phi σ. FC phi = {} ==>
            fsatis M1 σ phi = fsatis M2 σ phi
Proof
  rw[fsatis_def,feval_def,valuation_def] >> metis_tac[FC_EMPTY_feval]
QED

----------
val ST_FC_EMPTY = store_thm(
  "ST_FC_EMPTY",
  ``!f x. FC (ST x f) = {}``,
  cheat);  



  Induct_on `f` >> rw[ST_def,FC_def,FCT_def] (* 3 *) 
  >- fs[FC]

  `() = u` by fs[] >> fs[fAND_def,fconsts_def,tconsts_def,ST_def]);
  
                      
val ST_FV_singleton = store_thm(
  "ST_FV_singleton",
  ``!f x. (FV (ST x f)) SUBSET {x}``,
  cheat);

  Induct_on `f` (* 5 *)
  >- rw[



 rw[ST_def,freevars_def,fvars_def,tvars_def,fAND_def] >>
  `(freevars (ST (x + 1) () f)) SUBSET {x + 1}` by metis_tac[] >> fs[DELETE_DEF,DIFF_DEF,SUBSET_DEF] >> metis_tac[]);

--------------
val diff_form_diff_ST = store_thm(
  "diff_form_diff_ST",
  ``!f1 f2. f1 <> f2 ==> !x. ST x f1 <> ST x f2``,
  cheat);

???????????????

  Induct_on `f1` >> rw[] (* 5 *)
  >- (Cases_on `f2` >> rw[ST_def,fAND_def,fNOT_def,fDISJ_def,Exists_def])
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
  ``!x s1 s2. (!f. f IN s1 ==> (ST x f) IN s2) ==> INJ (ST x) s1 s2``,
  rw[INJ_DEF] >> metis_tac[diff_form_diff_ST]);


  

val thm_2_65 = store_thm(
  "thm_2_65",
  ``!M. countably_saturated (mm2folm M) ==> M_sat M``,
  rw[countably_saturated_def,n_saturated_def,M_sat_def] >>
  qabbrev_tac `Σ' = {fR (Fn 0 []) (fV x)} UNION (IMAGE (ST x) Σ)` >>
  qabbrev_tac `MA = <| Dom := (mm2folm M).Dom;
                       Fun := (λn args. if n = 0 ∧ args = [] then w else CHOICE (mm2folm M).Dom);
                       Pred := (mm2folm M).Pred |>` >>
  `consistent MA Σ'`
      by (rw[consistent_def] >> fs[fin_satisfiable_in_def] >>
         Cases_on `(fR (Fn 0 []) (fV x)) IN G0` (* 2 *)
	 >- (`G0 =  (fR (Fn 0 []) (fV x)) INSERT (G0 DELETE (fR (Fn 0 []) (fV x)))` by metis_tac[INSERT_DELETE] >>
	    `!f. f IN G0 ==> f = fR (Fn 0 []) (fV x) \/ f IN (IMAGE (ST x) Σ)`
	       by (rpt strip_tac >>
	          `f <> fR (Fn 0 []) (fV x) ==> f ∈ IMAGE (ST x) Σ` suffices_by metis_tac[] >>
		  strip_tac >>
	          `f IN Σ'` by fs[SUBSET_DEF] >> fs[Abbr`Σ'`] (* 2 *)
	          >- fs[] >- metis_tac[]) >>
            fs[satisfiable_in_def] >>
	    qabbrev_tac `ps = {x' | x' IN Σ /\ ?f. f IN G0 /\ f = ST x x'}` >>
            `ps SUBSET Σ` by fs[Abbr`ps`,SUBSET_DEF] >>
	    `FINITE ps` 
	        by (`(IMAGE (ST x) ps) SUBSET G0`
		       by (fs[Abbr`ps`,SUBSET_DEF] >> metis_tac[]) >>
	           `INJ (ST x) ps G0`
	               by (irule ST_INJ >> rw[Abbr`ps`]) >>
		   SPOSE_NOT_THEN ASSUME_TAC >>
		   metis_tac[INFINITE_INJ]) >>
	    `∃x. (x ∈ M.frame.world ∧ M.frame.rel w x) ∧ ∀form. form ∈ ps ⇒ satis M x form` by metis_tac[] >>
	    qexists_tac `\n. x'` >> rw[fsatis_def] (* 3 *)
	    >- (rw[Abbr`MA`] >> rw[IMAGE_DEF,SUBSET_DEF,mm2folm_def])
	    >-  fs[IMAGE_DEF,SUBSET_DEF,Abbr`MA`,valuation_def,mm2folm_def]
	    >- (`IMAGE (λn. x') 𝕌(:num) ⊆ MA.Dom` by (rw[Abbr`MA`] >> rw[IMAGE_DEF,SUBSET_DEF,mm2folm_def]) >>
	       Cases_on `phi = fR (Fn 0 []) (fV x)` (* 2 *)
	       >- (fs[] >> rw[feval_def,termval_def,Abbr`MA`,valuation_def,mm2folm_def])
	       >- (`∃t. phi = ST x t ∧ t ∈ ps`
	               by (`phi IN Σ'` by fs[SUBSET_DEF] >>
		          fs[Abbr`ps`,Abbr`Σ'`]
			  >- fs[] >- metis_tac[]) >>
	          `satis M x' t` by metis_tac[] >>
		  `(λn. x') x = x'` by fs[] >>
		  `IMAGE (λn. x') 𝕌(:num) ⊆ M.frame.world` by fs[Abbr`MA`,mm2folm_def] >>
		  imp_res_tac prop_2_47_i >>
		  `satis M ((λn. x') x) t` by metis_tac[] >>
                  `fsatis (mm2folm M) (λn. x') (ST x t)` by fs[] >>
		  `FC (ST x t) = {}` by metis_tac[ST_FC_EMPTY] >>
		  `(mm2folm M).Dom = MA.Dom` by fs[mm2folm_def,Abbr`MA`] >>
		  `(mm2folm M).Pred = MA.Pred` by fs[mm2folm_def,Abbr`MA`] >>
                  `(∀n l. l ≠ [] ⇒ (mm2folm M).Fun n l = MA.Fun n l)`
		      by fs[mm2folm_def,Abbr`MA`] >>
		  `fsatis MA (λn. x') phi` by metis_tac[FC_EMPTY_fsatis] >>
		  fs[fsatis_def])))
	  >-  (`!f. f IN G0 ==> f IN (IMAGE (ST x) Σ)`
	       by (rpt strip_tac >>
	          `f IN Σ'` by fs[SUBSET_DEF] >> fs[Abbr`Σ'`] (* 2 *)
	          >- fs[] >- metis_tac[]) >>
	       fs[satisfiable_in_def] >>
	       qabbrev_tac `ps = {x' | x' IN Σ /\ ?f. f IN G0 /\ f = ST x x'}` >>
               `ps SUBSET Σ` by fs[Abbr`ps`,SUBSET_DEF] >>
	       `FINITE ps` 
	           by (`(IMAGE (ST x) ps) SUBSET G0`
		           by (fs[Abbr`ps`,SUBSET_DEF] >> metis_tac[]) >>
	               `INJ (ST x) ps G0`
	                   by (irule ST_INJ >> rw[Abbr`ps`]) >>
		        SPOSE_NOT_THEN ASSUME_TAC >>
		        metis_tac[INFINITE_INJ]) >>
	       `∃x. (x ∈ M.frame.world ∧ M.frame.rel w x) ∧ ∀form. form ∈ ps ⇒ satis M x form` by metis_tac[] >>
	        qexists_tac `\n. x'` >> rw[fsatis_def] (* 3 *)
		>- (rw[Abbr`MA`] >> rw[IMAGE_DEF,SUBSET_DEF,mm2folm_def]) 
		>- fs[IMAGE_DEF,SUBSET_DEF,Abbr`MA`,valuation_def,mm2folm_def]
		>- (`IMAGE (λn. x') 𝕌(:num) ⊆ MA.Dom` by (rw[Abbr`MA`] >> rw[IMAGE_DEF,SUBSET_DEF,mm2folm_def]) >>
		   `∃t. phi = ST x t ∧ t ∈ ps`
	               by (`phi IN Σ'` by fs[SUBSET_DEF] >>
		          fs[Abbr`ps`,Abbr`Σ'`]
			  >- fs[] >- metis_tac[]) >>
	          `satis M x' t` by metis_tac[] >>
		  `(λn. x') x = x'` by fs[] >>
		  `IMAGE (λn. x') 𝕌(:num) ⊆ M.frame.world` by fs[Abbr`MA`,mm2folm_def] >>
		  imp_res_tac prop_2_47_i >>
		  `satis M ((λn. x') x) t` by metis_tac[] >>
                  `fsatis (mm2folm M) (λn. x') (ST x t)` by fs[] >>
		  `FC (ST x t) = {}` by metis_tac[ST_FC_EMPTY] >>
		  `(mm2folm M).Dom = MA.Dom` by fs[mm2folm_def,Abbr`MA`] >>
		  `(mm2folm M).Pred = MA.Pred` by fs[mm2folm_def,Abbr`MA`] >>
                  `(∀n l. l ≠ [] ⇒ (mm2folm M).Fun n l = MA.Fun n l)`
		     by fs[mm2folm_def,Abbr`MA`] >>
		  `fsatis MA (λn. x') phi` by metis_tac[FC_EMPTY_fsatis] >>
		  fs[fsatis_def]))) >>
   `FINITE {w}` by fs[] >>
   `CARD {w} <= 1` by fs[] >>
   `{w} SUBSET (mm2folm M).Dom` by fs[SUBSET_DEF,mm2folm_def] >>
   `expansion (mm2folm M) {w} MA (\n.w)`
       by (rw[expansion_def] (* 4 *)
            >- fs[mm2folm_def,Abbr`MA`]
            >- fs[BIJ_DEF,INJ_DEF,SURJ_DEF,Abbr`MA`]
            >- (fs[BIJ_DEF,INJ_DEF,SURJ_DEF,Abbr`MA`] >> simp[FUN_EQ_THM]  >> rw[] >>
                fs[])
            >- fs[mm2folm_def,Abbr`MA`]) >>


   `Σ' SUBSET {phi |ok_form MA phi}`
       by (rw[SUBSET_DEF,ok_form_def,Abbr`MA`] >>
          fs[Abbr`Σ'`] (* 2 *)
	  >- (`fconsts (fRrel () (fConst 0) (fVar x)) = {0}` by fs[fconsts_def,tconsts_def] >>
	     `fconsts x' = {0}` by metis_tac[] >> fs[])
	  >- (`fconsts (ST x () x''') = {}` by metis_tac[ST_no_constant] >>
	     `fconsts x' = {}` by metis_tac[] >> metis_tac[NOT_IN_EMPTY])) >>


   `ftype x Σ'`
       by (rw[ftype_def,SUBSET_DEF] >> fs[Abbr`Σ'`] (* 2 *)
          >- (`FV (fR (Fn 0 []) (fV x)) = {x}`
	         by rw[FV_def,FVT_def] >>
	     `x'' IN {x}` by metis_tac[] >> fs[])
	  >- (`FV (ST x x''') SUBSET {x}` by metis_tac[ST_FV_singleton] >>
	     `x'' IN {x}` by metis_tac[SUBSET_DEF] >> fs[])) >>
   `frealizes MA x Σ'` by metis_tac[] >>
   fs[frealizes_def] >>
   rw[satisfiable_in_def] (* 2 *)
   >- rw[SUBSET_DEF]
   >- (qexists_tac `w'` >> rw[] (* 3 *)
      >- fs[Abbr`MA`,mm2folm_def]
      >- (`(fR (Fn 0 []) (fV x)) IN Σ'` by fs[Abbr`Σ'`] >>
         `IMAGE (\n. w') univ(:num) SUBSET MA.Dom`
	     by fs[SUBSET_DEF,IMAGE_DEF,Abbr`MA`,mm2folm_def] >> 
	 `fsatis MA ((x =+ w') (λn. w')) (fR (Fn 0 []) (fV x))` by metis_tac[] >>
	 fs[fsatis_def,feval_def,APPLY_UPDATE_THM,termval_def,Abbr`MA`,mm2folm_def])
      >- (`IMAGE (\n. w') univ(:num) SUBSET MA.Dom`
	     by fs[SUBSET_DEF,IMAGE_DEF,Abbr`MA`,mm2folm_def] >>
	 `(ST x form) IN Σ'` by fs[Abbr`Σ'`] >>
	 `fsatis MA ((x =+ w') (λn. w')) (ST x form)` by metis_tac[] >>
	 `(IMAGE ((x =+ w') (λn. w')) univ(:num)) SUBSET M.frame.world`
	     by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x'' = x` (* 2 *) >> rw[] >>
	         fs[APPLY_UPDATE_THM,Abbr`MA`,mm2folm_def]) >>
	 `FC (ST x form) = ∅` by metis_tac[ST_FC_EMPTY] >>
	 `fsatis (mm2folm M) ((x =+ w') (λn. w')) (ST x form)`
	     by (`(mm2folm M).Dom = MA.Dom /\ (mm2folm M).Pred = MA.Pred /\
		  (∀n l. l ≠ [] ⇒ (mm2folm M).Fun n l = MA.Fun n l)` by fs[Abbr`MA`,mm2folm_def] >>
		 `IMAGE ((x =+ w') (λn. w')) 𝕌(:num) ⊆ MA.Dom` by fs[Abbr`MA`,mm2folm_def] >>
		metis_tac[FC_EMPTY_fsatis]) >>
	 `(x =+ w') (λn. w') x = w'` by fs[APPLY_UPDATE_THM] >>
	 metis_tac[prop_2_47_i])));


val thm_2_65_corollary = store_thm(
  "thm_2_65_corollary",
  ``∀M M' w:'b w':'c.
       countably_saturated (mm2folm M) /\ countably_saturated (mm2folm M') ∧ w ∈ M.frame.world ∧ w' ∈ M'.frame.world ⇒
       modal_eq M M' w w' ⇒
       bisim_world M M' w w'``,
   rw[] >> `M_sat M /\ M_sat M'` by metis_tac[thm_2_65] >> metis_tac[prop_2_54_DIST_TYPE]);



*)
val _ = export_theory();

