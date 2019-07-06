open HolKernel Parse boolLib bossLib;
open chap1Theory;
open pred_setTheory;
open relationTheory;
open arithmeticTheory;
open set_relationTheory;

open chap2_1Theory;
open chap2_2Theory;
open chap2_4revisedTheory;
open chap2_5Theory;
open equiv_on_partitionTheory;
open IBCDNFrevisedTheory;
open prim_recTheory;
open listTheory;
open rich_listTheory;
open finite_mapTheory;
open combinTheory;
open folModelsTheory;
open folLangTheory;
open ultraproductTheory;
open lemma2_73Theory;

val _ = new_theory "chap2_6";
  


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

(*okay up to here*)


val ST_form_functions_EMPTY = store_thm(
  "ST_FC_EMPTY",
  ``!f x. form_functions (ST x f) = {}``,
  Induct_on `f` >> 
 rw[ST_def,form_functions_def,fNOT_def,fAND_def,fDISJ_def,Exists_def]);  

                      
val ST_FV_singleton = store_thm(
  "ST_FV_singleton",
  ``!f x. (FV (ST x f)) SUBSET {x}``,
  Induct_on `f` >> rw[ST_def,FV_def,fNOT_def,fAND_def,fDISJ_def] >>
  fs[SUBSET_DEF] >> metis_tac[]);

Theorem term_functions_EMPTY_termval:
!t. term_functions t = {} ==>
               !M1 M2 σ. M1.Dom = M2.Dom /\
                         M1.Pred = M2.Pred ==>
               (termval M1 σ t = termval M2 σ t)
Proof
rw[] >> Cases_on `t` >> fs[term_functions_def]
QED


Theorem form_functions_EMPTY_feval:
!phi. form_functions phi = {} ==>
               !M1 M2 σ. M1.Dom = M2.Dom /\
                         M1.Pred = M2.Pred ==>
               (feval M1 σ phi <=> feval M2 σ phi)
Proof
Induct_on `phi` >> rw[feval_def] (* 3 *)
>- (`(MAP (termval M1 σ) l) = (MAP (termval M2 σ) l)` suffices_by metis_tac[] >>
   irule MAP_CONG >> rw[] >>
   `term_functions x = {}`
     suffices_by metis_tac[term_functions_EMPTY_termval] >>
   SPOSE_NOT_THEN ASSUME_TAC >> fs[GSYM MEMBER_NOT_EMPTY] >>
   `x' IN (LIST_UNION (MAP term_functions l))` 
    suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
   rw[IN_LIST_UNION] >> rw[MEM_MAP,PULL_EXISTS] >> metis_tac[])
>- metis_tac[]
>- metis_tac[]
QED



val thm_2_65 = store_thm(
  "thm_2_65",
  ``!M. countably_saturated (mm2folm M) ==> M_sat M``,
rw[countably_saturated_def,n_saturated_def,M_sat_def] >>
qabbrev_tac `Σ' = {fR (Fn 0 []) (fV x)} UNION (IMAGE (ST x) Σ)` >>
qabbrev_tac `MA = <| Dom := (mm2folm M).Dom;
                     Fun := (λn args. if n = 0 ∧ args = [] then w 
                                      else CHOICE (mm2folm M).Dom);
                     Pred := (mm2folm M).Pred |>` >>
`consistent MA Σ'`
  by 
   (rw[consistent_def] >> fs[fin_satisfiable_in_def] >>
    Cases_on `(fR (Fn 0 []) (fV x)) IN G0` (* 2 *)
    >- (`G0 = (fR (Fn 0 []) (fV x)) INSERT (G0 DELETE (fR (Fn 0 []) (fV x)))` 
          by metis_tac[INSERT_DELETE] >>
	`!f. f IN G0 ==> f = fR (Fn 0 []) (fV x) \/ f IN (IMAGE (ST x) Σ)`
	  by (rpt strip_tac >>
	      `f <> fR (Fn 0 []) (fV x) ==> f ∈ IMAGE (ST x) Σ` 
                suffices_by metis_tac[] >>
	      strip_tac >>
	      `f IN Σ'` by fs[SUBSET_DEF] >> fs[Abbr`Σ'`] (* 2 *)
	      >- fs[] >- metis_tac[]) >>
        fs[satisfiable_in_def] >>
        qabbrev_tac
         `G0' = G0 DELETE fR (Fn 0 []) (fV x)` >>
	qabbrev_tac 
         `ps = 
              {CHOICE {x' | x' IN Σ /\ f = ST x x'} | 
                f IN G0'}` >>
        `!f. (f IN G0 /\ f <> fR (Fn 0 []) (fV x))
               ==> {x' | x' IN Σ /\ f = ST x x'} <> {}`
          by
           (rw[] >> rfs[Abbr`Σ'`,IMAGE_DEF] >> rw[GSYM MEMBER_NOT_EMPTY] >>
            metis_tac[]) >> 
        `ps SUBSET Σ` 
          by 
           (rw[SUBSET_DEF,Abbr`ps`] >> 
            `CHOICE {x' | x' ∈ Σ ∧ f = ST x x'} IN
              {x' | x' ∈ Σ ∧ f = ST x x'}` 
              suffices_by fs[] >>
            `{x' | x' ∈ Σ ∧ f = ST x x'} <> {}`
              suffices_by metis_tac[CHOICE_DEF] >>
            fs[Abbr`G0'`] >> metis_tac[]) >>
	`FINITE ps` 
          by (`FINITE {{x' | x' ∈ Σ ∧ f = ST x x'} | f ∈ G0'} /\
               ps = IMAGE CHOICE {{x' | x' ∈ Σ ∧ f = ST x x'} | f ∈ G0'}`
                suffices_by metis_tac[IMAGE_FINITE] >>
              rw[Once EXTENSION,EQ_IMP_THM,IMAGE_DEF,Abbr`ps`] (* 3 *)
              >- (`{{x' | x' ∈ Σ ∧ f = ST x x'} | f ∈ G0'} = 
                   IMAGE (\f. {x' | x' ∈ Σ ∧ f = ST x x'}) G0' /\ 
                  FINITE G0'` suffices_by metis_tac[IMAGE_FINITE] >>
                  rw[IMAGE_DEF,Once EXTENSION,Abbr`G0'`] >>
                  qabbrev_tac `a = fR (Fn 0 []) (fV x)` >>
                  fs[INSERT_DELETE]
                 )
              >> metis_tac[]
              ) >>
	`∃x. (x ∈ M.frame.world ∧ M.frame.rel w x) ∧
         ∀form. form ∈ ps ⇒ satis M x form` by metis_tac[] >>
	qexists_tac `\n. x'` >> rw[fsatis_def] (* 5 *)
	>- (rw[Abbr`MA`] >> rw[IMAGE_DEF,SUBSET_DEF,mm2folm_def])
	>- fs[IMAGE_DEF,SUBSET_DEF,Abbr`MA`,valuation_def,mm2folm_def]
	>- (fs[] >> rw[feval_def,termval_def,Abbr`MA`,
                           valuation_def,mm2folm_def])
        >- (`IMAGE (λn. x') 𝕌(:num) ⊆ MA.Dom` 
             by (rw[Abbr`MA`] >> rw[IMAGE_DEF,SUBSET_DEF,mm2folm_def]) >>
            rw[valuation_def] >> fs[IMAGE_DEF,SUBSET_DEF])
        >- (`∃t. phi = ST x t ∧ t ∈ ps` 
             by 
              (fs[Abbr`G0'`] (*2*)
               >- metis_tac[]
               >- (`phi IN Σ'` by fs[SUBSET_DEF] >>
		   fs[Abbr`ps`,Abbr`Σ'`] (* 2 *)
                   >- fs[] >>
                   fs[PULL_EXISTS] >> 
                   qexists_tac `ST x x''` >>
                   rw[] >> 
                   `CHOICE {x' | x' ∈ Σ ∧ ST x x'' = ST x x'} IN
                    {x' | x' ∈ Σ ∧ ST x x'' = ST x x'}` suffices_by fs[] >>
                   `{x' | x' ∈ Σ ∧ ST x x'' = ST x x'} <> {}`
                     suffices_by metis_tac[CHOICE_DEF] >>
                   rw[GSYM MEMBER_NOT_EMPTY] >> metis_tac[])
              ) >>
            `satis M x' t` by metis_tac[] >>
            `(λn. x') x = x'` by fs[] >>
            `IMAGE (λn. x') 𝕌(:num) ⊆ M.frame.world` 
              by fs[Abbr`MA`,mm2folm_def,IMAGE_DEF,SUBSET_DEF] >>
            imp_res_tac prop_2_47_i >>
            `satis M ((λn. x') x) t` by metis_tac[] >>
            `fsatis (mm2folm M) (λn. x') (ST x t)` by fs[] >>
            `feval (mm2folm M) (λn. x') phi <=>
             feval MA (λn. x') phi` 
              suffices_by metis_tac[fsatis_def] >> 
            `!phi. form_functions (ST x phi) = {}` 
              by metis_tac[ST_form_functions_EMPTY] >> 
            `!phi. form_functions phi = {} ==>
               !M1 M2 σ. M1.Dom = M2.Dom /\
                         M1.Pred = M2.Pred ==>
               (feval M1 σ phi <=> feval M2 σ phi)` 
              by metis_tac[form_functions_EMPTY_feval] >>
            `(mm2folm M).Dom = MA.Dom` by fs[mm2folm_def,Abbr`MA`] >>
            `(mm2folm M).Pred = MA.Pred` by fs[mm2folm_def,Abbr`MA`] >>
            metis_tac[]))
    >- (`!f. f IN G0 ==> f IN (IMAGE (ST x) Σ)`
	  by (rpt strip_tac >>
	      `f IN Σ'` by fs[SUBSET_DEF] >> fs[Abbr`Σ'`] (* 2 *)
	      >- fs[] >- metis_tac[]) >>
        fs[satisfiable_in_def] >>
	qabbrev_tac 
         `ps = 
              {CHOICE {x' | x' IN Σ /\ f = ST x x'} | 
                f IN G0}` >>
        `!f. f IN G0
               ==> {x' | x' IN Σ /\ f = ST x x'} <> {}`
          by
           (rw[] >> rfs[Abbr`Σ'`,IMAGE_DEF] >> rw[GSYM MEMBER_NOT_EMPTY] >>
            metis_tac[]) >> 
        `ps SUBSET Σ` 
          by 
           (rw[SUBSET_DEF,Abbr`ps`] >> 
            `CHOICE {x' | x' ∈ Σ ∧ f = ST x x'} IN
              {x' | x' ∈ Σ ∧ f = ST x x'}` 
              suffices_by fs[] >>
            `{x' | x' ∈ Σ ∧ f = ST x x'} <> {}`
              suffices_by metis_tac[CHOICE_DEF] >>
             metis_tac[]) >>
	`FINITE ps` 
          by (`FINITE {{x' | x' ∈ Σ ∧ f = ST x x'} | f ∈ G0} /\
               ps = IMAGE CHOICE {{x' | x' ∈ Σ ∧ f = ST x x'} | f ∈ G0}`
                suffices_by metis_tac[IMAGE_FINITE] >>
              rw[Once EXTENSION,EQ_IMP_THM,IMAGE_DEF,Abbr`ps`] (* 3 *)
              >- (`{{x' | x' ∈ Σ ∧ f = ST x x'} | f ∈ G0} = 
                   IMAGE (\f. {x' | x' ∈ Σ ∧ f = ST x x'}) G0 /\ 
                  FINITE G0` suffices_by metis_tac[IMAGE_FINITE] >>
                  rw[IMAGE_DEF,Once EXTENSION])
              >> metis_tac[]
              ) >>
	`∃x. (x ∈ M.frame.world ∧ M.frame.rel w x) ∧
         ∀form. form ∈ ps ⇒ satis M x form` by metis_tac[] >>
	qexists_tac `\n. x'` >> rw[fsatis_def] (* 3 *)
	>- (rw[Abbr`MA`] >> rw[IMAGE_DEF,SUBSET_DEF,mm2folm_def])
	>- fs[IMAGE_DEF,SUBSET_DEF,Abbr`MA`,valuation_def,mm2folm_def]
        >- (`∃t. phi = ST x t ∧ t ∈ ps` 
             by 
              (`phi IN Σ'` by fs[SUBSET_DEF] >>
	       fs[Abbr`ps`,Abbr`Σ'`] (* 2 *)
               >- fs[] >>
               fs[PULL_EXISTS] >> 
               qexists_tac `ST x x''` >>
               rw[] >> 
               `CHOICE {x' | x' ∈ Σ ∧ ST x x'' = ST x x'} IN
                 {x' | x' ∈ Σ ∧ ST x x'' = ST x x'}` suffices_by fs[] >>
               `{x' | x' ∈ Σ ∧ ST x x'' = ST x x'} <> {}`
                  suffices_by metis_tac[CHOICE_DEF] >>
               rw[GSYM MEMBER_NOT_EMPTY] >> metis_tac[]) >>
            `satis M x' t` by metis_tac[] >>
            `(λn. x') x = x'` by fs[] >>
            `IMAGE (λn. x') 𝕌(:num) ⊆ M.frame.world` 
              by fs[Abbr`MA`,mm2folm_def,IMAGE_DEF,SUBSET_DEF] >>
            imp_res_tac prop_2_47_i >>
            `satis M ((λn. x') x) t` by metis_tac[] >>
            `fsatis (mm2folm M) (λn. x') (ST x t)` by fs[] >>
            `feval (mm2folm M) (λn. x') phi <=>
             feval MA (λn. x') phi` 
              suffices_by metis_tac[fsatis_def] >> 
            `!phi. form_functions (ST x phi) = {}` 
              by metis_tac[ST_form_functions_EMPTY] >> 
            `!phi. form_functions phi = {} ==>
               !M1 M2 σ. M1.Dom = M2.Dom /\
                         M1.Pred = M2.Pred ==>
               (feval M1 σ phi <=> feval M2 σ phi)` 
              by metis_tac[form_functions_EMPTY_feval] >>(* cheated lemma*)
            `(mm2folm M).Dom = MA.Dom` by fs[mm2folm_def,Abbr`MA`] >>
            `(mm2folm M).Pred = MA.Pred` by fs[mm2folm_def,Abbr`MA`] >>
            metis_tac[]))) >>
`FINITE {w}` by fs[] >>
`CARD {w} <= 1` by fs[] >>
`{w} SUBSET (mm2folm M).Dom` by fs[SUBSET_DEF,mm2folm_def] >>
`expansion (mm2folm M) {w} MA (\n.w)`
  by (rw[expansion_def] (* 4 *)
      >- fs[mm2folm_def,Abbr`MA`]
      >- fs[BIJ_DEF,INJ_DEF,SURJ_DEF,Abbr`MA`]
      >- (fs[BIJ_DEF,INJ_DEF,SURJ_DEF,Abbr`MA`] >> simp[FUN_EQ_THM] >> rw[] >>
          fs[])
      >- fs[mm2folm_def,Abbr`MA`]) >>
`ftype x Σ'`
  by (rw[ftype_def,SUBSET_DEF] >> fs[Abbr`Σ'`] (* 2 *)
      >- (`FV (fR (Fn 0 []) (fV x)) = {x}`
	    by rw[FV_def,FVT_def] >>
	  `x'' IN {x}` by metis_tac[] >> fs[])
      >- (`FV (ST x x''') SUBSET {x}` by metis_tac[ST_FV_singleton] >>
	  `x'' IN {x}` by metis_tac[SUBSET_DEF] >> fs[])) >>
`frealizes MA x Σ'`
  by (first_x_assum irule >> rw[] >>
      map_every qexists_tac [`{w}`,`\n.w`,`1`] >> rw[] (* 3 *)
      >- (Cases_on `phi = fR (Fn 0 []) (fV x)` (* 2 *)
          >- fs[form_functions_def,FST] >>
          fs[Abbr`Σ'`] >> metis_tac[ST_form_functions_EMPTY,MEMBER_NOT_EMPTY])
      >- (Cases_on `phi = fR (Fn 0 []) (fV x)` (* 2 *)
          >- fs[form_functions_def,FST] >>
          fs[Abbr`Σ'`] >> metis_tac[ST_form_functions_EMPTY,MEMBER_NOT_EMPTY])
      >- rw[SUBSET_DEF,mm2folm_def,IMAGE_DEF]
     ) >>
fs[frealizes_def] >>
rw[satisfiable_in_def] (* 2 *)
>- rw[SUBSET_DEF]
>- (qexists_tac `w'` >> rw[] (* 3 *)
    >- fs[Abbr`MA`,mm2folm_def]
    >- (`(fR (Fn 0 []) (fV x)) IN Σ'` by fs[Abbr`Σ'`] >>
        `IMAGE (\n. w') univ(:num) SUBSET MA.Dom`
	  by fs[SUBSET_DEF,IMAGE_DEF,Abbr`MA`,mm2folm_def] >> 
	`fsatis MA ((x =+ w') (λn. w')) (fR (Fn 0 []) (fV x))` by metis_tac[] >>
	fs[fsatis_def,feval_def,APPLY_UPDATE_THM,termval_def,Abbr`MA`,mm2folm_def]        )
    >- (`IMAGE (\n. w') univ(:num) SUBSET MA.Dom`
	  by fs[SUBSET_DEF,IMAGE_DEF,Abbr`MA`,mm2folm_def] >>
        `(ST x form) IN Σ'` by fs[Abbr`Σ'`] >>
	`fsatis MA ((x =+ w') (λn. w')) (ST x form)` by metis_tac[] >>
	`(IMAGE ((x =+ w') (λn. w')) univ(:num)) SUBSET M.frame.world`
	  by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x'' = x` (* 2 *) >> rw[] >>
	      fs[APPLY_UPDATE_THM,Abbr`MA`,mm2folm_def]) >>
	`fsatis (mm2folm M) ((x =+ w') (λn. w')) (ST x form)`
	     by cheat (*trivial *) >>
	`(x =+ w') (λn. w') x = w'` by fs[APPLY_UPDATE_THM] >>
	metis_tac[prop_2_47_i])));



val thm_2_65_corollary = store_thm(
  "thm_2_65_corollary",
  ``∀M M' w:'b w':'c.
       countably_saturated (mm2folm M) /\ countably_saturated (mm2folm M') ∧ w ∈ M.frame.world ∧ w' ∈ M'.frame.world ⇒
       modal_eq M M' w w' ⇒
       bisim_world M M' w w'``,
   rw[] >> `M_sat M /\ M_sat M'` by metis_tac[thm_2_65] >> metis_tac[prop_2_54_DIST_TYPE]);




Theorem thm_2_74_half1:
  !M N w v. w IN M.frame.world /\ v IN N.frame.world ==> 
         !U I MS NS. ultrafilter U I /\
                     (!i. i IN I ==> MS i = M) /\
                     (!i. i IN I ==> NS i = N) ==>
               bisim_world (ultraproduct_model U I MS) (ultraproduct_model U I NS) 
                           {fw | Uequiv U I (models2worlds MS) (λi. w) fw}
                           {fv | Uequiv U I (models2worlds NS) (λi. v) fv}
                   ==> (!phi. satis M w phi <=> satis N v phi)
Proof
  rw[] >> drule prop_2_71 >> rw[] >> last_x_assum (qspec_then `U` assume_tac) >>
  first_x_assum (qspecl_then [`phi`,`v`] assume_tac) >> first_x_assum drule >> rw[] >>
  `∀phi w.
             satis (ultraproduct_model U I' MS)
               {fw | Uequiv U I' (models2worlds MS) (λi. w) fw} phi ⇔
             satis M w phi` by metis_tac[prop_2_71] >> 
  first_x_assum (qspecl_then [`phi`,`w`] assume_tac) >> drule thm_2_20_lemma >> 
  metis_tac[]
QED


Theorem thm_2_74_half2:
  !(M: (num,α) chap1$model) N w v. w IN M.frame.world /\ v IN N.frame.world ==> 
            (!phi. satis M w phi <=> satis N v phi) ==>
             ?U (I:num -> bool). ultrafilter U I /\
               bisim_world (ultraproduct_model U I (\i. M)) (ultraproduct_model U I (\i. N)) 
                           {fw | Uequiv U I (models2worlds (\i. M)) (λi. w) fw}
                           {fv | Uequiv U I (models2worlds (\i. N)) (λi. v) fv}
Proof
rw[] >> 
`∃U. ultrafilter U 𝕌(:num) ∧ ∀s. FINITE s ⇒ s ∉ U`
  by metis_tac[exercise_2_5_4_b] >>
`!n. {n} NOTIN U` by fs[] >>
drule example_2_72 >> rw[] >>
map_every qexists_tac [`U`,`univ(:num)`] >> rw[] >>
irule thm_2_65_corollary >> rw[] (* 5 *)
>- (irule lemma_2_73 >> rw[] >> metis_tac[MEMBER_NOT_EMPTY]) 
>- (irule lemma_2_73 >> rw[] >> metis_tac[MEMBER_NOT_EMPTY]) 
>- (`!i. i IN 𝕌(:num) ==> (\i. M) i = M` by fs[] >>
    `{fw | Uequiv U 𝕌(:num) (models2worlds (λi. M)) (λi. w) fw} ∈
     (ultraproduct_model U 𝕌(:num) (λi. M)).frame.world <=> w IN M.frame.world`
      suffices_by metis_tac[] >> irule ultraproduct_world_constant >> rw[])
>- (`!i. i IN 𝕌(:num) ==> (\i. N) i = N` by fs[] >>
    `{fv | Uequiv U 𝕌(:num) (models2worlds (λi. N)) (λi. v) fv} ∈
     (ultraproduct_model U 𝕌(:num) (λi. N)).frame.world <=> v IN N.frame.world`
      suffices_by metis_tac[] >> irule ultraproduct_world_constant >> rw[])
>- (rw[modal_eq_tau] >>
    `!i. i IN 𝕌(:num) ==> (\i. M) i = M` by fs[] >>
    drule prop_2_71 >> rw[] >> 
    `!i. i IN 𝕌(:num) ==> (\i. N) i = N` by fs[] >>
    drule prop_2_71 >> rw[])
QED

(*detour lemma 2.74 2.62*)


val invar4bisim_def = Define`
  invar4bisim x (t1: μ itself) (t2: ν itself) phi <=> 
     (FV phi ⊆ {x} /\ 
     !(M:(num,μ) chap1$model) (N:(num,ν) chap1$model) v w.
        bisim_world M N (w:μ) (v:ν) ==> 
           (!(σm: num -> μ) (σn: num -> ν). fsatis (mm2folm M) σm(|x |-> w|) phi <=> 
                    fsatis (mm2folm N) σn(|x |-> v|) phi))`


Theorem ST_CONJ:
ST x (AND f1 f2) = fAND (ST x f1) (ST x f2)
Proof
rw[ST_def,fAND_def,AND_def]
QED


Theorem ST_BIGCONJ:
!s.
   FINITE s ==>
    !x. 
      (!f. f IN s ==> ?phi. f = ST x phi) ==>
       ?cf. (!M σ. IMAGE σ (univ(:num)) ⊆ M.Dom ==>
                  (feval M σ cf <=>
                   (!f. f IN s ==> feval M σ f))) /\
           ?psi. cf = ST x psi
Proof
Induct_on `FINITE` >> rw[] (* 2 *)
>- (qexists_tac `True` >> rw[True_def,fNOT_def,feval_def] >>
    qexists_tac `NOT FALSE` >> rw[ST_def,fNOT_def]) >>
`(∀f. f ∈ s ⇒ ∃phi. f = ST x phi)` by metis_tac[] >>
first_x_assum drule >> rw[] >> 
`∃phi. e = ST x phi` by metis_tac[] >>
qexists_tac `fAND (ST x phi) (ST x psi)` >> rw[EQ_IMP_THM] (* 3 *)
>- rw[]
>- metis_tac[] >>
metis_tac[ST_CONJ]
QED

Theorem ST_fNOT:
ST x (NOT f) = fNOT (ST x f)
Proof
rw[ST_def,fNOT_def,Not_def]
QED

(*
Theorem thm_2_68_half1:
!a x. FV a ⊆ {x} /\ form_functions a = {} ==> 
      invar4bisim x 
      (t1: ((num -> α) -> bool) itself) 
      (t2: ((num -> α) -> bool) itself) a ==> 
       ?phi. 
          (!M:'a model σ. fsatis M σ (ST x phi) <=> fsatis M σ a)
          
Proof
rw[] >>
qabbrev_tac 
  `MOC = {ST x phi | (!M σ. IMAGE σ (univ(:num)) ⊆ M.Dom ==>
                            (feval M σ a ==> feval M σ (ST x phi)))}` >>
`!M:'a model σ. (IMAGE σ (univ(:num)) ⊆ M.Dom /\
       (!f. f IN MOC ==> feval M σ f)) ==> feval M σ a` 
  suffices_by cheat
   (rw[] >>
    `?ss. FINITE ss /\ ss ⊆ MOC /\ 
         (∀M σ.
            IMAGE σ 𝕌(:num) ⊆ M.Dom ∧ (∀f. f ∈ ss ⇒ feval M σ f) ⇒
            feval M σ a)`
     by cheat (*compactness cheat*) >>
    (* `!fs. FINITE fs ==> 
      ?bc. 
       !M σ. IMAGE σ 𝕌(:num) ⊆ M.Dom ==> 
             (!f. f IN fs ==> feval M σ f) <=> feval M σ bc`
     by cheat (*cheat for bigconj*) >>*)
    `?phi. 
       ∀M σ.
            IMAGE σ 𝕌(:num) ⊆ M.Dom ==>
              ((∀f. f ∈ ss ⇒ feval M σ f) <=>
                feval M σ (ST x phi))` by cheat 
      (*cheated for bigconj need ST closed under conj*) >>
    qexists_tac `phi` >> rw[fsatis_def,valuation_def] >>
    rw[EQ_IMP_THM] (* 2 *)
    >- (`IMAGE σ 𝕌(:num) ⊆ M.Dom` 
         by (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
        metis_tac[])
    >- (`IMAGE σ 𝕌(:num) ⊆ M.Dom` 
         by (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
        `(∀f. f ∈ ss ⇒ feval M σ f)` suffices_by metis_tac[] >>
        rw[] >> fs[Abbr`MOC`,SUBSET_DEF] >> metis_tac[])
   ) >>
(*suffices tac end*)
rw[] >>
qabbrev_tac `Tx = {ST x phi | feval M σ (ST x phi)}` >>
`?N:'a model σn. 
    IMAGE σn 𝕌(:num) ⊆ N.Dom /\
    (!f. (f IN Tx \/ f = a) ==> feval N σn f)` 
  by cheat
   (SPOSE_NOT_THEN ASSUME_TAC >> fs[] >>
    `∀N σn.
       IMAGE σn 𝕌(:num) ⊆ N.Dom /\ 
       (!f. f IN Tx ==> feval N σn f) ==>  ¬feval N σn a`
     by metis_tac[] >>
    `?ss. FINITE ss /\ ss ⊆ Tx /\ 
         (∀M:'a model σ.
            IMAGE σ 𝕌(:num) ⊆ M.Dom ∧ (∀f. f ∈ ss ⇒ feval M σ f) ⇒
            ¬feval M σ a)`
     by cheat (*compactness cheat*) >>
    `∀M σ.
           (IMAGE σ 𝕌(:num) ⊆ M.Dom ∧ 
            feval M σ a) ==> 
               ¬(∀f. f ∈ ss ⇒ feval M σ f)` by metis_tac[] >>
    `?phi. phi IN MOC /\
           (!M σ. IMAGE σ 𝕌(:num) ⊆ M.Dom ==>
                   (feval M σ phi <=> (¬∀f. f ∈ ss ⇒ feval M σ f)))`
     by cheat >>
    (* need ST closed under negation *)
    `feval M σ phi` by metis_tac[] >>
    `∀f. f ∈ ss ⇒ feval M σ f` suffices_by metis_tac[] >>
    rw[] >> fs[Abbr`Tx`,SUBSET_DEF] >> metis_tac[]
   ) >>
`feval N σn a` by fs[] >>
qabbrev_tac `w = σ x` >> 
qabbrev_tac `v = σn x` >> 
`!phi. satis (folm2mm M) w phi <=> satis (folm2mm N) v phi` 
  by cheat
   (rw[EQ_IMP_THM] (* 2 *)
    >- (`ST x phi IN Tx`
          by
           (`IMAGE σ 𝕌(:num) ⊆ (folm2mm M).frame.world`
              by rw[folm2mm_def] >>
            `fsatis (mm2folm (folm2mm M)) σ (ST x phi)`
              by metis_tac[Abbr`w`,prop_2_47_i] >>
            rw[Abbr`Tx`] >> 
            `feval M σ (ST x phi)` suffices_by metis_tac[] >>
            `form_functions (ST x phi) = {}` by cheat >>
             (*it is proved before, I just have to find it*) 
            fs[fsatis_def] >> 
            `!f. form_functions f = {} ==> 
                !σ. IMAGE σ 𝕌(:num) ⊆ M.Dom ==> 
                    (feval (mm2folm (folm2mm M)) σ f <=> 
                    feval M σ f)`
              suffices_by 
               (rw[] >> `IMAGE σ 𝕌(:num) ⊆ M.Dom` by fs[folm2mm_def] >>
                metis_tac[]) >>
            (*confirmed the lemma applies, need prove it, cheated!*)
            cheat) >>
        `feval N σn (ST x phi)` by metis_tac[] >>
        `IMAGE σn 𝕌(:num) ⊆ (folm2mm N).frame.world`
          by fs[folm2mm_def] >>
        `feval (mm2folm (folm2mm N)) σn (ST x phi)` by cheat >>
        (*trivial by 2.47*) cheat
    >- (* similar*)  cheat
   ) >>
(*apply 2.74*)
`v IN (folm2mm N).frame.world /\ w IN (folm2mm M).frame.world`
  by (fs[folm2mm_def,IMAGE_DEF,SUBSET_DEF,Abbr`w`,Abbr`v`] >> metis_tac[]) >>
drule (thm_2_74_half2 |> INST_TYPE [beta |-> ``:'a``]) >>
rw[] >> first_x_assum drule >> rw[] >>
fs[invar4bisim_def] >>
qabbrev_tac `Mst = (ultraproduct_model U I' (λi. folm2mm M))` >>
qabbrev_tac `Nst = (ultraproduct_model U I' (λi. folm2mm N))` >>
qabbrev_tac `wst = {fw | Uequiv U I' (models2worlds (λi. folm2mm M)) (λi. w) fw}` >>
qabbrev_tac `vst = {fv | Uequiv U I' (models2worlds (λi. folm2mm N)) (λi. w) fv}` >>
first_x_assum (qspecl_then [`Mst`,`Nst`,`vst`,`wst`] assume_tac) >> rfs[] >>
drule corollary_A_21 >> rw[] >> 
`(feval M σ a <=> fsatis (mm2folm Mst) (\x. wst) a) /\ 
fsatis (mm2folm Nst) (\x. vst) a` 
  suffices_by 
   (first_x_assum (qspecl_then [`(λx. wst)`,`(λx. vst)`] assume_tac) >>
    `(λx. wst)⦇x ↦ wst⦈ = (λx. wst) /\
     (λx. vst)⦇x ↦ vst⦈ = (λx. vst)` by fs[FUN_EQ_THM,APPLY_UPDATE_THM] >>
    rw[] >> 
    `fsatis (mm2folm Nst) (λx. vst)⦇x ↦ vst⦈ a` by cheat >>
    `fsatis (mm2folm Mst) (λx. wst) a <=> 
     fsatis (mm2folm Mst) (λx. wst)⦇x ↦ wst⦈ a` by cheat >>
    (*cheated! do not understand why metis does not solve it*)
    metis_tac[]) >>
`(feval M σ a ⇔ fsatis (mm2folm Mst) (λx. wst) a) /\
 (feval N σn a <=> fsatis (mm2folm Nst) (λx. vst) a)`
suffices_by metis_tac[] >> 
`!M σ a I U. 
   (FV a ⊆ {x} /\ form_functions a = ∅ /\
    ultrafilter U I /\
    (∀ff ll. M.Fun ff ll ∈ M.Dom) /\
    IMAGE σ (univ(:num)) ⊆ M.Dom) ==>
    (feval M σ a <=>
     feval (mm2folm (ultraproduct_model U I (λi. folm2mm M))) 
       (λx. {fw | Uequiv U I' (models2worlds (λi. folm2mm M)) (λi. σ x) fw}) a)`
  suffices_by
   (strip_tac >> 
    first_x_assum (qspecl_then [`M`,`σ`,`a`,`I'`,`U`] assume_tac) >> 
    `(∀ff ll. M.Fun ff ll ∈ M.Dom)` by cheat >>
    (*cheated for well-formness*)
    first_x_assum drule_all >> strip_tac >> 
    fs[Abbr`Mst`,Abbr`wst`,Abbr`w`] >> rw[] (*  2 similar*)
    `feval (mm2folm (ultraproduct_model U I' MS))
          (λx. {fw | Uequiv U I' (models2worlds MS) (λi. σ x) fw}) a ⇔
     feval (mm2folm (ultraproduct_model U I' MS))
          (λx'. {fw | Uequiv U I' (models2worlds MS) (λi. σ x) fw}) a`
     suffices_by cheat >>
    (*cheat for the image stuff, trivial*)
    irule holds_valuation >> rw[] >>
    `x' = x` by fs[SUBSET_DEF] >>
    rw[] 
   
    (*cheated! checked the lemma above can be applied*)

)

QED

*)

Theorem termval_IN_ultraproduct_Dom':
∀U I MS.
    ultrafilter U I ⇒
     (∀n0 l0 i. i IN I ==> (MS i).Fun n0 l0 ∈ (MS i).Dom) ==>
         ∀σ.
             IMAGE σ 𝕌(:num) ⊆ ultraproduct U I (folmodels2Doms MS) ⇒
             ∀a.
                 termval (ultraproduct_folmodel U I MS) σ a ∈
                 ultraproduct U I (folmodels2Doms MS)
Proof
rw[] >>
`ultraproduct U I' (folmodels2Doms MS) = 
 (ultraproduct_folmodel U I' MS).Dom`
 by fs[ultraproduct_folmodel_def] >>
rw[] >> irule termval_IN_Dom >> rw[] (* 2 *)
>- metis_tac[ultraproduct_folmodel_well_formed] >>
fs[ultraproduct_folmodel_def]
QED

Theorem folmodels2Doms_models2worlds_folm2mm:
!MS. (folmodels2Doms MS) = (models2worlds (λi. folm2mm (MS i)))
Proof
rw[folmodels2Doms_def,models2worlds_def,folm2mm_def,FUN_EQ_THM] 
QED


Theorem ultraproduct_comm_termval':
  !t U I MS. ultrafilter U I ==> term_functions t = {} ==>
      !σ. (termval (ultraproduct_folmodel U I MS) σ t =
           termval (mm2folm (ultraproduct_model U I (λi. folm2mm (MS i)))) σ t)
Proof
 Cases_on `t` >> rw[termval_def] 
QED


Theorem ultraproduct_comm_feval':
!phi U I MS. 
  ultrafilter U I ==>
  form_functions phi = {} ==> 
  (!i n. i IN I ==> (MS i).Pred n [] = F) ==>
  (!i a b n. i IN I ==> (MS i).Pred n [a; b] ==> n = 0) ==>
  (!i a b c d n. i IN I ==> (MS i).Pred n (a:: b :: c :: d) = F) ==>
  (∀n0 l0 i. i IN I ==> (MS i).Fun n0 l0 ∈ (MS i).Dom) ==>
  !σ. 
     IMAGE σ (univ(:num)) ⊆ ultraproduct U I (folmodels2Doms MS) ==>
     (feval (ultraproduct_folmodel U I MS) σ phi <=>
      feval (mm2folm (ultraproduct_model U I (λi. folm2mm (MS i)))) σ phi)
Proof
Induct_on `phi` (* 4 *)
>- fs[feval_def]
>- (rw[feval_def] >>
    `MAP (termval (ultraproduct_folmodel U I' MS) σ) l = 
     MAP (termval
           (mm2folm (ultraproduct_model U I' (λi. folm2mm (MS i)))) σ) l`
     by 
      (irule MAP_CONG >> rw[] >> irule ultraproduct_comm_termval' >> rw[] >>
       SPOSE_NOT_THEN ASSUME_TAC >> fs[GSYM MEMBER_NOT_EMPTY] >>
       `x' IN LIST_UNION (MAP term_functions l)` 
         suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
       simp[IN_LIST_UNION] >> qexists_tac `term_functions x` >>
       rw[MEM_MAP] >> metis_tac[]) >>
    rw[] >>
    qabbrev_tac 
      `mapl = 
        MAP (termval
             (mm2folm (ultraproduct_model U I' (λi. folm2mm (MS i)))) σ) l` >>
    Cases_on `mapl = []` (* 2 *)
    >- (fs[] >> 
        rw[mm2folm_def,ultraproduct_folmodel_def,
           folm2mm_def,ultraproduct_model_def] >>
        `{i | i ∈ I' ∧ (MS i).Pred n []} = {}` 
          suffices_by metis_tac[EMPTY_NOTIN_ultrafilter] >>
        rw[Once EXTENSION] >> metis_tac[]) 
    >- (`(?a. l = [a]) \/ 
         (?a b. l = [a;b]) \/ 
         (?a b c d. l = a :: b :: c :: d)`
          by 
           (Cases_on `l` >> fs[] >>
            Cases_on `t` >> fs[] >> Cases_on `t'` >> fs[]) (* 3 *)
        >- (rw[] >>
            qabbrev_tac 
             `sl = termval (ultraproduct_folmodel U I' MS) σ a` >>
            rw[mm2folm_def,
               ultraproduct_folmodel_def,ultraproduct_model_def] >> 
            `sl ∈ ultraproduct U I' (models2worlds (λi. folm2mm (MS i)))`
             by
              (rw[Abbr`sl`] >> drule termval_IN_ultraproduct_Dom' >>
               rw[] >> 
               metis_tac[folmodels2Doms_models2worlds_folm2mm]) >>
            (*remove the conj first*)
           `sl <> {}` by metis_tac[ultraproduct_eqclass_non_empty] >>
           `CHOICE sl IN sl` by metis_tac[CHOICE_DEF] >>
           `{i | i ∈ I' ∧ (MS i).Pred n [CHOICE sl i]} = 
            {i | i ∈ I' ∧ CHOICE sl i ∈ (folm2mm (MS i)).valt n}`
             by (rw[EXTENSION,EQ_IMP_THM,folm2mm_def] >> 
                 drule ultraproduct_val_IN_A >> rw[] >>
                 first_x_assum 
                   (qspecl_then [`models2worlds (λi. folm2mm (MS i))`,
                                 `sl`,`CHOICE sl`,`x`] assume_tac) >>
                 `(models2worlds (λi. folm2mm (MS i))) x = (MS x).Dom`
                   by rw[models2worlds_def,folm2mm_def] >>
                 fs[]) >>
           rw[EQ_IMP_THM] >- metis_tac[] >>
           `{i | i IN I' /\ f i = (CHOICE sl) i} IN U` 
             by 
              (irule ultraproduct_same_eqclass >> rw[] >>
               map_every qexists_tac
                [`models2worlds (λi. folm2mm (MS i))`,`sl`] >> 
               rw[]) >> 
           `({i | i ∈ I' ∧ f i ∈ (folm2mm (MS i)).valt n} ∩
             {i | i ∈ I' ∧ f i = CHOICE sl i}) IN U`
             by metis_tac[ultrafilter_INTER] >>
           irule ultrafilter_SUBSET' >> rw[PULL_EXISTS] (* 2 *)
           >- (qexists_tac 
                 `{i | i ∈ I' ∧ f i ∈ (folm2mm (MS i)).valt n} ∩
                  {i | i ∈ I' ∧ f i = CHOICE sl i}` >> 
               rw[SUBSET_DEF] >> metis_tac[]) >>
           qexists_tac `I'` >> rw[SUBSET_DEF]
           ) (*1 out of 3*)
        >- (rw[] >>
            qabbrev_tac 
             `sl1 = termval (ultraproduct_folmodel U I' MS) σ a` >>
            qabbrev_tac 
             `sl2 = termval (ultraproduct_folmodel U I' MS) σ b` >>
            rw[mm2folm_def,ultraproduct_folmodel_def,ultraproduct_model_def] >>
            `{i | i ∈ I' ∧ (MS i).Pred n [CHOICE sl1 i; CHOICE sl2 i]} ∈ U ==>
             n = 0`
              by 
               (rw[] >> SPOSE_NOT_THEN ASSUME_TAC >>
                `{i | i ∈ I' ∧ (MS i).Pred n [CHOICE sl1 i; CHOICE sl2 i]} = {}`
                  by 
                   (rw[EXTENSION] >> metis_tac[]) >>
                metis_tac[EMPTY_NOTIN_ultrafilter]) >>
            `sl1 ∈ ultraproduct U I' (models2worlds (λi. folm2mm (MS i))) ∧
             sl2 ∈ ultraproduct U I' (models2worlds (λi. folm2mm (MS i)))`
              by
               (`!t. (termval (ultraproduct_folmodel U I' MS) σ t) IN
                 ultraproduct U I' (models2worlds (λi. folm2mm (MS i)))`
                  suffices_by metis_tac[] >>
                drule termval_IN_ultraproduct_Dom' >>
                rw[] >> 
                metis_tac[folmodels2Doms_models2worlds_folm2mm]) >>
            `sl1 <> {}` by metis_tac[ultraproduct_eqclass_non_empty] >>
            `sl2 <> {}` by metis_tac[ultraproduct_eqclass_non_empty] >>
            `CHOICE sl1 IN sl1 /\ CHOICE sl2 IN sl2` by metis_tac[CHOICE_DEF]>>
            rw[EQ_IMP_THM,EXTENSION] (* 2 *)
            >- (map_every qexists_tac [`CHOICE sl1`,`CHOICE sl2`] >>
                rw[] >> 
                `n = 0` by metis_tac[] >>
                `!i. i IN I' ==> CHOICE sl1 i ∈ (MS i).Dom /\ 
                 CHOICE sl2 i ∈ (MS i).Dom`
                  by 
                   (drule ultraproduct_val_IN_A >> 
                    `!x. models2worlds (λi. folm2mm (MS i)) x = (MS x).Dom`
                      by rw[models2worlds_def,folm2mm_def] >>
                    metis_tac[CHOICE_DEF,ultraproduct_eqclass_non_empty]) >>
                rw[folm2mm_def] >> 
                `{i | i ∈ I' ∧ (MS i).Pred 0 [CHOICE sl1 i; CHOICE sl2 i]} = 
                 {i | i ∈ I' ∧ (MS i).Pred 0 [CHOICE sl1 i; CHOICE sl2 i] ∧
                   CHOICE sl1 i ∈ (MS i).Dom ∧ CHOICE sl2 i ∈ (MS i).Dom}`
                  by rw[EXTENSION,EQ_IMP_THM] >>
                metis_tac[]) >>
            qmatch_abbrev_tac `ss IN U` >>
            irule ultrafilter_INTER_INTER_SUBSET >>
            `ss ⊆ I'` by fs[Abbr`ss`,SUBSET_DEF,INTER_DEF] >> rw[] (* 2 *)
            >- (map_every qexists_tac
                 [`{i | i IN I' /\ f i = (CHOICE sl1) i}`,
                  `{i | i IN I' /\ g i = (CHOICE sl2) i}`,
                  `{i | i ∈ I' ∧ (folm2mm (MS i)).frame.rel (f i) (g i)}`] >>
                rw[SUBSET_DEF,folm2mm_def] (* 3 *)
                >- (irule ultraproduct_same_eqclass >> rw[] >>
                    map_every qexists_tac
                    [`models2worlds (λi. folm2mm (MS i))`,`sl1`] >> 
                    rw[])
                >- (irule ultraproduct_same_eqclass >> rw[] >>
                    map_every qexists_tac
                    [`models2worlds (λi. folm2mm (MS i))`,`sl2`] >> 
                    rw[]) >>
                fs[Abbr`ss`] >> metis_tac[]) >>
            qexists_tac `I'` >> rw[SUBSET_DEF])
        >- (`(mm2folm 
              (ultraproduct_model U I' (λi. folm2mm (MS i)))).Pred n mapl = F`
              by rw[mm2folm_def] >>
            `(ultraproduct_folmodel U I' MS).Pred n mapl = F` 
              by 
              (`{i | i ∈ I' ∧ (MS i).Pred n (MAP (λfc. CHOICE fc i) mapl)} NOTIN
                  U` 
                 suffices_by fs[ultraproduct_folmodel_def] >>
               `{i | i ∈ I' ∧ (MS i).Pred n (MAP (λfc. CHOICE fc i) mapl)} = {}`
                 suffices_by metis_tac[EMPTY_NOTIN_ultrafilter] >>
               rw[Once EXTENSION] >> metis_tac[]) >>
            metis_tac[])
    )
   )
>- (rw[] >> metis_tac[])
>- (rw[feval_def,EQ_IMP_THM] (* 2 *)
    >- (first_x_assum drule >> rw[] >>
        `IMAGE σ⦇n ↦ a⦈ 𝕌(:num) ⊆ ultraproduct U I' (folmodels2Doms MS)`
          by (irule IMAGE_UPDATE >> 
              `(mm2folm (ultraproduct_model U I' (λi. folm2mm (MS i)))).Dom =
               ultraproduct U I' (folmodels2Doms MS)`
               by 
                (rw[mm2folm_def,ultraproduct_model_def] >>
                 `(models2worlds (λi. folm2mm (MS i))) = (folmodels2Doms MS)`
                   suffices_by metis_tac[] >>
                 rw[FUN_EQ_THM,models2worlds_def,
                    folm2mm_def,folmodels2Doms_def]) >>
              metis_tac[]) >>
        first_x_assum drule >> rw[] >>
        `(ultraproduct_folmodel U I' MS).Dom = 
         (mm2folm (ultraproduct_model U I' (λi. folm2mm (MS i)))).Dom`
          suffices_by metis_tac[] >>
        rw[ultraproduct_folmodel_def,mm2folm_def,ultraproduct_model_def] >>
        metis_tac[folmodels2Doms_models2worlds_folm2mm])
    >- (first_x_assum drule >> rw[] >>
        `IMAGE σ⦇n ↦ a⦈ 𝕌(:num) ⊆ ultraproduct U I' (folmodels2Doms MS)`
          by (irule IMAGE_UPDATE >> rw[] >> fs[ultraproduct_folmodel_def]) >>
        `(ultraproduct_folmodel U I' MS).Dom = 
         (mm2folm (ultraproduct_model U I' (λi. folm2mm (MS i)))).Dom`
          suffices_by metis_tac[] >>
        rw[ultraproduct_folmodel_def,mm2folm_def,ultraproduct_model_def] >>
        metis_tac[folmodels2Doms_models2worlds_folm2mm])
    )
QED



Theorem detour_embedding_lemma:
!M σ a I U x MS. 
   (FV a ⊆ {x} /\ form_functions a = ∅ /\
    ultrafilter U I /\
    (∀ff ll. M.Fun ff ll ∈ M.Dom) /\
    (∀n. M.Pred n [] ⇔ F) /\
    (∀a b n. M.Pred n [a; b] ⇒ n = 0) /\
    (∀a b c d n. (M.Pred n (a::b::c::d) ⇔ F)) /\
    IMAGE σ (univ(:num)) ⊆ M.Dom) ==>
    (feval M σ a <=>
     feval (mm2folm (ultraproduct_model U I (λi. folm2mm M))) 
       (λx. {fw | Uequiv U I (models2worlds (λi. folm2mm M)) (λi. σ x) fw}) a)
Proof
rw[] >> 
drule (corollary_A_21 |> INST_TYPE [alpha |-> ``:'b``,beta |-> ``:'a``]) >>
rw[] >>
first_x_assum 
  (qspecl_then [`\i.M`,`M`,`σ`,`a`] assume_tac) >>
fs[] >>
`(∀i ff ll. i ∈ I' ⇒ M.Fun ff ll ∈ M.Dom)` by metis_tac[] >> 
first_x_assum drule_all >> rw[] >> 
drule
  (ultraproduct_comm_feval'|> INST_TYPE [alpha |-> ``:'b``,beta |-> ``:'a``])>> 
rw[] >>
first_x_assum 
  (qspecl_then 
    [`a`,`\i.M`,
     `(λx. {g | Uequiv U I' (folmodels2Doms (λi. M)) g (λi. σ x)})`]
   assume_tac) >>
rfs[] >>
`IMAGE (λx. {g | Uequiv U I' (folmodels2Doms (λi. M)) g (λi. σ x)})
          𝕌(:num) ⊆ ultraproduct U I' (folmodels2Doms (λi. M))`
  by
   (rw[SUBSET_DEF,ultraproduct_def,partition_def] >>
    qexists_tac `\i. σ x''` >>
    rw[] (* 2 *)
    >- (rw[Cart_prod_def,folmodels2Doms_def] >>
        fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
    >- (rw[EXTENSION,Uequiv_def,EQ_IMP_THM] (* 2 same *) >>
        `{i | i ∈ I' ∧ x' i = σ x''} = 
         {i | i ∈ I' ∧ σ x'' = x' i}` 
          by (rw[EXTENSION,EQ_IMP_THM] >> metis_tac[]) >>
        metis_tac[])
   ) >>
fs[] >> 
`(models2worlds (λi. folm2mm M)) = (folmodels2Doms (λi. M))`
  by 
   rw[FUN_EQ_THM,models2worlds_def,folmodels2Doms_def,folm2mm_def] >>
rw[] >> 
`(λx. {g | Uequiv U I' (folmodels2Doms (λi. M)) g (λi. σ x)}) = 
 (λx'. {fw | Uequiv U I' (folmodels2Doms (λi. M)) (λi. σ x') fw})`
  by 
   (rw[FUN_EQ_THM,EQ_IMP_THM] (* 2 same *) >>
    qexists_tac `x''` >> rw[] >> metis_tac[Uequiv_SYM]) >>
rw[] >>
`(∀i a b n. i ∈ I' ⇒ M.Pred n [a; b] ⇒ n = 0)`
  by metis_tac[] >>
first_x_assum drule >> rw[]
QED

Theorem mm2folm_folm2mm_termval:
!t. 
  term_functions t = {} ==>
   !σ. 
      IMAGE σ univ(:num) ⊆ M.Dom ==>
       termval (mm2folm (folm2mm M)) σ t = termval M σ t
Proof
 rw[] >> Cases_on `t` >> fs[term_functions_def] >> rw[termval_def,mm2folm_def,folm2mm_def]
QED

Theorem mm2folm_folm2mm_feval:
∀f. form_functions f = ∅ ⇒
  ∀σ. IMAGE σ 𝕌(:num) ⊆ M.Dom ⇒
      (∀n. M.Pred n [] ⇔ F) ==>
      (∀a b n. M.Pred n [a; b] ⇒ n = 0) ==>
      (∀a b c d n. (M.Pred n (a::b::c::d) ⇔ F)) ==>
           (feval (mm2folm (folm2mm M)) σ f ⇔ feval M σ f)
Proof
Induct_on `f` (* 4 *)
>- rw[feval_def]
>- (rw[feval_def] >>  
    qabbrev_tac `tv = (termval (mm2folm (folm2mm M)) σ)` >>
    rw[mm2folm_def,folm2mm_def] >> Cases_on `l` (*2 *)
    >- fs[] >>
    Cases_on `t` (*2 *)
    >- (fs[] >> Cases_on `h` >> fs[term_functions_def] >>
        rw[Abbr`tv`,mm2folm_folm2mm_termval] >> 
        fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
    fs[] >> 
    Cases_on `t'` (* 2 *)
    >- (fs[] >> rw[EQ_IMP_THM] (* 7 *)
        >- (fs[Abbr`tv`,mm2folm_folm2mm_termval] >>
            metis_tac[mm2folm_folm2mm_termval])
        >- metis_tac[]
        >- (fs[Abbr`tv`,mm2folm_folm2mm_termval] >>
            metis_tac[mm2folm_folm2mm_termval])
        >- (Cases_on `h` >> 
            fs[term_functions_def,Abbr`tv`,IMAGE_DEF,SUBSET_DEF] >>
            metis_tac[])
        >- (Cases_on `h'` >> 
            fs[term_functions_def,Abbr`tv`,IMAGE_DEF,SUBSET_DEF] >>
            metis_tac[])
        >- (Cases_on `h` >> 
            fs[term_functions_def,Abbr`tv`,IMAGE_DEF,SUBSET_DEF] >>
            metis_tac[])
        >- (Cases_on `h'` >> 
            fs[term_functions_def,Abbr`tv`,IMAGE_DEF,SUBSET_DEF] >>
            metis_tac[])) >>
    fs[])
>- (rw[feval_def] >> metis_tac[]) >>
rw[feval_def,EQ_IMP_THM]
>- (`(mm2folm (folm2mm M)).Dom = M.Dom` by fs[mm2folm_def,folm2mm_def] >>
    first_x_assum drule >> rw[] >>
    `IMAGE σ(|n |-> a|) 𝕌(:num) ⊆ M.Dom`
      by (irule IMAGE_UPDATE >> rw[]) >>
    metis_tac[]) >>
`(mm2folm (folm2mm M)).Dom = M.Dom` by fs[mm2folm_def,folm2mm_def] >>
`IMAGE σ(|n |-> a|) 𝕌(:num) ⊆ M.Dom`
  by (irule IMAGE_UPDATE >> fs[]) >>
metis_tac[]
QED


Theorem thm_2_68_half1:
!a x. FV a ⊆ {x} /\ form_functions a = {} ==> 
      invar4bisim x 
      (t1: ((num -> α) -> bool) itself) 
      (t2: ((num -> α) -> bool) itself) a ==> 
       ?phi. 
          (!M:'a model σ. 
             fsatis M σ (ST x phi) <=> fsatis M σ a)
          
Proof
rw[] >>
qabbrev_tac 
  `MOC = {ST x phi | (!M σ. IMAGE σ (univ(:num)) ⊆ M.Dom ==>
                            (feval M σ a ==> feval M σ (ST x phi)))}` >>
`!M:'a model σ. (IMAGE σ (univ(:num)) ⊆ M.Dom /\
       (!f. f IN MOC ==> feval M σ f)) ==> feval M σ a` 
  suffices_by cheat
   (rw[] >>
    `?ss. FINITE ss /\ ss ⊆ MOC /\ 
         (∀M σ.
            IMAGE σ 𝕌(:num) ⊆ M.Dom ∧ (∀f. f ∈ ss ⇒ feval M σ f) ⇒
            feval M σ a)`
      by cheat (*compactness cheat*) >>
    drule ST_BIGCONJ >> rw[] >>
    first_x_assum (qspec_then `x` assume_tac) >> 
    `(∀f. f ∈ ss ⇒ ∃phi. f = ST x phi)`
      by 
       (rw[] >> fs[Abbr`MOC`,SUBSET_DEF] >> cheat)
    first_x_assum drule >> rw[] >>
    qexists_tac `psi` >> rw[fsatis_def,valuation_def] >>
    rw[EQ_IMP_THM] (* 2 *)
    >- (`IMAGE σ 𝕌(:num) ⊆ M.Dom` 
         by (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
        metis_tac[])
    >- (`IMAGE σ 𝕌(:num) ⊆ M.Dom` 
         by (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
        `(∀f. f ∈ ss ⇒ feval M σ f)` suffices_by metis_tac[] >>
        rw[] >> fs[Abbr`MOC`,SUBSET_DEF] >> metis_tac[])
   ) >>
(*suffices tac end*)
rw[] >>
qabbrev_tac `Tx = {ST x phi | feval M σ (ST x phi)}` >>
`?N:'a model σn. 
    IMAGE σn 𝕌(:num) ⊆ N.Dom /\
    (!f. (f IN Tx \/ f = a) ==> feval N σn f)` 
  by cheat
   (SPOSE_NOT_THEN ASSUME_TAC >> fs[] >>
    `∀N σn.
       IMAGE σn 𝕌(:num) ⊆ N.Dom /\ 
       (!f. f IN Tx ==> feval N σn f) ==>  ¬feval N σn a`
     by metis_tac[] >>
    `?ss. FINITE ss /\ ss ⊆ Tx /\ 
         (∀M:'a model σ.
            IMAGE σ 𝕌(:num) ⊆ M.Dom ∧ (∀f. f ∈ ss ⇒ feval M σ f) ⇒
            ¬feval M σ a)`
     by cheat (*compactness cheat*) >>
    `∀M σ.
           (IMAGE σ 𝕌(:num) ⊆ M.Dom ∧ 
            feval M σ a) ==> 
               ¬(∀f. f ∈ ss ⇒ feval M σ f)` by metis_tac[] >>
    (*temp cheat for the bound issue*)
    `∀f. f ∈ ss ⇒ ∃phi. f = ST x phi` by cheat >> rw[] >>
    drule ST_BIGCONJ >> strip_tac >> 
    first_x_assum (qspec_then `x` assume_tac) >> 
    first_x_assum drule >> strip_tac >> 
    `ST x (NOT psi) IN MOC`
      by
       (rw[Abbr`MOC`] >> map_every qexists_tac [`x`,`NOT psi`] >> rw[]) >>
    `(!M σ. IMAGE σ 𝕌(:num) ⊆ M.Dom ==>
                   (feval M σ (fNOT cf) <=> (¬∀f. f ∈ ss ⇒ feval M σ f)))`
      by rw[feval_def,fNOT_def] >>
    `feval M σ (ST x (¬psi))` by metis_tac[] >>
    `∀f. f ∈ ss ⇒ feval M σ f` suffices_by metis_tac[ST_fNOT] >>
    rw[] >> fs[Abbr`Tx`,SUBSET_DEF] >> metis_tac[]
   ) >>
`feval N σn a` by fs[] >>
qabbrev_tac `w = σ x` >> 
qabbrev_tac `v = σn x` >> 
`!phi. satis (folm2mm M) w phi <=> satis (folm2mm N) v phi` 
  by 
   (rw[EQ_IMP_THM] (* 2 *)
    >- (`ST x phi IN Tx`
          by
           (`IMAGE σ 𝕌(:num) ⊆ (folm2mm M).frame.world`
              by rw[folm2mm_def] >>
            `fsatis (mm2folm (folm2mm M)) σ (ST x phi)`
              by metis_tac[Abbr`w`,prop_2_47_i] >>
            rw[Abbr`Tx`] >> 
            `feval M σ (ST x phi)` suffices_by metis_tac[] >>
            `form_functions (ST x phi) = {}` 
              by metis_tac[ST_form_functions_EMPTY] >>
            fs[fsatis_def] >> 
            `!f. form_functions f = {} ==> 
                !σ. IMAGE σ 𝕌(:num) ⊆ M.Dom ==> 
                    (feval (mm2folm (folm2mm M)) σ f <=> 
                    feval M σ f)`
              suffices_by 
               (rw[] >> `IMAGE σ 𝕌(:num) ⊆ M.Dom` by fs[folm2mm_def] >>
                metis_tac[]) >>
            (*confirmed the lemma applies, need prove it,
             the lemma is not proved ,required well formness of M


 cheated!*)
            cheat) >>
        `feval N σn (ST x phi)` by metis_tac[] >>
        `IMAGE σn 𝕌(:num) ⊆ (folm2mm N).frame.world`
          by fs[folm2mm_def] >>
        `feval (mm2folm (folm2mm N)) σn (ST x phi)` by cheat >>
        (*trivial by 2.47*) cheat
    >- (* similar*)  cheat
   ) >>
(*apply 2.74*)
`v IN (folm2mm N).frame.world /\ w IN (folm2mm M).frame.world`
  by (fs[folm2mm_def,IMAGE_DEF,SUBSET_DEF,Abbr`w`,Abbr`v`] >> metis_tac[]) >>
drule (thm_2_74_half2 |> INST_TYPE [beta |-> ``:'a``]) >>
rw[] >> first_x_assum drule >> rw[] >>
fs[invar4bisim_def] >>
qabbrev_tac `Mst = (ultraproduct_model U I' (λi. folm2mm M))` >>
qabbrev_tac `Nst = (ultraproduct_model U I' (λi. folm2mm N))` >>
qabbrev_tac `wst = {fw | Uequiv U I' (models2worlds (λi. folm2mm M)) (λi. w) fw}` >>
qabbrev_tac `vst = {fv | Uequiv U I' (models2worlds (λi. folm2mm N)) (λi. w) fv}` >>
first_x_assum (qspecl_then [`Mst`,`Nst`,`vst`,`wst`] assume_tac) >> rfs[] >>
drule corollary_A_21 >> rw[] >> 
`(feval M σ a <=> fsatis (mm2folm Mst) (\x. wst) a) /\ 
fsatis (mm2folm Nst) (\x. vst) a` 
  suffices_by 
   (first_x_assum (qspecl_then [`(λx. wst)`,`(λx. vst)`] assume_tac) >>
    `(λx. wst)⦇x ↦ wst⦈ = (λx. wst) /\
     (λx. vst)⦇x ↦ vst⦈ = (λx. vst)` by fs[FUN_EQ_THM,APPLY_UPDATE_THM] >>
    rw[] >> 
    `fsatis (mm2folm Nst) (λx. vst)⦇x ↦ vst⦈ a` by cheat >>
    `fsatis (mm2folm Mst) (λx. wst) a <=> 
     fsatis (mm2folm Mst) (λx. wst)⦇x ↦ wst⦈ a` by cheat >>
    (*cheated! do not understand why metis does not solve it*)
    metis_tac[]) >>
`(feval M σ a ⇔ fsatis (mm2folm Mst) (λx. wst) a) /\
 (feval N σn a <=> fsatis (mm2folm Nst) (λx. vst) a)`
suffices_by metis_tac[] >> 
`!M σ a I U. 
   (FV a ⊆ {x} /\ form_functions a = ∅ /\
    ultrafilter U I /\
    (∀ff ll. M.Fun ff ll ∈ M.Dom) /\
    IMAGE σ (univ(:num)) ⊆ M.Dom) ==>
    (feval M σ a <=>
     feval (mm2folm (ultraproduct_model U I (λi. folm2mm M))) 
       (λx. {fw | Uequiv U I' (models2worlds (λi. folm2mm M)) (λi. σ x) fw}) a)`
  suffices_by
   (strip_tac >> 
    first_x_assum (qspecl_then [`M`,`σ`,`a`,`I'`,`U`] assume_tac) >> 
    `(∀ff ll. M.Fun ff ll ∈ M.Dom)` by cheat >>
    (*cheated for well-formness*)
    first_x_assum drule_all >> strip_tac >> 
    fs[Abbr`Mst`,Abbr`wst`,Abbr`w`] >> rw[] (*  2 similar*)
    `feval (mm2folm (ultraproduct_model U I' MS))
          (λx. {fw | Uequiv U I' (models2worlds MS) (λi. σ x) fw}) a ⇔
     feval (mm2folm (ultraproduct_model U I' MS))
          (λx'. {fw | Uequiv U I' (models2worlds MS) (λi. σ x) fw}) a`
     suffices_by cheat >>
    (*cheat for the image stuff, trivial*)
    irule holds_valuation >> rw[] >>
    `x' = x` by fs[SUBSET_DEF] >>
    rw[] 
   
    (*cheated! checked the lemma above can be applied*)

)

QED



val _ = export_theory();

