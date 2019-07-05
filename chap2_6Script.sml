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
             ?U (I:num -> bool) MS NS. ultrafilter U I /\
                     (!i. i IN I ==> MS i = M) /\
                     (!i. i IN I ==> NS i = N) /\
               bisim_world (ultraproduct_model U I MS) (ultraproduct_model U I NS) 
                           {fw | Uequiv U I (models2worlds MS) (λi. w) fw}
                           {fv | Uequiv U I (models2worlds NS) (λi. v) fv}
Proof
rw[] >> 
`∃U. ultrafilter U 𝕌(:num) ∧ ∀s. FINITE s ⇒ s ∉ U`
  by metis_tac[exercise_2_5_4_b] >>
`!n. {n} NOTIN U` by fs[] >>
drule example_2_72 >> rw[] >>
map_every qexists_tac [`U`,`univ(:num)`,`\i.M`,`\i.N`] >> rw[] >>
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
(*
Theorem compactness_corollary:
!s phi. 
   (!M σ:num -> α. IMAGE σ (univ(:num)) ⊆ M.Dom ==> 
       (!f. f IN s ==> feval M σ f) ==> feval M σ phi) ==>
   ?ss. FINITE ss /\ ss ⊆ s /\ 
   (!M σ:num -> α. IMAGE σ (univ(:num)) ⊆ M.Dom ==> 
       (!f. f IN ss ==> feval M σ f) ==> feval M σ phi)
Proof
cheat
QED


val folm2mm_def = Define`
folm2mm FM = <| frame := <| world := FM.Dom ;
                              rel := \w1 w2. (FM.Pred 0 [w1;w2] /\
                                              w1 IN FM.Dom /\ w2 IN FM.Dom) |>;
                 valt := \v w. (FM.Pred v [w] /\ w IN FM.Dom) |>`;


val invar4bisim_def = Define`
  invar4bisim x (t1: μ itself) (t2: ν itself) phi <=> 
     (FV phi ⊆ {x} /\ 
     !(M:μ model) (N:ν model) v w.
        bisim_world (folm2mm M) (folm2mm N) (w:μ) (v:ν) ==> 
           (!(σm: num -> μ) (σn: num -> ν). 
                    fsatis M σm(|x |-> w|) phi <=> 
                    fsatis N σn(|x |-> v|) phi))`

Theorem ultraproduct_comm_termval':

*)f



Theorem ultraproduct_comm_feval':
  !phi U I FMS. ultrafilter U I (* /\ (!i. i IN I ==> (MS i).frame.world <> {})*)
          ==> form_functions phi = {} ==>
         !σ. IMAGE σ (univ(:num)) ⊆ ultraproduct U I (folmodels2Doms FMS) ==>
          (feval (mm2folm (ultraproduct_model U I (\i. folm2mm (FMS i)))) σ phi <=>
            feval (ultraproduct_folmodel U I FMS) σ phi)
Proof
(*Induct_on `phi` (* 4 *)
>- rw[feval_def]
>- rw[feval    *)cheat                 
QED

Theorem thm_2_68_half1:
!a x. FV a ⊆ {x} ==> 
      invar4bisim x 
      (t1: ((num -> α) -> bool) itself) 
      (t2: ((num -> α) -> bool) itself) a ==> 
       ?phi. 
          (!M σ. fsatis M σ (ST x phi) <=> fsatis M σ a)
          
Proof
rw[] >>
qabbrev_tac 
  `MOC = {ST x phi | (!M σ. IMAGE σ (univ(:num)) ⊆ M.Dom ==>
                            (feval M σ a ==> feval M σ (ST x phi)))}` >>
`!M σ. IMAGE σ (univ(:num)) ⊆ M.Dom ==>
       (!f. f IN MOC ==> feval M σ f) ==> feval M σ a` 
  suffices_by cheat >>
(*first usage of compactness*)
rw[] >>
qabbrev_tac `Tx = {ST x phi | feval M σ (ST x phi)}` >>
`!M:'a model. consistent M (Tx ∪ {a})` by cheat >>
`?N σn:num -> α. IMAGE σn (univ(:num)) ⊆ N.Dom /\
        (!f. f IN (Tx ∪ {a}) ==> feval N σn f)` by cheat >>
(*get N by compactness*)
`feval N σn a` by fs[] >>
qabbrev_tac `w = σ x` >> 
qabbrev_tac `v = σn x` >> 
`!phi. satis (folm2mm M) w phi <=> satis (folm2mm N) v phi` by cheat >>
`∃U I MS NS.
             ultrafilter U I ∧ (∀i. i ∈ I ⇒ MS i = (folm2mm M)) ∧
             (∀i. i ∈ I ⇒ NS i = (folm2mm N)) ∧
             bisim_world (ultraproduct_model U I MS)
               (ultraproduct_model U I NS)
               {fw | Uequiv U I (models2worlds MS) (λi. w) fw}
               {fv | Uequiv U I (models2worlds NS) (λi. v) fv}` by cheat >>
`feval (ultraproduct_folmodel U I' (\i. N))
       (λx. {g | Uequiv U I' (folmodels2Doms (\i. N)) g (λi. σn x)})
       a` by cheat >>
(*corollary_A_21*)
`feval (ultraproduct_folmodel U I' (λi. (mm2folm (folm2mm N))))
          (λx. {g | Uequiv U I' (folmodels2Doms (λi. N)) g (λi. σn x)}) a`
by cheat >>
(*ugly!*)
`feval (mm2folm (ultraproduct_model U I' (\i.(folm2mm N) ))) 
      (λx. {g | Uequiv U I' (folmodels2Doms (λi. N)) g (λi. σn x)})
       a`
by cheat >>
fs[invar4bisim_def] >>
`feval (mm2folm (ultraproduct_model U I' (λi. folm2mm M)))
       (λx. {g | Uequiv U I' (folmodels2Doms (λi. M)) g (λi. σ x)}) a`
by cheat >>
(*definition of invar4bisim*)
Theorem ultraproduct_comm_termval':
  !t U I MS. ultrafilter U I ==> term_functions t = {} ==>
      !σ. (termval (ultraproduct_folmodel U I MS) σ t =
           termval (mm2folm (ultraproduct_model U I (λi. folm2mm (MS i)))) σ t)
Proof
 Cases_on `t` >> rw[termval_def] 
QED

(*
(termval
                (mm2folm (ultraproduct_model U I' (λi. folm2mm (MS i)))) σ)
*)

Theorem ultraproduct_comm_feval':
!phi U I MS. 
  ultrafilter U I ==>
  form_functions phi = {} ==> 
  (*!i. (MS i) Pred n [] = F*)
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
           folm2mm_def,ultraproduct_model_def] >> cheat
        (*{i | i ∈ I' ∧ (MS i).Pred n []} ∉ U should be empty otherwise*)) 
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
               `∀n0 l0 i. (MS i).Fun n0 l0 ∈ (MS i).Dom` by cheat >>
               (*cheated! need extra assumption*)
               metis_tac[folmodels2Doms_models2worlds_folm2mm]) >>
            (*remove the conj first*)
           `sl <> {}` by metis_tac[ultraproduct_eqclass_non_empty] >>
           `CHOICE sl IN sl` by metis_tac[CHOICE_DEF] >>
           `{i | i ∈ I' ∧ (MS i).Pred n [CHOICE sl i]} = 
            {i | i ∈ I' ∧ CHOICE sl i ∈ (folm2mm (MS i)).valt n}`
             by (rw[EXTENSION,EQ_IMP_THM,folm2mm_def] >> cheat) >>
           (*CHOICE sl x ∈ (MS x).Dom trivial cheat*) >> 
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
            `n = 0` by cheat  (*
             {i | i ∈ I' ∧ (MS i).Pred n [CHOICE sl1 i; CHOICE sl2 i]}
             cheated! need extra assumption since we 
             are only careing about folmodels which are modal*) >>
            `sl1 ∈ ultraproduct U I' (models2worlds (λi. folm2mm (MS i))) ∧
             sl2 ∈ ultraproduct U I' (models2worlds (λi. folm2mm (MS i)))`
              by
               (`!t. (termval (ultraproduct_folmodel U I' MS) σ t) IN
                 ultraproduct U I' (models2worlds (λi. folm2mm (MS i)))`
                  suffices_by metis_tac[] >>
                drule termval_IN_ultraproduct_Dom' >>
                rw[] >> 
                `∀n0 l0 i. (MS i).Fun n0 l0 ∈ (MS i).Dom` by cheat >>
                (*cheated! need extra assumption*)
                metis_tac[folmodels2Doms_models2worlds_folm2mm]) >>
            `{i | i ∈ I' ∧ (MS i).Pred n [CHOICE sl1 i; CHOICE sl2 i]} = 
             {i | i ∈ I' ∧ (folm2mm (MS i)).frame.rel 
                            (CHOICE sl1 i) (CHOICE sl2 i)}`
              by
               (rw[EXTENSION,EQ_IMP_THM,folm2mm_def] >> cheat (*trivial *)) >>
            `sl1 <> {}` by metis_tac[ultraproduct_eqclass_non_empty] >>
            `sl2 <> {}` by metis_tac[ultraproduct_eqclass_non_empty] >>
            `CHOICE sl1 IN sl1 /\ CHOICE sl2 IN sl2` by metis_tac[CHOICE_DEF]>>
            rw[EQ_IMP_THM] >- metis_tac[] >>
            qmatch_abbrev_tac `ss IN U` >>
            irule ultrafilter_INTER_INTER_SUBSET >>
            `ss ⊆ I'` by rw[SUBSET_DEF,INTER_DEF] >> rw[] (* 2 *)
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
                metis_tac[]) >>
            qexists_tac `I'` >> rw[SUBSET_DEF])
        >- (`(mm2folm 
              (ultraproduct_model U I' (λi. folm2mm (MS i)))).Pred n mapl = F`
               by rw[mm2folm_def] >>
            `!i a b c d n. (MS i).Pred n (a:: b :: c :: d) = F` by cheat >>
            (*cheated! one of the wf axioms*)
            `(ultraproduct_folmodel U I' MS).Pred n mapl = F` 
             by (rw[ultraproduct_folmodel_def] >>
                 metis_tac[EMPTY_NOTIN_ultrafilter]) >>
            metis_tac[])
    )
   )
>- rw[]
>- (rw[feval_def,EQ_IMP_THM] (* 2 *)
    >- (first_x_assum drule >> rw[] >>
        `IMAGE σ⦇n ↦ a⦈ 𝕌(:num) ⊆ ultraproduct U I' (folmodels2Doms MS)`
          by (irule IMAGE_UPDATE >> 
              `(mm2folm (ultraproduct_model U I' (λi. folm2mm (MS i)))).Dom =
               ultraproduct U I' (folmodels2Doms MS)`
               by 
                (rw[mm2folm_def,ultraproduct_model_def] >>
                 metis_tac[folmodels2Doms_models2worlds_folm2mm]) >>
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

----------

Theorem termval_IN_ultraproduct_Dom':
∀U I MS.
    ultrafilter U I ⇒
     (∀n0 l0 i. (MS i).Fun n0 l0 ∈ (MS i).Dom) ==>
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

---------------------
(*apply 2.74 half 2*)
`countably_saturated (mm2folm (ultraproduct_model U I' MS))` by cheat >>
`countably_saturated (mm2folm (ultraproduct_model U I' NS))` by cheat >>
(*need add it to 2.66 detour lemma, not contained in 2.74*)
`M_sat (ultraproduct_model U I' MS)` by cheat >>
`M_sat (ultraproduct_model U I' NS)` by cheat >>
(*by 2.65*)
`





`(σ x) IN (folm2mm M).frame.world /\
 (σn x) IN (folm2mm N).frame.world` by cheat >>
drule (thm_2_74_half2 |> INST_TYPE [beta |-> ``:'a``]) >> rw[] >> 
`(∀phi. satis (folm2mm N) (σn x) phi ⇔ satis (folm2mm M) (σ x) phi)` by cheat >>
rw[] >>
first_x_assum (qspecl_then [`(folm2mm M)`,`σ x`] assume_tac) >>   
first_x_assum drule_all >> rw[] >> 
qabbrev_tac `Na =  (ultraproduct_model U I' MS)` >>
qabbrev_tac `Ma = ultraproduct_model U I' NS` >>
fs[invar4bisim_def] >>

(* first_x_assum drule >> rw[] >>
`feval M σ a <=>
 feval (ultraproduct_folmodel U I' (\i. M))
                   (λx. {g | Uequiv U I' (folmodels2Doms (\i.M)) g (λi. σ x)})
                   a`
by cheat >>
`feval (ultraproduct_folmodel U I' (λi. M))
          (λx. {g | Uequiv U I' (folmodels2Doms (λi. M)) g (λi. σ x)}) a <=> 
fsatis (mm2folm (ultraproduct_model U I' NS))
              σn'⦇x ↦ {fv | Uequiv U I' (models2worlds NS) (λi. σ x) fv}⦈ a


(mm2folm (ultraproduct_model U I' NS))
              σn'⦇x ↦ {fv | Uequiv U I' (models2worlds NS) (λi. σ x) fv}⦈ a
*)

`bisim_world (folm2mm M) (folm2mm N) (σ x) (σn x)` by cheat >>
qabbrev_tac `na = {fw | Uequiv U I' (models2worlds MS) (λi. σn x) fw}` >>
qabbrev_tac `ma = {fv | Uequiv U I' (models2worlds NS) (λi. σ x) fv}` >>
`bisim_world (folm2mm (mm2folm Na)) (folm2mm (mm2folm Ma)) na ma` by cheat >>
first_x_assum drule >> rw[] >> 
`feval M σ a ⇔
 feval (ultraproduct_folmodel U I' (\i. M))
       (λx. {g | Uequiv U I' (\i. M.Dom) g (λi. σ x)})
                      a` by cheat
`




(*second usage of compactness*)
`?(Ma:(num,(num -> α) -> bool) chap1$model) eqcm
  (Na:(num,(num -> α) -> bool) chap1$model) eqcn. 
    countably_saturated (mm2folm Ma) /\
    countably_saturated (mm2folm Na) /\
    (!ff σ. IMAGE σ (univ(:num)) ⊆ M.Dom ==>
           (feval M σ ff <=> feval (mm2folm Ma) (eqcm σ) ff)) /\
    (!ff σ. IMAGE σ (univ(:num)) ⊆ N.Dom ==>
           (feval N σ ff <=> feval (mm2folm Na) (eqcn σ) ff)) /\
    bisim_world Ma Na (eqcm σ x) (eqcm σ x)`
  by cheat >>
`feval (mm2folm Ma) (feqc σ) a` suffices_by cheat >>
fs[invar4bisim_def] >> 

QED
(feval (mm2folm (ultraproduct_model U I MS)) σ phi <=>
                 feval (ultraproduct_folmodel U I (\i. mm2folm (MS i))) σ phi)





 
val closed_under_bisim_def = Define`
  closed_under_bisim K <=>
  !(M:(num,α) chap1$model,w:α). 
      K (t1: α itself) (M,w) ==>
      !N v:β. bisim_world M N w v ==> K (t2: β itself) (N,v)`     




Theorem thm_2_68:
  
 
  

val _ = export_theory();

