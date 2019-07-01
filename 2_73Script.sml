open HolKernel Parse boolLib bossLib;
open ultrafilterTheory;
open HolKernel Parse boolLib bossLib;
open chap1Theory;
open pred_setTheory;
open relationTheory;
open arithmeticTheory;
open set_relationTheory;
open pairTheory;
open listTheory;
open rich_listTheory;
open combinTheory;
open folLangTheory;
open folModelsTheory;
open chap2_4revisedTheory;
open equiv_on_partitionTheory;
open ultraproductTheory;
val _ = ParseExtras.tight_equality()
val _ = new_theory "2_73";



Theorem thm_A_19_ii:
   !U I phi. ultrafilter U I ==>
      !σ FMS. IMAGE σ (univ(:num)) ⊆ ultraproduct U I (folmodels2Doms FMS) ==>
             (!i ff ll. i IN I ==> (FMS i).Fun ff ll IN (FMS i).Dom) ==>
                  (feval (ultraproduct_folmodel U I FMS) σ phi <=>
                  {i | i IN I /\ feval (FMS i) (\x. (CHOICE (σ x)) i) phi} IN U)
Proof
 cheat
QED


Theorem ultraproduct_comm_termval:
  !t U I MS. ultrafilter U I ==> term_functions t = {} ==>
      !σ. (termval (mm2folm (ultraproduct_model U I MS)) σ t =
           termval (ultraproduct_folmodel U I (\i. mm2folm (MS i))) σ t)
Proof
 Cases_on `t` >> rw[termval_def] 
QED

Theorem ultraproduct_image:
  !U I. ultrafilter U I ==> 
       !A eqc. eqc IN (ultraproduct U I A) ==>
               !f. f IN eqc ==> (!i. i IN I ==> (f i) IN (A i))
Proof
  rw[ultraproduct_def,partition_def] >> fs[] >> fs[Cart_prod_def]
QED

Theorem ultraproduct_folmodel_well_formed:
!U I.  ultrafilter U I ==> 
  !FMS n l. (!n0 l0 i. ((FMS i).Fun n0 l0) IN (FMS i).Dom) ==> 
         ((ultraproduct_folmodel U I FMS).Fun n l) IN (ultraproduct_folmodel U I FMS).Dom
Proof
  rw[ultraproduct_folmodel_def] >> 
  rw[ultraproduct_def,folmodels2Doms_def,partition_def,Cart_prod_def] >>
  qexists_tac `\i. (FMS i).Fun n (MAP (λfc. CHOICE fc i) l)` >> rw[Once EXTENSION] >>
  rw[Uequiv_def,EQ_IMP_THM] (* 5 *)
  >- metis_tac[MEMBER_NOT_EMPTY]
  >- rw[Cart_prod_def]
  >- rw[Cart_prod_def]
  >> (`{i | i ∈ I' ∧ x i = (FMS i).Fun n (MAP (λfc. CHOICE fc i) l)} = 
     {i | i ∈ I' ∧ (FMS i).Fun n (MAP (λfc. CHOICE fc i) l) = x i}` suffices_by metis_tac[] >>
     rw[EXTENSION] >> metis_tac[])
QED

Theorem ultraproduct_comm_Dom:
  !U I MS. (ultraproduct_folmodel U I (\i. mm2folm (MS i))).Dom =
           (mm2folm (ultraproduct_model U I MS)).Dom
Proof
 rw[ultraproduct_model_def,ultraproduct_folmodel_def,mm2folm_def,folmodels2Doms_def,models2worlds_def]
QED

Theorem mm2folm_ultraproduct_model_Dom:
!U I MS. (mm2folm (ultraproduct_model U I MS)).Dom = ultraproduct U I (models2worlds MS)
Proof
rw[ultraproduct_model_def,ultraproduct_folmodel_def,mm2folm_def,folmodels2Doms_def,models2worlds_def]
QED

Theorem ultraproduct_folmodel_Dom:
!U I FMS. (ultraproduct_folmodel U I FMS).Dom = ultraproduct U I (folmodels2Doms FMS)
Proof
rw[ultraproduct_folmodel_def]
QED

Theorem mm2folm_well_formed:
  !M n l. M.frame.world <> {} ==> ((mm2folm M).Fun n l) IN (mm2folm M).Dom
Proof
  rw[mm2folm_def] >> metis_tac[CHOICE_DEF]
QED


Theorem termval_IN_ultraproduct_Dom:
!U I MS. ultrafilter U I ==> 
 !σ. IMAGE σ 𝕌(:num) ⊆ ultraproduct U I (models2worlds MS) ==>
  !a. (termval (mm2folm (ultraproduct_model U I MS)) σ a) IN 
      (ultraproduct U I (models2worlds MS))
Proof
  rw[] >>
  `(ultraproduct U I' (models2worlds MS)) = (mm2folm (ultraproduct_model U I' MS)).Dom`
  by metis_tac[mm2folm_ultraproduct_model_Dom] >>
  rw[] >> irule termval_IN_Dom >> rw[] (* 2 *)
  >- (irule mm2folm_well_formed >> fs[IMAGE_DEF,SUBSET_DEF] >>
     `(ultraproduct_model U I' MS).frame.world =  
      (mm2folm (ultraproduct_model U I' MS)).Dom` by fs[mm2folm_def] >> rw[] >> 
     simp[GSYM MEMBER_NOT_EMPTY] >> fs[PULL_EXISTS] >> qexists_tac `σ x` >> rw[])
  >- fs[mm2folm_def]     
QED

Theorem ultraproduct_val_IN_A:
  !U I. ultrafilter U I ==> 
     !A eqc. eqc IN ultraproduct U I A ==> 
              !f. f IN eqc ==> (!i. i IN I ==> (f i) IN (A i))
Proof
  rw[] >> fs[ultraproduct_def,partition_def,Cart_prod_def] >> rfs[]
QED

Theorem ultraproduct_comm_feval:
  !phi U I MS. ultrafilter U I (* /\ (!i. i IN I ==> (MS i).frame.world <> {})*)
          ==> form_functions phi = {} ==>
            !σ. IMAGE σ (univ(:num)) ⊆ ultraproduct U I (models2worlds MS) ==>
                (feval (mm2folm (ultraproduct_model U I MS)) σ phi <=>
                 feval (ultraproduct_folmodel U I (\i. mm2folm (MS i))) σ phi)
Proof
  Induct_on `phi` (* 4 *)
  >- rw[feval_def]
  >- rw[feval_def] >> 
     (* cheat to see what happens if the termval are same (where is the cheat...) *)
     `(MAP (termval (mm2folm (ultraproduct_model U I' MS)) σ) l) = 
      (MAP (termval (ultraproduct_folmodel U I' (λi. mm2folm (MS i))) σ) l)` by 
        (irule MAP_LIST_EQ >> rw[] >> irule ultraproduct_comm_termval >> rw[] >>
         SPOSE_NOT_THEN ASSUME_TAC >> fs[GSYM MEMBER_NOT_EMPTY] >> 
        `x IN LIST_UNION (MAP term_functions l)` suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
        simp[IN_LIST_UNION] >> qexists_tac `term_functions m` >> rw[MEM_MAP] >> metis_tac[]) >>
     rw[] >> 
     qabbrev_tac `mapl = (MAP (termval (ultraproduct_folmodel U I' (λi. mm2folm (MS i))) σ) l)` >> 
     Cases_on `mapl = []`(* 2 *)
     >- (fs[] >> rw[mm2folm_def,ultraproduct_folmodel_def,ultraproduct_model_def] >>
        metis_tac[EMPTY_NOTIN_ultrafilter])
     >- (`(?a. l = [a]) \/ (?a b. l = [a;b]) \/ (?a b c d. l = a :: b :: c :: d)` by 
            (Cases_on `l` >> fs[] >> Cases_on `t` >> fs[] >> Cases_on `t'` >> fs[])
        (* 3 *)
        >- (rw[] >> qabbrev_tac `sl = termval (mm2folm (ultraproduct_model U I' MS)) σ a` >>
           rw[mm2folm_def,ultraproduct_folmodel_def,ultraproduct_model_def] >> rw[EQ_IMP_THM] (* 3 *) 
           >- (`{i | i IN I' /\ f i = (CHOICE sl) i} IN U` by 
                (irule ultraproduct_same_eqclass >> rw[] >>
                map_every qexists_tac [`models2worlds MS`,`sl`] >> rw[] >>
                `sl <> {}` suffices_by metis_tac[CHOICE_DEF] >> 
                 drule ultraproduct_eqclass_non_empty >> rw[] >> metis_tac[]) >>
              `{i | i ∈ I' ∧ f i ∈ (MS i).valt n} ∩ {i | i ∈ I' ∧ f i = CHOICE sl i} ⊆ 
               {i | i ∈ I' ∧ CHOICE sl i ∈ (MS i).frame.world ∧ (MS i).valt n (CHOICE sl i)}` by
                 (rw[INTER_DEF,SUBSET_DEF] (* 2 *)
                 >- (drule ultraproduct_image >> rw[] >>
                    first_x_assum (qspecl_then [`models2worlds MS`,`sl`,`CHOICE sl`,`x`] assume_tac)>>
                    fs[models2worlds_def] >> first_x_assum irule >> rw[] >>
                    `sl <> {}` suffices_by metis_tac[CHOICE_DEF] >> 
                     drule ultraproduct_eqclass_non_empty >> rw[] >> metis_tac[])
                 >- fs[IN_DEF]) >> 
              (* proved subset *)
              irule ultrafilter_SUBSET' >> rw[PULL_EXISTS] (* 2 *)
              >- metis_tac[ultrafilter_INTER]
              >- (qexists_tac `I'` >> rw[SUBSET_DEF]))
           >- (drule ultraproduct_folmodel_well_formed >> rw[Abbr`sl`] >> 
              `ultraproduct U I' (models2worlds MS) = 
               (mm2folm (ultraproduct_model U I' MS)).Dom` by 
                metis_tac[mm2folm_ultraproduct_model_Dom] >> 
              rw[] >> irule termval_IN_Dom >> rw[](* 2 *)
              >- (`(ultraproduct_model U I' MS).frame.world <> {}` suffices_by 
                   metis_tac[mm2folm_well_formed] >> (* cheated! (fixed)*)
                   rw[Once ultraproduct_model_def] >> 
                   fs[mm2folm_ultraproduct_model_Dom] >>
                   fs[IMAGE_DEF,SUBSET_DEF,GSYM MEMBER_NOT_EMPTY] >> qexists_tac `σ x` >> rw[]>>
                   metis_tac[])
              >- metis_tac[mm2folm_ultraproduct_model_Dom])
           >- (qexists_tac `CHOICE sl` >> rw[] (* 2 *)
              >- (`sl <> {}` suffices_by metis_tac[CHOICE_DEF] >> 
                  rw[Abbr`sl`] >> drule ultraproduct_eqclass_non_empty >> rw[] >>
                  metis_tac[termval_IN_ultraproduct_Dom])
                 (*once proved sl in world then true by some lemma (fixed)*)
              >- (irule ultrafilter_SUBSET' >> rw[PULL_EXISTS] (* 2 *)
                 >- (qexists_tac `{i | i ∈ I' ∧ CHOICE sl i ∈ (MS i).frame.world ∧
                                 (MS i).valt n (CHOICE sl i)}` >> rw[SUBSET_DEF,IN_DEF])
                 >- (qexists_tac `I'` >> rw[SUBSET_DEF]))))
        (*one out of three subgoals solved here*)
        >- (rw[] >>
           qabbrev_tac `sl1 = termval (mm2folm (ultraproduct_model U I' MS)) σ a` >>
           qabbrev_tac `sl2 = termval (mm2folm (ultraproduct_model U I' MS)) σ b` >>
           rw[mm2folm_def,ultraproduct_folmodel_def,ultraproduct_model_def] >> rw[EQ_IMP_THM](*5*)
           >- (`{i | i IN I' /\ f i = (CHOICE sl1) i} IN U` by 
                (irule ultraproduct_same_eqclass >> rw[] >>
                map_every qexists_tac [`models2worlds MS`,`sl1`] >> rw[] >>
                `sl1 <> {}` suffices_by metis_tac[CHOICE_DEF] >> 
                drule ultraproduct_eqclass_non_empty >> rw[] >> metis_tac[]) >>
              `{i | i IN I' /\ g i = (CHOICE sl2) i} IN U` by 
                (irule ultraproduct_same_eqclass >> rw[] >>
                map_every qexists_tac [`models2worlds MS`,`sl2`] >> rw[] >>
                `sl2 <> {}` suffices_by metis_tac[CHOICE_DEF] >> 
                drule ultraproduct_eqclass_non_empty >> rw[] >> metis_tac[]) >>
              qmatch_abbrev_tac `BS IN U` >> 
              `{i | i ∈ I' ∧ (MS i).frame.rel (f i) (g i)} ∩ 
               {i | i ∈ I' ∧ f i = CHOICE sl1 i} ∩ {i | i ∈ I' ∧ g i = CHOICE sl2 i} ⊆ BS` by
               (* start a proof subset *)
               (rw[SUBSET_DEF,INTER_DEF,Abbr`BS`] (* 3 *)
               >- fs[] 
               >- (`f x IN (MS x).frame.world` suffices_by metis_tac[] >>
                  drule ultraproduct_val_IN_A >> rw[] >> 
                  first_x_assum (qspecl_then [`models2worlds MS`,`sl1`, `f`,`x`] assume_tac) >>
                  fs[models2worlds_def] >> metis_tac[])
               >- (`g x IN (MS x).frame.world` suffices_by metis_tac[] >>
                  drule ultraproduct_val_IN_A >> rw[] >> 
                  first_x_assum (qspecl_then [`models2worlds MS`,`sl2`, `g`,`x`] assume_tac) >>
                  fs[models2worlds_def] >> metis_tac[]))
              (*subset proof end*)
              `BS ⊆ I'` by fs[Abbr`BS`,SUBSET_DEF] >> drule ultrafilter_INTER_INTER_SUBSET >> rw[] >>
              first_x_assum irule >> metis_tac[](* tedious! same as above (fixed)*))
           >- (SPOSE_NOT_THEN ASSUME_TAC >> 
              `{i | i ∈ I' ∧ n = 0 ∧ (MS i).frame.rel (CHOICE sl1 i) (CHOICE sl2 i) ∧
                    CHOICE sl1 i ∈ (MS i).frame.world ∧
                    CHOICE sl2 i ∈ (MS i).frame.world} = {}` by rw[Once EXTENSION] >>
              metis_tac[EMPTY_NOTIN_ultrafilter])
           >- (map_every qexists_tac [`CHOICE sl1`,`CHOICE sl2`] >> rw[] (* 3 *)
              >- (`sl1 <> {}` suffices_by metis_tac[CHOICE_DEF] >> 
                 drule ultraproduct_eqclass_non_empty >> rw[] >> rw[Abbr`sl1`] >>
                 `termval (mm2folm (ultraproduct_model U I' MS)) σ a ∈
                    ultraproduct U I' (models2worlds MS)` by metis_tac[termval_IN_ultraproduct_Dom]>>
                 metis_tac[ultraproduct_eqclass_non_empty])
              >- (`sl2 <> {}` suffices_by metis_tac[CHOICE_DEF] >> 
                 drule ultraproduct_eqclass_non_empty >> rw[] >> rw[Abbr`sl2`] >>
                 `termval (mm2folm (ultraproduct_model U I' MS)) σ b ∈
                    ultraproduct U I' (models2worlds MS)` by metis_tac[termval_IN_ultraproduct_Dom]>>
                 metis_tac[ultraproduct_eqclass_non_empty])
              >- (irule ultrafilter_SUBSET' >> rw[] (* 2 *)
                 >- (qexists_tac `{i |i ∈ I' ∧ n = 0 ∧(MS i).frame.rel (CHOICE sl1 i) (CHOICE sl2 i) ∧
                             CHOICE sl1 i ∈ (MS i).frame.world ∧ CHOICE sl2 i ∈ (MS i).frame.world}`>>
                    rw[SUBSET_DEF])
                 >- (qexists_tac `I'` >> rw[SUBSET_DEF])))
           >- (rw[Abbr`sl1`] >> irule termval_IN_ultraproduct_Dom >> rw[])
           >- (rw[Abbr`sl2`] >> irule termval_IN_ultraproduct_Dom >> rw[]))
        >- (rw[mm2folm_def,ultraproduct_folmodel_def,ultraproduct_model_def] >>
           metis_tac[EMPTY_NOTIN_ultrafilter])) 
  >- rw[feval_def] 
  >- (rw[feval_def] >> rw[EQ_IMP_THM] (* 2 same *) >>
     first_x_assum (qspecl_then [`U`,`I'`,`MS`] assume_tac) >> rfs[] >>
     first_x_assum (qspec_then `σ(|n |-> a|)` assume_tac) >>
     `(ultraproduct_folmodel U I' (λi. mm2folm (MS i))).Dom = 
      (mm2folm (ultraproduct_model U I' MS)).Dom` by 
        metis_tac[ultraproduct_comm_Dom,mm2folm_ultraproduct_model_Dom] >>
     `IMAGE σ⦇n ↦ a⦈ 𝕌(:num) ⊆ ultraproduct U I' (models2worlds MS)` suffices_by metis_tac[] >>
     irule IMAGE_UPDATE >> rw[] >> 
     metis_tac[ultraproduct_comm_Dom,mm2folm_ultraproduct_model_Dom])
QED




Theorem ultraproduct_comm_feval:
  !phi U I MS. ultrafilter U I (* /\ (!i. i IN I ==> (MS i).frame.world <> {})*)
          ==> form_functions phi = {} ==>
            !σ. IMAGE σ (univ(:num)) ⊆ ultraproduct U I (models2worlds MS) ==>
                (feval (mm2folm (ultraproduct_model U I MS)) σ phi <=>
                 feval (ultraproduct_folmodel U I (\i. mm2folm (MS i))) σ phi)
Proof
cheat
QED


(* theory on shift in order to pass from expansion to mm2folm model and then to ultraprodfol model*)

Definition shift_term_def:
  shift_term n (V m) = V (m+n) /\
  shift_term n (Fn m l) = if l = [] then (V m) else (Fn m (MAP (shift_term n) l))
Termination
WF_REL_TAC `measure (term_size o SND)` >> rw[term_size_lemma]
End

Definition shift_form_def:
  shift_form n False = False /\
  shift_form n (Pred m l) = Pred m (MAP (shift_term n) l) /\
  shift_form n (IMP f1 f2) = IMP (shift_form n f1) (shift_form n f2) /\
  shift_form n (FALL x f) = FALL (x + n) (shift_form n f)
End

Definition shift_valuation_def:
  shift_valuation n σ f = \m. if m < n then (f m) else (σ (m-n))
End

Theorem expansion_shift_termval:
  !M A M' f. expansion (mm2folm M) A M' f ==>
            !t. (∀c. c ∈ FCT t ⇒ c < CARD A) ==>
                !σ. (termval M' σ t =
                    termval (mm2folm M) (shift_valuation (CARD A) σ f) (shift_term (CARD A) t))
Proof
  strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>
  completeInduct_on `term_size t` >> Cases_on `t` >> rw[] (* 3 *)
  >- rw[termval_def,shift_valuation_def,shift_term_def]
  >- (rw[termval_def,shift_valuation_def,shift_term_def] >> fs[expansion_def])
  >- (rw[termval_def,shift_valuation_def,shift_term_def] >> fs[expansion_def] >>
      fs[mm2folm_def])
QED


Theorem expansion_shift_feval:
  !M A M' f. expansion (mm2folm M) A M' f ==>
            !phi. (∀c. c ∈ FC phi ⇒ c < CARD A) ==>
                 !σ. 
                    IMAGE σ (univ(:num)) ⊆ M.frame.world ==>
                    (feval M' σ phi <=> 
                    feval (mm2folm M) (shift_valuation (CARD A) σ f) (shift_form (CARD A) phi))
Proof
  strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >> Induct_on `phi` (* 4 *)
  >- rw[feval_def,shift_form_def]
  >- (rw[feval_def,shift_form_def,shift_term_def,shift_valuation_def,expansion_def] >> 
     ` M'.Pred n (MAP (termval M' σ) l) ⇔
       M'.Pred n
          (MAP
             (termval (mm2folm M)
                (λm. if m < CARD A then f m else σ (m - CARD A)))
             (MAP (shift_term (CARD A)) l))` suffices_by metis_tac[expansion_def] >>
     AP_TERM_TAC >> simp[MAP_MAP_o] >> irule MAP_LIST_EQ >> rw[] >> 
     drule expansion_shift_termval >> rw[] >> 
     first_x_assum (qspecl_then [`m`, `σ`] assume_tac) >> fs[shift_valuation_def] >>
     first_x_assum irule >> rw[] >> first_x_assum irule >> rw[MEM_MAP,PULL_EXISTS] >>
     metis_tac[])
  >- (rw[FC_def] >>
     `(∀c. c ∈ FC phi ==> c < CARD A) /\
      (!c. c ∈ FC phi' ⇒ c < CARD A)` by metis_tac[] >> 
     first_x_assum drule >> first_x_assum drule >> rw[] >> 
     rw[EQ_IMP_THM,shift_form_def])
  >- (rw[FC_def] >> first_x_assum drule >> rw[feval_def] >> rw[EQ_IMP_THM] 
    >- (rw[shift_form_def] >>
     `(shift_valuation (CARD A) σ f)⦇n + CARD A ↦ a⦈ = 
      (shift_valuation (CARD A) σ(|n |-> a|) f)` by (* store as little lemma ?*) 
         (rw[FUN_EQ_THM,shift_valuation_def] >> 
         Cases_on `x < CARD A` (* 2 *)
         >- rw[APPLY_UPDATE_THM] 
         >- (Cases_on `x = n + CARD A` >> rw[APPLY_UPDATE_THM])) >>
     rw[] >> first_x_assum (qspec_then `σ(|n |-> a|)` assume_tac) >> rw[] >> 
     `IMAGE σ⦇n ↦ a⦈ 𝕌(:num) ⊆ M.frame.world /\ feval M' σ⦇n ↦ a⦈ phi` suffices_by metis_tac[] >>
     rw[] (* 2 *) >- (irule IMAGE_UPDATE >> fs[mm2folm_def]) >- fs[mm2folm_def,expansion_def])
    >- (first_x_assum (qspec_then `σ(|n |-> a|)` assume_tac) >>
       `IMAGE σ⦇n ↦ a⦈ 𝕌(:num) ⊆ M.frame.world /\ 
       feval (mm2folm M) (shift_valuation (CARD A) σ⦇n ↦ a⦈ f)
           (shift_form (CARD A) phi)` suffices_by metis_tac[] >> rw[] (* 2 *)
       >- (irule IMAGE_UPDATE >> fs[mm2folm_def,expansion_def] >> rfs[])
       >- (fs[shift_form_def] >> first_x_assum (qspec_then `a` assume_tac) >> rw[] >> 
          `a IN (mm2folm M).Dom` by (fs[mm2folm_def,expansion_def] >> rfs[]) >> fs[] >>
          `(shift_valuation (CARD A) σ f)⦇n + CARD A ↦ a⦈ = 
           (shift_valuation (CARD A) σ(|n |-> a|) f)` by (* store as little lemma ?*) 
             (rw[FUN_EQ_THM,shift_valuation_def] >> 
             Cases_on `x < CARD A` (* 2 *)
              >- rw[APPLY_UPDATE_THM] 
              >- (Cases_on `x = n + CARD A` >> rw[APPLY_UPDATE_THM])) >>
         fs[])))
QED

Theorem shift_term_functions_EMPTY:
  !t. (∀c. c ∈ term_functions t ⇒ FST c ∈ count (CARD A) ∧ SND c = 0) ==>
      term_functions (shift_term (CARD A) t) = {}
Proof
  completeInduct_on `term_size t` >> rw[] >> Cases_on `t` >> fs[shift_term_def] >> Cases_on `l = []`>>
  fs[term_functions_def] >> first_x_assum (qspec_then `(n,LENGTH l)` assume_tac) >> fs[]
QED

Theorem shift_form_functions_EMPTY:
  !phi. (∀c. c ∈ form_functions phi ⇒ FST c ∈ count (CARD A) ∧ SND c = 0) ==>
     form_functions (shift_form (CARD A) phi) = {}
Proof
  Induct_on `phi` (* 4 *)
  >- rw[form_functions_def,shift_form_def]
  >- (rw[form_functions_def,shift_form_def] >> SPOSE_NOT_THEN ASSUME_TAC >> 
      fs[GSYM MEMBER_NOT_EMPTY] >> fs[MEM_MAP,PULL_EXISTS] >> Cases_on `y'` (* 2 *)
     >- (fs[shift_term_def] >> metis_tac[MEMBER_NOT_EMPTY])
     >- (rfs[] >> fs[term_functions_def,shift_term_def] >> Cases_on `l' = []` >> fs[] (* 2 same *)>>
        first_x_assum drule >> rw[] >> qexists_tac `(n,LENGTH l')` >> rw[]))
  >- rw[form_functions_def,shift_form_def]
  >- rw[form_functions_def,shift_form_def]     
QED


(*theory for shifting ends*)

Theorem ultraproduct_sat:
!U I FMS x. countably_incomplete U I ==> 
   (∀i ff ll. i ∈ I ⇒ (FMS i).Fun ff ll ∈ (FMS i).Dom) ==> 
  !s. (!phi. phi IN s ==> form_functions phi = {} /\ (FV phi) DIFF N ⊆ {x}) ==> 
       (!ss. FINITE ss /\ ss ⊆ s ==> 
          ?σ. (IMAGE σ (univ(:num)) ⊆ (ultraproduct_folmodel U I FMS).Dom) /\ 
              (!n. n IN N ==> σ n = f n) /\
              (!phi. phi IN ss ==> feval (ultraproduct_folmodel U I FMS) σ phi)) ==>
      (?σ. (IMAGE σ (univ(:num)) ⊆ (ultraproduct_folmodel U I FMS).Dom) /\ 
           (!n. n IN N ==> σ n = f n)  /\ 
           (!phi. phi IN s ==> feval (ultraproduct_folmodel U I FMS) σ phi))
Proof
  rw[] >> drule countably_incomplete_chain >> rw[] >>
  fs[countably_incomplete_def] >> drule thm_A_19_ii >> rw[] >> 
  `(∀i ff ll. i ∈ I' ⇒ (FMS i).Fun ff ll ∈ (FMS i).Dom)` by cheat (* cheat!! to add the condition where Los applies*)
  `∃σ.
            IMAGE σ 𝕌(:num) ⊆ (ultraproduct_folmodel U I' FMS).Dom ∧
            (∀n. n ∈ N ⇒ σ n = f n) ∧
            ∀phi. phi ∈ s ⇒ {i | i ∈ I' ∧ feval (FMS i) (λx. CHOICE (σ x) i) phi} ∈ U`
   suffices_by (rw[] >> qexists_tac `σ` >> rw[] >> first_x_assum drule  >>
                metis_tac[ultraproduct_folmodel_Dom]) >> 
  (*cheat the suffices holds*)
  `?enum. BIJ enum (univ(:num)) s` by cheat (*countability of s, need Godel numbering*)
  qabbrev_tac `conj = PRIM_REC (enum 0) (\conjn n. fAND conjn (enum (n + 1)))` >> 
  qabbrev_tac `Jn = \n. {i | i IN I' /\ 
                        ?σ. IMAGE σ 𝕌(:num) ⊆ (ultraproduct_folmodel U I' FMS).Dom ∧
                            (∀n. n ∈ N ⇒ σ n = f n) /\
                            feval (FMS i) (λy. CHOICE (σ y) i) (fEXISTS x (conj n))}` >>
  (* use y to be the variable, avoid name clash with FV x*)
  qabbrev_tac `Xn = \n. (In n) ∩ (Jn n)` >>(* wrong, Jn should start with 0!*)
  `BIGINTER {Xn n | n IN (univ(:num))} = {}` by cheat (* because has In as subset *)
  `!i. i IN I' ==> ?ni. i IN (Xn ni) /\ 
                        !ns. ns > ni ==> i NOTIN (Xn ns)` by cheat >>
  (* since the definition of Jn is wrong this is cheated for the moment*) >>
  `!n. (Jn n) IN U` by cheat >>
  qabbrev_tac `Ni = \i. CHOICE {ni | i IN (Xn ni) /\ 
                        !ns. ns > ni ==> i NOTIN (Xn ns)}` >> 
  qabbrev_tac `ssn = \n. {enum m | m <= n}` >>
  `!n. FINITE (ssn n) /\ (ssn n) ⊆ s` by cheat >> 
  `?σ. IMAGE σ 𝕌(:num) ⊆ (ultraproduct_folmodel U I' FMS).Dom ∧
            (∀n. n ∈ N ⇒ σ n = f n) ∧
            ∀k. {i | i ∈ I' ∧ feval (FMS i) (λx. CHOICE (σ x) i) (enum k)} ∈ U` suffices_by cheat >>
 (* the above is because of the bijection*)
  `!M σ. feval M σ (fIMP (conj k) (enum k))` by cheat >>
  (* conj k implies a conjunct*)
  `!n. Xn n IN U` by cheat >> 
  `∃σ.
            IMAGE σ 𝕌(:num) ⊆ (ultraproduct_folmodel U I' FMS).Dom ∧
            (∀n. n ∈ N ⇒ σ n = f n) ∧
            ∀k.
                {i | i ∈ I' ∧ feval (FMS i) (λx. CHOICE (σ x) i) (conj k)} ∈
                U` suffices_by cheat >>
  `∃σ.
            IMAGE σ 𝕌(:num) ⊆ (ultraproduct_folmodel U I' FMS).Dom ∧
            (∀n. n ∈ N ⇒ σ n = f n) ∧
            ∀k. ?ks. ks IN U /\
                ks ⊆ {i | i ∈ I' ∧ feval (FMS i) (λx. CHOICE (σ x) i) (conj k)}` suffices_by cheat >>
  `∀k.
            ∃σ.
                IMAGE σ 𝕌(:num) ⊆ (ultraproduct_folmodel U I' FMS).Dom ∧
                (∀n. n ∈ N ⇒ σ n = f n) ∧
                 feval (ultraproduct_folmodel U I' FMS) σ (conj k)` by cheat >>
  (*apply asumption to conj <=> fin set satis assum 5*)
  `∀k.
            ∃σ.
                IMAGE σ 𝕌(:num) ⊆ (ultraproduct_folmodel U I' FMS).Dom ∧
                (∀n. n ∈ N ⇒ σ n = f n) ∧
                {i | i ∈ I' ∧ feval (FMS i) (λx. CHOICE (σ x) i) (conj k)} ∈ U` by cheat >>
  (* apply Los thm*)               
  qabbrev_tac `σn = \n. CHOICE {σ| IMAGE σ 𝕌(:num) ⊆ (ultraproduct_folmodel U I' FMS).Dom ∧
                                   (∀n. n ∈ N ⇒ σ n = f n) ∧
                                   feval (ultraproduct_folmodel U I' FMS) σ (conj n)}` >> 
  (*can choose such a σn according to existence in order to define the fp*)                           
  qabbrev_tac `fp = \i. if (Ni i) = 0 then CHOICE (FMS i).Dom
                     else (CHOICE ((σn n) x)) i` >>
  qabbrev_tac `fc = {g | Uequiv U I' (folmodels2Doms FMS) fp g}` >>
  qexists_tac `\n. if (n IN N) then (f n) else fc` >> rw[] (* 2 *)
  >- cheat (*because fc in codomain and A ⊆ codomain 
     !!!!! currently no assumption says this, need fix*)
  >- qexists_tac `Xn n` >> rw[] >> rw[SUBSET_DEF] >- cheat >- 
     `!s. CHOICE s IN s` by cheat (*cheat to see what happens because nothing is empty here*)
     fs[Abbr`Xn`] >> fs[Abbr`Jn`]
  

 
 cheat >> 
  (* this is according to Los thm, not give details because maybe the theorem can be fixed without the ugly assumption *)
  `∀ss.
            FINITE ss ∧ ss ⊆ s ⇒
            ∃σ.
                IMAGE σ 𝕌(:num) ⊆ (ultraproduct_folmodel U I' FMS).Dom ∧
                (∀n. n ∈ N ⇒ σ n = f n) ∧
                ∀phi. phi ∈ ss ⇒ {i | i ∈ I' ∧ feval (FMS i) (λx. CHOICE (σ x) i) phi} ∈ U`
   by cheat >> (* according to Los theorem *)
   `?δ. BIJ δ (univ(:num)) s` by cheat >>  (* here we only consider when s is countably infinite, the finite case is bording, the set is countably infinite because L is countable language, need Godel's numbering here *)
   (*
   qabbrev_tac `c = \i. CHOICE {a | (i IN X a) /\ (i NOTIN (X (a + 1)))}`
   qabbrev_tac `ff = \i. if (c i = 0) then CHOICE (FMS i).Dom else 
                             CHOICE {a | a IN (FMS i).Dom /\ 
                                         (?σ. (!n. n IN N ==> σ n = f n) /\
                                               feval (FMS i) σ phi) }`
(\i. if ((c i) = 0) then CHOICE (FMS i).Dom else
                         (CHOICE {a |?σ. (!n. n IN N ==> σ n = f n) /\
                                         (a IN (FMS i).Dom) /\ 
                                         (feval (FMS i) σ(|x |-> a|) (δ (c i)))}))`*)
 *) cheat
QED


Theorem ultraproduct_sat':
!U I MS x N f. countably_incomplete U I ==> 
  !s. (!phi. phi IN s ==> form_functions phi = {} /\ (FV phi) DIFF N ⊆ {x}) ==> 
       (!ss. FINITE ss /\ ss ⊆ s ==> 
          ?σ. (IMAGE σ (univ(:num)) ⊆ (mm2folm (ultraproduct_model U I MS)).Dom) /\ 
              (!n. n IN N ==> σ n = f n) /\
              (!phi. phi IN ss ==> feval (mm2folm (ultraproduct_model U I MS)) σ phi)) ==>
      (?σ. (IMAGE σ (univ(:num)) ⊆ (mm2folm (ultraproduct_model U I MS)).Dom) /\ 
           (!n. n IN N ==> σ n = f n)  /\ 
           (!phi. phi IN s ==> feval (mm2folm (ultraproduct_model U I MS)) σ phi))
Proof
  (*rw[] >> drule ultraproduct_sat >> rw[] >> fs[countably_incomplete_def] >>
  drule ultraproduct_comm_feval >> rw[] >> 
  `!σ phi FMS. feval (ultraproduct_folmodel U I' FMS) σ phi <=> 
    feval (mm2folm (ultraproduct_model U I' MS)) σ phi` by cheat
  (* assume compactible lemma applies must apply since no functions *)
  fs[] >> 
  `!FMS. (ultraproduct_folmodel U I' FMS).Dom = (mm2folm (ultraproduct_model U I' MS)).Dom` by cheat
  (* just by definition *) >> fs[] >> first_x_assum irule >> rw[] >> (* trivial *) cheat*)
  cheat (* confirmed this one can be implies by the above *)
QED


Theorem ultraproduct_sat'':
!U I MS x. countably_incomplete U I ==> 
   !A M' f. expansion (mm2folm (ultraproduct_model U I MS)) A M' f ==> 
  !s. (!phi. phi IN s ==>  (∀c. c ∈ form_functions phi ⇒ FST c ∈ count (CARD A) ∧ SND c = 0)
           /\ FV phi ⊆ {x}) ==> 
       (!ss. FINITE ss /\ ss ⊆ s ==> 
          ?σ. (IMAGE σ (univ(:num)) ⊆ (mm2folm (ultraproduct_model U I MS)).Dom) /\ 
              (*(!n. n IN N ==> σ n = f n) /\ *)
              (!phi. phi IN ss ==> feval M' σ phi)) ==>
      (?σ. (IMAGE σ (univ(:num)) ⊆ (mm2folm (ultraproduct_model U I MS)).Dom) /\ 
           (*(!n. n IN N ==> σ n = f n)  /\ *)
           (!phi. phi IN s ==> feval M' σ phi))
Proof
  (*rw[] >> drule ultraproduct_sat' >> rw[] >> drule expansion_shift_feval >> rw[] >>
  qabbrev_tac `sfs = {shift_form (CARD A) phi | phi IN s}` >> 
  `!phi. phi IN sfs ==> form_functions phi = ∅ ∧ (FV phi) DIFF (count (CARD A)) ⊆ {x}` by
     (rw[] (* 2 *)
     >- (fs[Abbr`sfs`] >> irule shift_form_functions_EMPTY >> rw[count_def] >> (*2 same*) metis_tac[])
     >- (fs[Abbr`sfs`] >> cheat (* cheated!! need a lemma saying about fv of shift add no more than N var *)))>>
  first_x_assum (qspecl_then [`MS`,`x`,`count (CARD A)`,`f`,`sfs`] assume_tac) >> 
  `∃σ.
            IMAGE σ 𝕌(:num) ⊆ (mm2folm (ultraproduct_model U I' MS)).Dom ∧
            (∀n. n ∈ count (CARD A) ⇒ σ n = f n) ∧
            ∀phi.
                phi ∈ sfs ⇒
                feval (mm2folm (ultraproduct_model U I' MS)) σ phi` suffices_by 
   (rw[] >> 
    (* suffices within suffices*)
   `∃σ.
            IMAGE σ 𝕌(:num) ⊆ (mm2folm (ultraproduct_model U I' MS)).Dom ∧
            ∀phi. phi ∈ s ⇒ 
            feval (mm2folm (ultraproduct_model U I' MS))
               (shift_valuation (CARD A) σ f) (shift_form (CARD A) phi)` suffices_by
    (rw[] >> qexists_tac `σ'` >> rw[] >> first_x_assum (qspec_then `phi` assume_tac) >> rfs[] >>
    first_x_assum (qspecl_then [`phi`,`σ'`] assume_tac) >> 
    `(feval M' σ' phi ⇔
         feval (mm2folm (ultraproduct_model U I' MS))
           (shift_valuation (CARD A) σ' f) (shift_form (CARD A) phi))` suffices_by metis_tac[] >>
    first_x_assum irule >> rw[] (* 2 two very trivial ones cheated!!!*) cheat)
   (*suffices within suffices end*)
   qexists_tac `\n. σ ((CARD A) + n)` >> rw[] (* 2 *)
   >- trivial cheat (*cheated!! vary trivial*)
   >- (first_x_assum (qspec_then `(shift_form (CARD A) phi)` assume_tac) >> 
      `shift_form (CARD A) phi ∈ sfs`  by cheat (* cheated! by definition*) >>
      first_x_assum drule >> rw[] >>
      `(shift_valuation (CARD A) (λn. σ (n + CARD A)) f) = σ` suffices_by metis_tac[] >>
      rw[FUN_EQ_THM,shift_valuation_def] >> Cases_on `x' < CARD A` >> rw[])) >>
   (* big suffices tac end *)
  first_x_assum irule
  `N = count (CARD A)` by cheat (*cheated!! because the sloppyness*) >> fs[] >>
  rw[] >> 
  `?s0. s0 ⊆ s /\ FINITE s0 /\ ss = IMAGE (shift_form (CARD A)) s0` by cheat >>
   (*cheated!! by definition of sfs*)
  first_x_assum (qspec_then `s0` assume_tac) >> rfs[] >> 
  qexists_tac `shift_valuation (CARD A) σ f` >> rw[] (* 3 *)
  >- cheat (*cheated! since f has image in dom*)
  >- rw[shift_valuation_def]
  >- `(∀c. c ∈ FC x' ⇒ c < CARD A) ∧
            IMAGE σ 𝕌(:num) ⊆ (ultraproduct_model U I' MS).frame.world` suffices_by metis_tac[]
     cheat (*cheated! just to check if the condition is ok *)
*) (* confirmed it relies on the lemmas and can be proved*)
QED

Theorem lemma_2_73:
  !U I MS M. 
         countably_incomplete U I ==>
             countably_saturated (mm2folm (ultraproduct_model U I MS))
Proof
  rw[countably_saturated_def,n_saturated_def,consistent_def,ftype_def,frealizes_def] >>
  drule ultraproduct_sat'' (*cheated key theorem*)>> rw[] >> first_x_assum drule >> rw[] >> 
  `∃σ.
                IMAGE σ 𝕌(:num) ⊆ (mm2folm (ultraproduct_model U I' MS)).Dom ∧
                ∀phi. phi ∈ G ⇒ feval M' σ phi` suffices_by
  (rw[] >> qexists_tac `σ x` >> rw[] (* 2 *)
   >- (`(mm2folm (ultraproduct_model U I' MS)).Dom = M'.Dom` by fs[expansion_def] >> 
      fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
   >- (rw[fsatis_def] (* 2 *)
      >- (rw[valuation_def] >> Cases_on `n' = x` >> rw[APPLY_UPDATE_THM] (* 2 *)
         >- (`(mm2folm (ultraproduct_model U I' MS)).Dom = M'.Dom` by fs[expansion_def] >> 
            fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
         >- (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]))
      >- (`feval M' σ phi <=> feval M' σ'⦇x ↦ σ x⦈ phi` suffices_by metis_tac[] >> 
         irule holds_valuation >> 
         `FV phi ⊆ {x}` by (fs[SUBSET_DEF] >> metis_tac[]) >> 
         fs[SUBSET_DEF,APPLY_UPDATE_THM]))) >>
  (*suffices tactic end*)
  first_x_assum irule >> 
  `(mm2folm (ultraproduct_model U I' MS)).Dom = M'.Dom` by fs[expansion_def] >> rw[] >>
  fs[fsatis_def] >> metis_tac[]
QED


Theorem lemma_2_73:
  !U I MS. 
         countably_incomplete U I ==>
         countably_saturated (mm2folm (ultraproduct_model U I MS))
Proof
  rw[countably_saturated_def,n_saturated_def,consistent_def,ftype_def,frealizes_def] >>
  drule expansion_shift_feval >> rw[] >>
  `∃w.
            w ∈ M'.Dom ∧
            ∀σ phi.
                IMAGE σ 𝕌(:num) ⊆ M'.Dom ∧ phi ∈ G ⇒ 
             feval (mm2folm (ultraproduct_model U I' MS))
               (shift_valuation (CARD A) σ⦇x ↦ w⦈ f) (shift_form (CARD A) phi)`
     suffices_by (rw[] >> qexists_tac `w` >> rw[] >> 
                 first_x_assum drule_all >> rw[] >> 
                 first_x_assum (qspecl_then [`phi`,`σ(|x |-> w|)`] assume_tac) >>
                 `IMAGE σ⦇x ↦ w⦈ 𝕌(:num) ⊆ (ultraproduct_model U I' MS).frame.world`
                    by cheat >> 
                 first_x_assum (qspec_then `phi` assume_tac) >> first_x_assum drule >>
                 rw[] >> first_x_assum drule_all >> rw[] >> rw[fsatis_def] >> cheat) >>
  (* from M' to mm2folm of a ultrapower model *)
  fs[countably_incomplete_def] >> fs[mm2folm_ultrapower_folmodel_comm] >>
  (* from mm2folm to ultraproductfolmodel in order to use Los thm*)
  fs[thm_A_19_ii] >>
  (* use Los thm *)
  `∀G0.
            FINITE G0 ∧ G0 ⊆ G ⇒
            ∃σ. IMAGE σ 𝕌(:num) ⊆ M'.Dom ∧ ∀phi. phi ∈ G0 ⇒
            feval (mm2folm (ultraproduct_model U I' MS))
               (shift_valuation (CARD A) σ f) (shift_form (CARD A) phi)`  by cheat
  (* change the assumption onto the unextended model *)
  >> qabbrev_tac `G' = {(shift_form (CARD A) phi) | phi IN G}` >>
     qabbrev_tac `sf = shift_form (CARD A)` >>
  (* change assumption into folmodel *)
  >- `∀G0.
            FINITE G0 ∧ G0 ⊆ G ⇒
            ∃σ.
                IMAGE σ 𝕌(:num) ⊆ M'.Dom ∧
                ∀phi.
                    phi ∈ G0 ⇒
                    feval (ultraproduct_folmodel U I' (λi. mm2folm (MS i)))
                      (shift_valuation (CARD A) σ f) (sf phi)` by cheat >>
     `∀G0.
            FINITE G0 ∧ G0 ⊆ G ⇒
            ∃σ.
                IMAGE σ 𝕌(:num) ⊆ M'.Dom ∧
                ∀phi.
                    phi ∈ G0 ==>
                {i | i IN I' /\ feval (mm2folm (MS i)) 
                                     (\x. CHOICE ((shift_valuation (CARD A) σ f) x) i) 
                                     (sf phi)} IN U
     ` by cheat >> 

QED



val _ = export_theory();
