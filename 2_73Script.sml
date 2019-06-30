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

Theorem mm2folm_well_formed:
  !M n l. M.frame.world <> {} ==> ((mm2folm M).Fun n l) IN (mm2folm M).Dom
Proof
  rw[mm2folm_def] >> metis_tac[CHOICE_DEF]
QED

Theorem ultraproduct_comm_feval:
  !phi U I MS. ultrafilter U I ==> form_functions phi = {} ==>
            !σ. IMAGE σ (univ(:num)) ⊆ ultraproduct U I (models2worlds MS) ==>
                (feval (mm2folm (ultraproduct_model U I MS)) σ phi <=>
                 feval (ultraproduct_folmodel U I (\i. mm2folm (MS i))) σ phi)
Proof
  Induct_on `phi` 
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
                (irule ultraproduct_same_eqclass >> rw[]
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
              >- qexists_tac `I'` >> rw[SUBSET_DEF])
           >- (drule ultraproduct_folmodel_well_formed >> rw[Abbr`sl`] >> 
              `ultraproduct U I' (models2worlds MS) = 
               (mm2folm (ultraproduct_model U I' MS)).Dom` by 
                metis_tac[mm2folm_ultraproduct_model_Dom] >> 
              rw[] >> irule termval_IN_Dom >> rw[](* 2 *)
              >- (`(ultraproduct_model U I' MS).frame.world <> {}` suffices_by 
                   metis_tac[mm2folm_well_formed] >> (* cheated! need assumption each MS i <> {}*)
                 cheat)
              >- metis_tac[mm2folm_ultraproduct_model_Dom])
           >- (qexists_tac `CHOICE sl` >> rw[] (* 2 *)
              >- (`sl <> {}` suffices_by metis_tac[CHOICE_DEF] >> cheat)
                 (*once proved sl in world then true by some lemma cheated!!*)
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
              cheat (* tedious! same as above *))
           >- (SPOSE_NOT_THEN ASSUME_TAC >> 
              `{i | i ∈ I' ∧ n = 0 ∧ (MS i).frame.rel (CHOICE sl1 i) (CHOICE sl2 i) ∧
                    CHOICE sl1 i ∈ (MS i).frame.world ∧
                    CHOICE sl2 i ∈ (MS i).frame.world} = {}` rw[Once EXTENSION] >>
              metis_tac[EMPTY_NOTIN_ultrafilter])
           >- (map_every qexists_tac [`CHOICE sl1`,`CHOICE sl2`] (*just tedious...*)>> cheat)
           >- (*  sl1 ∈ ultraproduct U I' (models2worlds MS) maybe really need lemmas...*) cheat
           >- cheat)
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

Theorem count_sat_folmodel_ultraproduct:
  !U I MS. ultrafilter U I ==> 
     countably_saturated (ultraproduct_folmodel U I (\i. mm2folm (MS i))) ==>
              countably_saturated (mm2folm (ultraproduct_model U I MS))
Proof
  rw[countably_saturated_def,n_saturated_def,consistent_def,ftype_def,frealizes_def] >>
  rpt (first_x_assum drule >> rw[]) >> 
  
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
  !s. (!phi. phi IN s ==> form_functions phi = {} /\ FV phi ⊆ {x}) ==> 
       (!ss. FINITE ss /\ ss ⊆ s ==> 
          ?σ. (IMAGE σ (univ(:num)) ⊆ (ultraproduct_folmodel U I FMS).Dom) /\ 
              (!n. n IN N ==> σ n = f n) /\
              (!phi. phi IN ss ==> feval (ultraproduct_folmodel U I FMS) σ phi)) ==>
      (?σ. (IMAGE σ (univ(:num)) ⊆ (ultraproduct_folmodel U I FMS).Dom) /\ 
           (!n. n IN N ==> σ n = f n)  /\ 
           (!phi. phi IN s ==> feval (ultraproduct_folmodel U I FMS) σ phi))
Proof
(*  rw[] >> drule countably_incomplete_chain >> rw[] >>
  fs[countably_incomplete_def] >> drule thm_A_19_ii >> rw[]
  `∃σ.
            IMAGE σ 𝕌(:num) ⊆ (ultraproduct_folmodel U I' FMS).Dom ∧
            (∀n. n ∈ N ⇒ σ n = f n) ∧
            ∀phi. phi ∈ s ⇒ {i | i ∈ I' ∧ feval (FMS i) (λx. CHOICE (σ x) i) phi} ∈ U`
   suffices_by cheat >> 
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
!U I MS x. countably_incomplete U I ==> 
  !s. (!phi. phi IN s ==> form_functions phi = {} /\ FV phi ⊆ {x}) ==> 
       (!ss. FINITE ss /\ ss ⊆ s ==> 
          ?σ. (IMAGE σ (univ(:num)) ⊆ (mm2folm (ultraproduct_model U I MS)).Dom) /\ 
              (!n. n IN N ==> σ n = f n) /\
              (!phi. phi IN ss ==> feval (mm2folm (ultraproduct_model U I MS)) σ phi)) ==>
      (?σ. (IMAGE σ (univ(:num)) ⊆ (mm2folm (ultraproduct_model U I MS)).Dom) /\ 
           (!n. n IN N ==> σ n = f n)  /\ 
           (!phi. phi IN s ==> feval (mm2folm (ultraproduct_model U I MS)) σ phi))
Proof
  (*rw[] >> drule ultraproduct_sat >> rw[] >>
  `!σ phi FMS. feval (ultraproduct_folmodel U I' FMS) σ phi <=> 
    feval (mm2folm (ultraproduct_model U I' MS)) σ phi` by cheat (* assume compactible lemma applies*)
  fs[] >> 
  `!FMS. (ultraproduct_folmodel U I' FMS).Dom = (mm2folm (ultraproduct_model U I' MS)).Dom` by cheat
  (* just by definition *) >> fs[] >> first_x_assum irule >> rw[] >> (* trivial *) cheat*)
  cheat
QED


Theorem expansion_shift_feval:
  !M A M' f. expansion (mm2folm M) A M' f ==>
             (*!phi σ. (∀c. c ∈ FC phi ⇒ c < CARD A) ==>
                  
                    IMAGE σ (univ(:num)) ⊆ M.frame.world ==> in order to assume when it applies, it should apply *)
                  !phi σ.  (feval M' σ phi <=> 
                    feval (mm2folm M) (shift_valuation (CARD A) σ f) (shift_form (CARD A) phi))
Proof
 cheat
  (*strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >> Induct_on `phi` (* 4 *)
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
  >- (rw[FC_def] >> rw[EQ_IMP_THM,shift_form_def] (* 2 *)
     >- (`(shift_valuation (CARD A) σ f)⦇n + CARD A ↦ a⦈ =
         (shift_valuation (CARD A) σ(|n |-> a|) f)` 
           by (rw[FUN_EQ_THM,shift_valuation_def] >> 
              Cases_on `x < CARD A` (* 2 *)
              >- (`x <> n + CARD A` by cheat >> fs[APPLY_UPDATE_THM])
              >- (Cases_on `x = n + CARD A` >> fs[APPLY_UPDATE_THM])) >>
        `feval (mm2folm M) (shift_valuation (CARD A) σ⦇n ↦ a⦈ f)
          (shift_form (CARD A) phi)` suffices_by metis_tac[] >> 
        first_x_assum (qspec_then `σ(|n |-> a|)` assume_tac) >> first_x_assum drule >>
        `IMAGE σ⦇n ↦ a⦈ 𝕌(:num) ⊆ M.frame.world /\ a IN M'.Dom` suffices_by metis_tac[] >>
        cheat)
     >- (first_x_assum (qspec_then `σ(|n |-> a|)` assume_tac) >> first_x_assum drule >>
        rw[] >> cheat)) *)
QED

(*

Theorem mm2folm_ultrapower_folmodel_termval:
 !t U I MS. 
    ultrafilter U I ==>
    !σ t. termval (mm2folm (ultraproduct_model U I MS)) σ t =
          termval (ultraproduct_folmodel U I (λi. mm2folm (MS i))) σ t
Proof
 completeInduct_on `term_size t` >> rw[] >> Cases_on `t'` >> rw[termval_def] >> 
 rw[mm2folm_def
QED



Theorem mm2folm_ultrapower_folmodel_comm:
  !phi U I MS. 
    ultrafilter U I ==>
    !σ. (feval (mm2folm (ultraproduct_model U I MS)) σ phi <=>
         feval (ultraproduct_folmodel U I (\i. mm2folm (MS i))) σ phi)
Proof
  Induct_on `phi` (* 4 *)
  >- rw[feval_def]
  >- rw[feval_def]
QED
*)


Theorem ultraproduct_sat'':
!U I MS x. countably_incomplete U I ==> 
   !A M' f. expansion (mm2folm (ultraproduct_model U I MS)) A M' f ==> 
  !s. (* (!phi. phi IN s ==> form_functions phi = {} /\ FV phi ⊆ {x}) ==> *)
       (!ss. FINITE ss /\ ss ⊆ s ==> 
          ?σ. (IMAGE σ (univ(:num)) ⊆ (mm2folm (ultraproduct_model U I MS)).Dom) /\ 
              (*(!n. n IN N ==> σ n = f n) /\ *)
              (!phi. phi IN ss ==> feval M' σ phi)) ==>
      (?σ. (IMAGE σ (univ(:num)) ⊆ (mm2folm (ultraproduct_model U I MS)).Dom) /\ 
           (*(!n. n IN N ==> σ n = f n)  /\ *)
           (!phi. phi IN s ==> feval M' σ phi))
Proof
  (*rw[] >> drule ultraproduct_sat' >> rw[] >> drule expansion_shift_feval >> rw[] >>*)
  (* need a lemma saying shift and σ n = f n is the same thing *) cheat
QED



Theorem lemma_2_73:
  !U I MS M. 
         countably_incomplete U I ==>
             countably_saturated (mm2folm (ultraproduct_model U I MS))
Proof
  rw[countably_saturated_def,n_saturated_def,consistent_def,ftype_def,frealizes_def] >>
  drule ultraproduct_sat'' >> rw[]
  (* checked match up *)
  `?In. (!n: num. In (n+1) ⊆ In n) /\
        (!n. (In n) IN U) /\
        BIGINTER {(In n)| n IN (univ (:num))} = {}` by cheat >>
  qabbrev_tac `upm = (mm2folm (ultraproduct_model U I' MS))` >> 
  `?k. BIJ p (univ(:num)) G` by cheat >>
  qabbrev_tac `s = \i. CHOICE {a | i IN (In a) /\ i NOTIN (In (a + 1))}`
  `∀G0s.
            FINITE G0s ∧ G0s ⊆ Gs ⇒
            ∃σ. IMAGE σ 𝕌(:num) ⊆ upm.Dom ∧ ∀phi. phi ∈ G0s ⇒ fsatis upm σ phi`
    by cheat >> 
  qabbrev_tac `upfm = (ultraproduct_folmodel U I' (\i. mm2folm M))` >> 
  `∀G0s.
            FINITE G0s ∧ G0s ⊆ Gs ⇒
            ∃σ.
                IMAGE σ 𝕌(:num) ⊆ upfm.Dom ∧
                ∀phi. phi ∈ G0s ⇒ fsatis upfm σ phi` by cheat >> 
  `∀n.
            ∃σ.
                IMAGE σ 𝕌(:num) ⊆ upfm.Dom ∧
                feval upfm σ (p n)` by cheat >> 
  `∃w.
            w ∈ upfm.Dom ∧
            ∀σ phi.
                IMAGE σ 𝕌(:num) ⊆ upfm.Dom ∧ phi ∈ Gs ⇒ fsatis upfm σ⦇x ↦ w⦈ phi`
   suffices_by cheat >>
  `∃w.
            w ∈ upfm.Dom ∧
            ∀σ n.
                IMAGE σ 𝕌(:num) ⊆ upfm.Dom ⇒ feval upfm σ⦇x ↦ w⦈ (p n)` 
   suffices_by cheat >>
   fs[thm_A_19_ii,Abbr`upfm`] >> 
   `∀n.
            ∃t. 
                {i | i ∈ I' ∧ !m. m <= n ==> feval (mm2folm M) (\n.t) (p m)} ∈
                U` by cheat
   `∃w.
            w ∈ upfm.Dom ∧
            ∀σ n.
                IMAGE σ 𝕌(:num) ⊆ upfm.Dom ⇒ feval upfm σ⦇x ↦ w⦈ (p n)` 
   suffices_by cheat >>
   `∃f.
 
            ∀n'.
                {i |
                 i ∈ I' ∧
                 feval (mm2folm M) (\n. f i) (p n')} ∈ U` suffices_by cheat >> 
  `∃f. ∀n' i. i ∈ I' ==> feval (mm2folm M) (\n. f i) (p n')` suffices_by cheat >> 
  
  qabbrev_tac 
  `fc = \i. CHOICE {w | (!m. m < (s i) ==> fsatis (mm2folm M) σ(|x |-> w|) (p m))}`
  qexists_tac `fc` >> rw[]



  qexists_tac `{f | Uequiv U I' (models2worlds MS) f fr}` >> rw[] >-
  cheat >- `?k. phi = p k` by cheat >> rw[] >> `fsatis σ'⦇x ↦ {f |
  Uequiv U I' (models2worlds MS) f fr}⦈ (p k) 
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
