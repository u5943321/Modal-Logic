open HolKernel Parse boolLib bossLib;

open chap1Theory chap2_1Theory chap2_2Theory chap2_3Theory chap2_4revisedTheory chap2_5Theory chap2_6Theory chap2_7Theory lemma2_73Theory IBCDNFrevisedTheory pred_setTheory pairTheory 

val _ = new_theory "prettyPrinting";

Theorem ppFINITE_BIGCONJ = REWRITE_RULE [GSYM CONJ_ASSOC, AND_IMP_INTRO] chap2_2Theory.FINITE_BIGCONJ

Theorem ppthm_2_74_half2 = REWRITE_RULE [GSYM CONJ_ASSOC, AND_IMP_INTRO] chap2_6Theory.thm_2_74_half2

Theorem ppPE_BIGCONJ = REWRITE_RULE [GSYM CONJ_ASSOC, AND_IMP_INTRO] chap2_7Theory.PE_BIGCONJ

Theorem ppPE_BIGDISJ = REWRITE_RULE [GSYM CONJ_ASSOC, AND_IMP_INTRO] chap2_7Theory.PE_BIGDISJ

Theorem ppultraproduct_sat'' = REWRITE_RULE [GSYM CONJ_ASSOC, AND_IMP_INTRO] lemma2_73Theory.ultraproduct_sat''

Theorem ppexercise_1_3_1 = REWRITE_RULE [GSYM CONJ_ASSOC, AND_IMP_INTRO] chap1Theory.exercise_1_3_1


Theorem pppeval_satis_strengthen':
!f M w. propform f /\ (prop_letters f ⊆ s) /\
        w IN M.frame.world ==>
        (satis M w f <=> peval (\a. w IN M.valt a /\ a IN s) f)
Proof
rw[] >> drule peval_satis_strengthen' >> fs[INTER_DEF] >> rw[] >>
first_x_assum drule_all >> fs[IN_DEF] >> 
`{x | M.valt x w ∧ s x}  = (λa. M.valt a w ∧ s a)` suffices_by fs[] >> 
rw[EXTENSION,EQ_IMP_THM]
QED



Theorem ppDU_def:
  DU (f, dom) = <| frame := <| world := {(i,w) | i IN dom /\ w IN (f i).frame.world};
                                 rel := \(i1,w1) (i2,w2). i1 = i2 /\
				                i1 IN dom /\
				                (f i1).frame.rel w1 w2 |>;
				valt := \v (i,w). (f i).valt v w |>
Proof
cheat
QED

Theorem pprooted_model_def:
!M x M'. rooted_model M x M' <=> x IN M'.frame.world /\
                                 (!a. a IN M.frame.world <=> (a IN M'.frame.world /\ (RTC (RESTRICT M'.frame.rel M'.frame.world)) x a)) /\
                                 (!w1 w2. w1 IN M.frame.world /\ w2 IN M.frame.world ==>
				   (M.frame.rel w1 w2 <=> (RESTRICT M'.frame.rel M'.frame.world) w1 w2)) /\
                                 (!p w. M.valt p w <=> M'.valt p w)
Proof
rw[rooted_model_def,IN_DEF]
QED

Theorem ppprop_2_15_corollary:
!M (w:'b) form. satis M w form ==>
  ?M' (s:'b list). tree M'.frame s /\ satis M' s form
Proof
rw[] >> drule prop_2_15_corollary >> metis_tac[]
QED


Theorem ppREL_CUS_def:
REL_CUS Σ M w1 w2 <=> w1 IN M.frame.world /\
                    w2 IN M.frame.world /\
                    (!phi. phi IN Σ ==> (satis M w1 phi <=> satis M w2 phi))
Proof
rw[REL_CUS_def]
QED

Theorem ppfiltration_def:
filtration M Σ L <=>
CUS Σ /\
(L.frame.world = EC_REP_SET Σ M) /\
(!w v. w IN M.frame.world /\ v IN M.frame.world /\ M.frame.rel w v ==> L.frame.rel (EC_REP Σ M w) (EC_REP Σ M v)) /\
(!w v. w IN M.frame.world /\ v IN M.frame.world /\ L.frame.rel (EC_REP Σ M w) (EC_REP Σ M v) ==> (!phi psi. (phi IN Σ /\ phi = DIAM psi /\ satis M v psi) ==> satis M w phi)) /\
(!p s. L.valt p s <=> (?w. s = EC_REP Σ M w /\ satis M w (VAR p)))
Proof
rw[filtration_def] >> metis_tac[]
QED

Theorem ppprop_2_38:
!Σ M L. FINITE Σ /\ filtration M Σ L ==> CARD (L.frame.world) <= 2 ** (CARD (Σ))
Proof
rw[] >> drule prop_2_38 >> metis_tac[]
QED

Theorem ppthm_2_39:
!phi. phi IN Σ ==> (!w. w IN M.frame.world /\ filtration M Σ L ==> (satis M w phi <=> satis L (EC_REP Σ M w) phi))
Proof
rw[] >> metis_tac[thm_2_39]
QED

Theorem ppREL_2_42_def:
    REL_2_42 Σ M w1 w2 = ?w. w IN M.frame.world /\ w1 = EC_CUS Σ M w /\
                         ?v. v IN M.frame.world /\ w2 = EC_CUS Σ M v /\
                         (!phi. (DIAM phi) IN Σ /\ satis M v (DISJ phi (DIAM phi)) ==> satis M w (DIAM phi))
Proof
rw[REL_2_42_def]
QED


Theorem ppequiv0_def:
     equiv0 (:α) f1 f2 <=> !M w:'a. satis M w f1 <=> satis M w f2
Proof
rw[equiv0_def]
QED

Theorem ppequiv0_DIAM:
 ∀f g μ. INFINITE 𝕌(:α) ⇒ (equiv0 (:α) (◇ f) (◇ g) ⇔ equiv0 (:α) f g)
Proof
rw[equiv0_DIAM]
QED

Theorem ppSUBMODEL_def:
∀M1 M2.
            SUBMODEL M1 M2 ⇔
            M1.frame.world ⊆ M2.frame.world ∧
            (∀w1.
                w1 ∈ M1.frame.world ⇒
                (∀v. M1.valt v w1 ⇔ M2.valt v w1)) ∧
            (∀w1 w2.
                    (w1 ∈ M1.frame.world /\ w2 IN M1.frame.world) ⇒
                    (M1.frame.rel w1 w2 ⇔ M2.frame.rel w1 w2))
Proof
rw[SUBMODEL_def] >> fs[IN_DEF] >> metis_tac[]
QED

Theorem ppGENSUBMODEL_def:
∀M1 M2.
            GENSUBMODEL M1 M2 ⇔
            SUBMODEL M1 M2 ∧
            ∀w1 w2.
                (w1 ∈ M1.frame.world /\
                w2 ∈ M2.frame.world ∧ M2.frame.rel w1 w2) ⇒
                    w2 ∈ M1.frame.world
Proof
rw[GENSUBMODEL_def] >> fs[IN_DEF] >> metis_tac[]
QED

Theorem pphom_def:
∀f M1 M2.
            hom f M1 M2 ⇔
            (∀w.
                w ∈ M1.frame.world ⇒
                f w ∈ M2.frame.world ∧
                (∀p. w ∈ M1.valt p ⇒ f w ∈ M2.valt p)) ∧
            (∀w v.  (w IN M1.frame.world /\
                    v ∈ M1.frame.world /\
                    M1.frame.rel w v) ⇒
                    M2.frame.rel (f w) (f v))
Proof
rw[hom_def] >> metis_tac[]
QED

Theorem ppstrong_hom_def:
∀f M1 M2.
            strong_hom f M1 M2 ⇔
            (∀w.
                w ∈ M1.frame.world ⇒
                f w ∈ M2.frame.world ∧
                (∀p. w ∈ M1.valt p ⇔ f w ∈ M2.valt p)) ∧
            (∀w v. (w IN M1.frame.world /\
                  v ∈ M1.frame.world) ⇒
                  (M1.frame.rel w v ⇔ M2.frame.rel (f w) (f v)))
Proof
rw[strong_hom_def] >> metis_tac[]
QED

Theorem ppsubforms_def:
(∀a. subforms (VAR a) = {VAR a}) ∧ subforms ⊥ = {⊥} ∧
        (∀f. subforms (¬f) = {¬f} ∪ subforms f) ∧
        (∀f1 f2.
             subforms (DISJ f1 f2) =
             {DISJ f1 f2} ∪ subforms f1 ∪ subforms f2) ∧
        ∀f. subforms (◇ f) = {◇ f} ∪ subforms f
Proof
rw[subforms_def,Once UNION_DEF,Once INSERT_DEF,EXTENSION,EQ_IMP_THM] >>
metis_tac[]
QED


Theorem pppeval_equiv0:
∀f1 f2.
            propform f1 ∧ propform f2 ∧ equiv0 μ f1 f2 ⇒
            (∀σ. peval σ f1 ⇔ peval σ f2)
Proof 
rw[] >> drule peval_equiv0 >> rw[] >> fs[equiv0_def]
QED

Theorem ppwffm_def:
 ∀M.
         wffm M ⇔
         ∀n0 l0. M.Fun n0 l0 ∈ M.Dom
Proof
cheat
QED


Theorem ppM_sat_def:
∀M.
            M_sat M ⇔
            ∀w Σ.
                (w ∈ M.frame.world /\
                fin_satisfiable_in Σ
                  {v | v ∈ M.frame.world ∧ M.frame.rel w v} M) ⇒
                satisfiable_in Σ {v | v ∈ M.frame.world ∧ M.frame.rel w v} M
Proof
rw[M_sat_def] >> metis_tac[]
QED

Theorem ppprop_2_54_DIST_TYPE:
∀M M' w w'.
            (M_sat M ∧ M_sat M' ∧ w ∈ M.frame.world ∧ w' ∈ M'.frame.world /\
            modal_eq M M' w w') ⇒
            bisim_world M M' w w'
Proof
rw[] >> metis_tac[prop_2_54_DIST_TYPE]
QED

Theorem ppcan_see_UNION:
can_see M (X ∪ Y) = (can_see M X) ∪ (can_see M Y)
Proof
rw[can_see_def,EXTENSION,EQ_IMP_THM] (* 6 *)
>> metis_tac[]
QED

Theorem ppexercise_2_5_5:
∀M u v.
       UE_rel M u v ⇔ (ultrafilter u M.frame.world ∧ ultrafilter v M.frame.world /\ {Y | only_see M Y ∈ u ∧ Y ⊆ M.frame.world} ⊆ v)
Proof
rw[EQ_IMP_THM] (* 4 *)
>- fs[UE_rel_def]
>- fs[UE_rel_def]
>- (`ultrafilter u M.frame.world /\ ultrafilter v M.frame.world`
     by metis_tac[UE_rel_def] >>
    metis_tac[exercise_2_5_5])
>- metis_tac[exercise_2_5_5]
QED


Theorem ppn_saturated_def:
∀M n.
            n_saturated M n ⇔
            ∀A M' G x f.
                (IMAGE f 𝕌(:num) ⊆ M.Dom /\ FINITE A ∧ CARD A ≤ n ∧ A ⊆ M.Dom ∧
                expansion M A M' f ∧
                (∀phi.
                     phi ∈ G ⇒ form_functions phi ⊆ {(c, 0) | c < CARD A}) ∧
                 ftype x G ∧
                consistent M' G) ⇒
                frealizes M' x G
Proof
rw[n_saturated_def,SUBSET_DEF,FST,SND,EQ_IMP_THM] (* 2 *)
>- (first_x_assum irule >> rw[] >>
   map_every qexists_tac [`A`,`f`] >> rw[] (* 2 *)
   >- (fs[FST] >> first_x_assum drule >> rw[] >> first_x_assum drule >> rw[] >>
      fs[FST])
   >- (first_x_assum drule >> rw[] >> first_x_assum drule >> rw[] >> fs[SND]))
>- (first_x_assum irule >> rw[] >>
    map_every qexists_tac [`A`,`f`] >> rw[] >>
    qexists_tac `FST x'` >> rw[] (* 2 *)
   >> first_x_assum drule >> rw[] >> first_x_assum drule >> rw[] >>
   Cases_on `x'` >> fs[FST,SND])
QED

Theorem ppthm_2_65_corollary:
∀M M' w w'.
         countably_saturated (mm2folm M) ∧ countably_saturated (mm2folm M') ∧
         w ∈ M.frame.world ∧ w' ∈ M'.frame.world ⇒
         (modal_eq M M' w w' <=>
         bisim_world M M' w w')
Proof
rw[EQ_IMP_THM] (* 2 *)
>- metis_tac[thm_2_65_corollary]
>- (rw[modal_eq_tau] >> metis_tac[thm_2_20,modal_eq_tau])
QED

Theorem ppultraproduct_rep_independence_lemma:
∀U I FMS σ.
            (ultrafilter U I /\
            valuation (ultraproduct_folmodel U I FMS) σ) ⇒
            ∀phi rv.
                (∀v. v ∈ FV phi ⇒ rv v ∈ σ v) ⇒
                ({i | i ∈ I ∧ feval (FMS i) (λx. CHOICE (σ x) i) phi} ∈ U ⇔
                 {i | i ∈ I ∧ feval (FMS i) (λv. rv v i) phi} ∈ U)
Proof
(*rw[] >> 
`IMAGE σ 𝕌(:num) ⊆ ultraproduct U I' (folmodels2Doms FMS)`
  suffices_by metis_tac[ultraproduct_rep_independence_lemma] >>
fs[IMAGE_DEF,SUBSET_DEF,valuation_def] >> fs[ultraproduct_folmodel_def] >>
metis_tac[]*) cheat
QED

Theorem pplemma_2_73:
∀U I MS.
            (countably_incomplete U I /\ 
            (∀i. i ∈ I ⇒ (MS i).frame.world ≠ ∅)) ⇒
            countably_saturated (mm2folm (ultraproduct_model U I MS))
Proof
metis_tac[lemma_2_73]
QED

Theorem ppcompactness_thm_L1tau:
!A. (INFINITE 𝕌(:α) /\
     (∀f. f ∈ A ⇒ L1tau f) ∧
         (∀ss.
              FINITE ss ∧ ss ⊆ A ⇒
              ∃M:α model σ. valuation M σ ∧ ∀ff. ff ∈ ss ⇒ feval M σ ff)) ⇒
         ∃M:α model σ. valuation M σ ∧ ∀f. f ∈ A ⇒ feval M σ f
Proof
(*rw[] >> drule compactness_thm_L1tau >> rw[]*) cheat
QED

Theorem ppcompactness_corollary_L1tau:
!A a. (INFINITE 𝕌(:α) /\ L1tau a /\
         (∀f. f ∈ A ⇒ L1tau f) ∧
         (∀M:α model σ. valuation M σ ⇒ (∀f. f ∈ A ⇒ feval M σ f) ⇒ feval M σ a)) ⇒
         ∃ss.
             FINITE ss ∧ ss ⊆ A ∧
             ∀M:α model σ. valuation M σ ⇒ (∀f. f ∈ ss ⇒ feval M σ f) ⇒ feval M σ a
Proof
(*rw[] >> drule compactness_corollary_L1tau >> rw[]*) cheat
QED

Theorem ppprop_2_3:
!i w f. i IN dom ==> (satis (f i) w phi <=> satis (DU (f, dom)) (i,w) phi)
Proof
rw[] >> `FST (i,w) IN dom` by fs[FST] >> drule prop_2_3 >> fs[FST,SND]
QED

Theorem ppprop_2_29_strengthen:
!s. FINITE s /\ INFINITE univ(:'b) ==> !n. FINITE (partition (equiv0 (μ:'b itself)) {f| DEG f <= n /\ prop_letters f ⊆ s})
Proof
rw[] >> drule prop_2_29_strengthen >> rw[] >> 
`{f | DEG f ≤ n ∧ ∀a. VAR a ∈ subforms f ⇒ a ∈ s} = 
{f | DEG f ≤ n ∧ prop_letters f ⊆ s}` suffices_by metis_tac[] >>
rw[EXTENSION,SUBSET_DEF] >> metis_tac[prop_letters_subforms]
QED

Theorem ppIMAGE_peval_singlton_strengthen:
!x form. x IN {f | propform f /\ prop_letters f ⊆ s}//e /\ form IN x ==>
IMAGE (λf. {σ | peval σ f} ∩ POW s) x = {{σ | (peval σ form)} INTER (POW s)}
Proof
rw[] >> 
`{f | propform f ∧ prop_letters f ⊆ s} = {f | propform f ∧ ∀a. VAR a ∈ subforms f ⇒ a ∈ s}` suffices_by metis_tac[IMAGE_peval_singlton_strengthen] >>
rw[EXTENSION,SUBSET_DEF] >> metis_tac[prop_letters_subforms]
QED

Theorem ppequiv0_peval_strengthen:
!f1 f2.
( propform f1 /\ propform f2 /\
(prop_letters f1 ⊆ s) /\
(prop_letters f2 ⊆ s))==>
(!σ. σ IN (POW s) ==> peval σ f1 = peval σ f2) ==> (!M w. satis M w f1 <=> satis M w f2)
Proof
rw[] >> drule equiv0_peval_strengthen >> rw[] >> 
fs[SUBSET_DEF] >> metis_tac[prop_letters_subforms]
QED

Theorem ppINJ_peval_partition_strengthen:
INJ
  (\eqc. ((IMAGE (λf. {σ| peval σ f} INTER (POW s)) eqc)))
  {f | propform f /\ prop_letters f ⊆ s}//e
  (POW (POW (POW s)))
Proof
rw[] >> 
`{f | propform f ∧ prop_letters f ⊆ s} = {f | propform f ∧ ∀a. VAR a ∈ subforms f ⇒ a ∈ s}` suffices_by metis_tac[INJ_peval_partition_strengthen] >>
rw[EXTENSION,SUBSET_DEF] >> metis_tac[prop_letters_subforms]
QED

Theorem ppDEG_IBC_strengthen:
∀x.
   DEG x ≤ n + 1 ∧ (prop_letters x ⊆ s) ⇔
   IBC x
     ({VAR v | v ∈ s} ∪
      {◇ psi | DEG psi ≤ n ∧ prop_letters psi ⊆ s})
Proof
(*rw[EQ_IMP_THM] (* 3 *)
>- (`{◇ psi | DEG psi ≤ n ∧ prop_letters psi ⊆ s} = {◇ psi | DEG psi ≤ n ∧ ∀a. VAR a ∈ subforms psi ⇒ a ∈ s} /\ (∀a. VAR a ∈ subforms x ⇒ a ∈ s)` 
     suffices_by metis_tac[DEG_IBC_strengthen] >>
   simp[EXTENSION] >> metis_tac[prop_letters_subforms,SUBSET_DEF])
>- (`{◇ psi | DEG psi ≤ n ∧ prop_letters psi ⊆ s} = {◇ psi | DEG psi ≤ n ∧ ∀a. VAR a ∈ subforms psi ⇒ a ∈ s}` 
     suffices_by metis_tac[DEG_IBC_strengthen] >>
    simp[EXTENSION] >> metis_tac[prop_letters_subforms,SUBSET_DEF])
>- (*(`{◇ psi | DEG psi ≤ n ∧ prop_letters psi ⊆ s} = {◇ psi | DEG psi ≤ n ∧ ∀a. VAR a ∈ subforms psi ⇒ a ∈ s} /\ (∀a. VAR a ∈ subforms x ⇒ a ∈ s)` 
     suffices_by metis_tac[DEG_IBC_strengthen,SUBSET_DEF] >> rw[] (*2 *)
   >- (simp[EXTENSION] >> metis_tac[prop_letters_subforms,SUBSET_DEF])
   >- (`{◇ psi | DEG psi ≤ n ∧ prop_letters psi ⊆ s} = 
        {◇ psi | DEG psi ≤ n ∧ ∀a. VAR a ∈ subforms psi ⇒ a ∈ s}`
       by (simp[EXTENSION] >> metis_tac[prop_letters_subforms,SUBSET_DEF]) >>
       fs[] >> metis_tac[DEG_IBC_strengthen])) have already proved it anyway*) cheat*) cheat
 
QED


Theorem ppDNF_OF_DISJ_equiv0_case4:
∀p1 p2 fs.
            (DISJ_OF0 p1 fs /\ DISJ_OF0 p2 fs) ⇒ ∃f. DISJ_OF0 f fs ∧ equiv0 μ f (DISJ p1 p2)
Proof
(*rw[] >> metis_tac[DNF_OF_DISJ_equiv0_case4]*) cheat
QED


Theorem pplist_demorgan:
∀l.
         l ≠ [] ⇒
         equiv0 μ (AND e (lit_list_to_form2 l))
           (lit_list_to_form2 (MAP (AND e) l))
Proof
cheat (* metis_tac[list_demorgan] *)
QED

Theorem ppDISJ_OF0_cset:
∀d fs.
         DISJ_OF0 d fs ⇒
         ∀fs0.
             fs ⊆ {c | CONJ_OF c fs0} ⇒
             ∃cs.
                 (∀c. c ∈ cs ⇒ is_lset c fs0) ∧
                 ∀M w.
                     w ∈ M.frame.world ⇒
                     (satis M w d ⇔ dsatis M w cs)
Proof
cheat (* rw[dsatis_def] >> drule DISJ_OF0_cset >> rw[] *)
QED

Theorem ppDNF_OF_cset:
∀d fs.
         DNF_OF d fs ⇒
         ∃cs.
             (∀c. c ∈ cs ⇒ is_lset c fs) ∧
             ∀M w.
                 w ∈ M.frame.world ⇒
                 (satis M w d ⇔ dsatis M w cs)
Proof
cheat (* rw[dsatis_def] >> drule DNF_OF_cset >> rw[] *)
QED
(*
Theorem ppthm_2_34:
∀M1 w1 phi.
         satis M1 w1 phi ⇒
         ∃M v. FINITE M.frame.world ∧ v ∈ M.frame.world ∧ satis M v phi
Proof
cheat
QED
*)

Theorem ppdsatis_ALL_POSSIBLE_VALUE = REWRITE_RULE [GSYM CONJ_ASSOC, AND_IMP_INTRO] IBCDNFrevisedTheory.dsatis_ALL_POSSIBLE_VALUE

Theorem ppis_lset_DNF_OF_EXISTS = REWRITE_RULE [GSYM CONJ_ASSOC, AND_IMP_INTRO] IBCDNFrevisedTheory.is_lset_DNF_OF_EXISTS

Theorem ppmm2folm_folm2mm_feval:
∀f σ M. L1tau f /\ valuation M σ ==>
           (feval (mm2folm (folm2mm M)) σ f ⇔ feval M σ f)
Proof
cheat
QED

Theorem ppprop_2_47_i:
!M w:'b phi (σ:num -> 'b) x:num. valuation (mm2folm M) σ
                       ==> (satis M (σ x) phi <=> fsatis (mm2folm M) σ (ST x phi))
Proof
cheat
QED

Theorem ppprop_2_47_i':
 !M w:'b phi σ x. valuation M σ
                       ==> (satis (folm2mm M) (σ x) phi <=> feval M σ (ST x phi))
Proof
cheat
QED


Theorem ppprop_2_47_i_alt:
!M w:'b phi σ. valuation (mm2folm M) σ
                       ==> (satis M (σ 1) phi <=> fsatis (mm2folm M) σ (ST_alt 1 phi)) /\
		           (satis M (σ 0) phi <=> fsatis (mm2folm M) σ (ST_alt 0 phi))
Proof
cheat
QED

Theorem ppST_BIGCONJ:
!s x.
   (FINITE s /\
    (!f. f IN s ==> ?phi. f = ST x phi)) ==>
       ?cf. (!M σ. valuation M σ ==>
                  (feval M σ cf <=>
                   (!f. f IN s ==> feval M σ f))) /\
           ?psi. cf = ST x psi
Proof
cheat
QED

Theorem ppexpansion_shift_feval:
  !M A M' f σ phi. (expansion (mm2folm M) A M' f /\ valuation (mm2folm M) σ /\
                    (form_functions phi ⊆ {(c1,0) | c1 < (CARD A)})) ==>
                    (feval M' σ phi <=>
                    feval (mm2folm M) (shift_valuation (CARD A) σ f) (shift_form (CARD A) phi))
Proof
cheat
QED
 
Theorem ppshift_FV:
∀phi s.
            FV phi ⊆ s ∧
            (form_functions phi ⊆ {(c1,0) | c1 < (CARD A)}) ⇒
            FV (shift_form (CARD A) phi) DIFF count (CARD A) ⊆
            {x + CARD A | x ∈ s}
Proof
cheat
QED

Theorem ppshift_form_functions_EMPTY:
∀phi.
            (form_functions phi ⊆ {(c1,0) | c1 < (CARD A)}) ⇒
            form_functions (shift_form (CARD A) phi) = ∅
Proof
cheat
QED

Theorem ppthm_A_19_i:
!t U I. ultrafilter U I ==>
          !σ FMS. (valuation (ultraproduct_folmodel U I FMS) σ /\
                   (!i. i IN I ==> wffm (FMS i))) ==>
          termval (ultraproduct_folmodel U I FMS) σ t =
          {f | Uequiv U I (folmodels2Doms FMS) f
               (\i. termval (FMS i) (\n. CHOICE (σ n) i) t)}
Proof
cheat
QED


Theorem ppthm_A_19_ii:
!U I phi. ultrafilter U I ==>
      !σ FMS. (valuation (ultraproduct_folmodel U I FMS) σ /\
               (!i. i IN I ==> wffm (FMS i))) ==>
                  (feval (ultraproduct_folmodel U I FMS) σ phi <=>
                  {i | i IN I /\ feval (FMS i) (\x. (CHOICE (σ x)) i) phi} IN U)
Proof
cheat
QED

Theorem ppultraproduct_suffices_rep:
!U I FMS rv phi.
  (ultrafilter U I /\
   (∀i. i IN I ==> wffm (FMS i)) /\
   (!i. valuation (FMS i) (\v. rv v i)) /\
   {i | i IN I /\ feval (FMS i) (\v. rv v i) phi} IN U) ==>
     feval (ultraproduct_folmodel U I FMS)
           (\v. {g | Uequiv U I (folmodels2Doms FMS) g (rv v)}) phi
Proof
cheat
QED



Theorem ppcorollary_A_21:
 !U I FMS FM σ.
   (ultrafilter U I /\
    (!i. i IN I ==> FMS i = FM) /\ wffm FM /\ valuation FM σ) ==>
     !phi.
           (feval FM σ phi <=>
            feval (ultraproduct_folmodel U I FMS)
            (\x. {g | Uequiv U I (folmodels2Doms FMS) g (\i. σ x)}) phi)
Proof
cheat
QED

Theorem ppultraproduct_comm_feval:
  !phi U I MS σ. (ultrafilter U I /\
                  L1tau phi /\
                   valuation (mm2folm (ultraproduct_model U I MS)) σ) ==>
                (feval (mm2folm (ultraproduct_model U I MS)) σ phi <=>
                 feval (ultraproduct_folmodel U I (\i. mm2folm (MS i))) σ phi)
Proof
cheat
(* rw[L1tau_def] >> drule ultraproduct_comm_feval >> rw[] *)
QED

Theorem ppultraproduct_comm_feval':
!phi U I MS σ.
  (ultrafilter U I /\
   L1tau phi /\
   (!i. i IN I ==> wffm (MS i)) /\
   valuation (ultraproduct_folmodel U I MS) σ)  ==>
     (feval (ultraproduct_folmodel U I MS) σ phi <=>
      feval (mm2folm (ultraproduct_model U I (λi. folm2mm (MS i)))) σ phi)
Proof
cheat
(* rw[] >> drule ultraproduct_comm_feval' >> rw[] >> *)
QED

Theorem ppultraproduct_mm2folm_folm2mm_comm_feval:
!M σ a I U.
   (FV a ⊆ {x} /\ L1tau a /\
    ultrafilter U I /\
    wffm M /\
    valuation M σ) ==>
    (feval M σ a <=>
     feval (mm2folm (ultraproduct_model U I (λi. folm2mm M)))
       (λx. {fw | Uequiv U I (models2worlds (λi. folm2mm M)) (λi. σ x) fw}) a)
Proof
cheat
QED

(*

Theorem holds_functions_predicates:
   M2.Dom = M1.Dom ∧ 
  (∀P zs. (P,LENGTH zs) ∈ form_predicates p ⇒ (M2.Pred P zs ⇔ M1.Pred P zs)) /\
  (∀f zs. (f,LENGTH zs) ∈ form_functions p ⇒ M2.Fun f zs = M1.Fun f zs) ⇒
      (∀v. feval M2 v p ⇔ feval M1 v p)
Proof
rw[] >> 
qabbrev_tac `M1' = <| Dom := M1.Dom ;
                      Fun := M2.Fun ;
                      Pred := M1.Pred |>` >>
`M2.Dom = M1'.Dom`
  by
   (fs[Abbr`M1'`]) >>
drule holds_predicates >> rw[] >>
`(feval M2 v p ⇔ feval M1' v p)` 
  by
   (first_x_assum irule >> rw[] (*  2*)
    >- fs[Abbr`M1'`,FUN_EQ_THM]
    >- fs[Abbr`M1'`]) >>
rw[] >> 
`M1'.Dom = M1.Dom` by fs[Abbr`M1'`] >>
drule holds_functions >> rw[] >>
first_x_assum irule >> rw[] (* 2 *)
>- fs[Abbr`M1'`]
>- fs[Abbr`M1'`,FUN_EQ_THM]
QED

*)



Theorem ppultraproduct_sat:
!U I FMS x f.
   (countably_incomplete U I /\
    valuation (ultraproduct_folmodel U I FMS) f /\
    (∀i. i ∈ I ⇒ wffm (FMS i))) ==>
  !s. (!phi. phi IN s ==> L1tau phi /\ (FV phi) DIFF N ⊆ {x}) ==>
       (!ss. FINITE ss /\ ss ⊆ s ==>
          ?σ. (valuation (ultraproduct_folmodel U I FMS) σ) /\
              (!n. n IN N ==> σ n = f n) /\
              (!phi. phi IN ss ==> feval (ultraproduct_folmodel U I FMS) σ phi)) ==>
       (?σ. valuation (ultraproduct_folmodel U I FMS) σ /\
            (!n. n IN N ==> σ n = f n)  /\
            (!phi. phi IN s ==> feval (ultraproduct_folmodel U I FMS) σ phi))
Proof
cheat
QED

Theorem pp2ultraproduct_sat:
!U I FMS x f s.
   (countably_incomplete U I /\
    valuation (ultraproduct_folmodel U I FMS) f /\
    (∀i. i ∈ I ⇒ wffm (FMS i)) /\
   (!phi. phi IN s ==> L1tau phi /\ (FV phi) DIFF N ⊆ {x})) ==>
       (!ss. (FINITE ss /\ ss ⊆ s) ==>
          ?σ. (valuation (ultraproduct_folmodel U I FMS) σ) /\
              (!n. n IN N ==> σ n = f n) /\
              (!phi. phi IN ss ==> feval (ultraproduct_folmodel U I FMS) σ phi)) ==>
       (?σ. valuation (ultraproduct_folmodel U I FMS) σ /\
            (!n. n IN N ==> σ n = f n)  /\
            (!phi. phi IN s ==> feval (ultraproduct_folmodel U I FMS) σ phi))
Proof
cheat
QED

Theorem pppreserved_under_sim_def:
 ∀phi.
         preserved_under_sim (:α) (:β) phi ⇔
         ∀M M' Z w:α w':β.
             w ∈ M.frame.world ∧ w' ∈ M'.frame.world ∧ sim Z M M' ∧ Z w w' ⇒
             satis M w phi ⇒
             satis M' w' phi
Proof
cheat
QED



Theorem ppultraproduct_sat':
!U I MS x N f.
     (countably_incomplete U I /\
      (!i. i IN I ==> (MS i).frame.world <> {}) /\
      (valuation (mm2folm (ultraproduct_model U I MS)) f)) ==>
  !s. (!phi. phi IN s ==> form_functions phi = {} /\ (FV phi) DIFF N ⊆ {x}) ==>
       (!ss. FINITE ss /\ ss ⊆ s ==>
          ?σ. (valuation (mm2folm (ultraproduct_model U I MS)) σ) /\
              (!n. n IN N ==> σ n = f n) /\
              (!phi. phi IN ss ==> feval (mm2folm (ultraproduct_model U I MS)) σ phi)) ==>
      (?σ. (valuation (mm2folm (ultraproduct_model U I MS)) σ) /\
           (!n. n IN N ==> σ n = f n)  /\
           (!phi. phi IN s ==> feval (mm2folm (ultraproduct_model U I MS)) σ phi))
Proof
cheat
QED


Theorem ppultraproduct_sat'':
!U I MS x A M' f.
      (countably_incomplete U I /\
       (∀i. i ∈ I ⇒ (MS i).frame.world ≠ ∅) /\
       expansion (mm2folm (ultraproduct_model U I MS)) A M' f /\
       (valuation (mm2folm (ultraproduct_model U I MS)) f)) ==>
  !s. (!phi. phi IN s ==>  (∀c. c ∈ form_functions phi ⇒ FST c ∈ count (CARD A) ∧ SND c = 0)
           /\ FV phi ⊆ {x}) ==>
       (!ss. FINITE ss /\ ss ⊆ s ==>
          ?σ. (valuation (mm2folm (ultraproduct_model U I MS)) σ) /\
              (!phi. phi IN ss ==> feval M' σ phi)) ==>
      (?σ. (valuation (mm2folm (ultraproduct_model U I MS)) σ) /\
           (!phi. phi IN s ==> feval M' σ phi))
Proof
cheat
QED


(*Theorem foo = SIMP_RULE bool_ss [PULL_FORALL, PULL_EXISTS] old_th*)

val _ = overload_on("Mw", “λM. M.frame.world”);

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Mw)"],
                  term_name = "Mw", paren_style = OnlyIfNecessary}

val _ = overload_on("Mr", “λM. M.frame.rel”);

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Mr)"],
                  term_name = "Mr", paren_style = OnlyIfNecessary}

val _ = overload_on("Mv", “λM. M.valt”);

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Mv)"],
                  term_name = "Mv", paren_style = OnlyIfNecessary}

val _ = overload_on("equiv", “equiv0”);

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix(NONASSOC, 450),
                  pp_elements = [TOK "(forces1)", TM,
                                 HardSpace 1,
                                 TOK "(forces2)", BreakSpace (1,2)],
                  term_name = "satis", paren_style = OnlyIfNecessary}
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix(NONASSOC, 450),
                  pp_elements = [TOK "(nforces1)", TM,
                                 HardSpace 1,
                                 TOK "(nforces2)", BreakSpace (1,2)],
                  term_name = "nsatis", paren_style = OnlyIfNecessary}

val _ = overload_on("nsatis", “λM w f. ~satis M w f”);

val _ = export_theory();
