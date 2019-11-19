open HolKernel Parse boolLib bossLib;

open chap1Theory chap2_1Theory chap2_2Theory chap2_3Theory chap2_4revisedTheory chap2_5Theory chap2_6Theory chap2_7Theory lemma2_73Theory IBCDNFrevisedTheory pred_setTheory pairTheory folLangTheory folModelsTheory ultraproductTheory

val _ = new_theory "prettyPrinting";

(* val _ = remove_termtok { tok = " *)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Infixr 200,
                  term_name = "==>",
                  pp_elements = [HardSpace 1, TOK "⇒", BreakSpace(1,2)]}


Theorem ppFINITE_BIGCONJ = REWRITE_RULE [GSYM CONJ_ASSOC, AND_IMP_INTRO] chap2_2Theory.FINITE_BIGCONJ

Theorem ppthm_2_74_half2 = REWRITE_RULE [GSYM CONJ_ASSOC, AND_IMP_INTRO] chap2_6Theory.thm_2_74_half2

Theorem ppPE_BIGCONJ = REWRITE_RULE [GSYM CONJ_ASSOC, AND_IMP_INTRO] chap2_7Theory.PE_BIGCONJ

Theorem ppPE_BIGDISJ = REWRITE_RULE [GSYM CONJ_ASSOC, AND_IMP_INTRO] chap2_7Theory.PE_BIGDISJ

Theorem ppultraproduct_sat'' = REWRITE_RULE [GSYM CONJ_ASSOC, AND_IMP_INTRO] lemma2_73Theory.ultraproduct_sat''

Theorem ppexercise_1_3_1 = REWRITE_RULE [GSYM CONJ_ASSOC, AND_IMP_INTRO] chap1Theory.exercise_1_3_1

Theorem ppprop_2_9:
∀M M' w w' f form.
            strong_hom f M M' ∧ w ∈ M.frame.world ∧
            SURJ f M.frame.world M'.frame.world ⇒
            modal_eq M M' w (f w)
Proof
rw[] >> drule prop_2_9 >> rw[]
QED



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



Theorem ppequiv0_def:
   !f1:chap1$form f2.  equiv0 (:β) f1 f2 <=> !M w:β. satis M w f1 <=> satis M w f2
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
            (∀w1 w2.
                    (w1 ∈ M1.frame.world /\ w2 IN M1.frame.world) ⇒
                    (M1.frame.rel w1 w2 ⇔ M2.frame.rel w1 w2)) /\
            (∀w1.
                w1 ∈ M1.frame.world ⇒
                (∀v. M1.valt v w1 ⇔ M2.valt v w1))
Proof
rw[SUBMODEL_def] >> fs[IN_DEF] >> metis_tac[]
QED


Theorem ppprop_2_31_half1:
∀M M' n w w' f.
             (nbisim M M' f n w w' /\
             DEG phi ≤ n) ⇒ (satis M w phi ⇔ satis M' w' phi)
Proof
metis_tac[prop_2_31_half1]
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
                BIJ f (count (CARD A)) A ∧
                (∀phi.
                     phi ∈ G ⇒ form_functions phi ⊆ {(c, 0) | c < CARD A}) ∧
                 ftype x G ∧
                consistent (expand M A f) G) ⇒
                frealizes (expand M A f) x G
Proof
rw[n_saturated_def,SUBSET_DEF,FST,SND,EQ_IMP_THM] (* 2 *)
>- (first_x_assum irule >> rw[] (* 2 *)
   >- (fs[FST] >> first_x_assum drule >> rw[] >> first_x_assum drule >> rw[] >>
      fs[FST])
   >- (first_x_assum drule >> rw[] >> first_x_assum drule >> rw[] >> fs[SND]))
>- (first_x_assum irule >> rw[] >>
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
∀U I FMS σ phi rv.
            ((ultrafilter U I /\
            valuation (ultraproduct_folmodel U I FMS) σ) /\

                (∀v. v ∈ FV phi ⇒ rv v ∈ σ v)) ⇒
                ({i | i ∈ I ∧ feval (FMS i) (λx. CHOICE (σ x) i) phi} ∈ U ⇔
                 {i | i ∈ I ∧ feval (FMS i) (λv. rv v i) phi} ∈ U)
Proof
rw[] >>
`IMAGE σ 𝕌(:num) ⊆ ultraproduct U I' (folmodels2Doms FMS)`
  suffices_by metis_tac[ultraproduct_rep_independence_lemma] >>
fs[IMAGE_DEF,SUBSET_DEF,valuation_def] >> fs[ultraproduct_folmodel_def] >>
metis_tac[]
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
              ∃M σ:num -> α. valuation M σ ∧ ∀ff. ff ∈ ss ⇒ feval M σ ff)) ⇒
         ∃M σ:num -> α. valuation M σ ∧ ∀f. f ∈ A ⇒ feval M σ f
Proof
rw[] >> drule compactness_thm_L1tau >> rw[]
QED

Theorem ppcompactness_corollary_L1tau:
!A a. (INFINITE 𝕌(:α) /\ L1tau a /\
         (∀f. f ∈ A ⇒ L1tau f) ∧
         (∀M σ:num -> α. valuation M σ ⇒ (∀f. f ∈ A ⇒ feval M σ f) ⇒ feval M σ a)) ⇒
         ∃ss.
             FINITE ss ∧ ss ⊆ A ∧
             ∀M σ:num -> α. valuation M σ ⇒ (∀f. f ∈ ss ⇒ feval M σ f) ⇒ feval M σ a
Proof
rw[] >> drule compactness_corollary_L1tau >> rw[]
QED


Theorem ppprop_2_29_strengthen:
!s. FINITE s /\ INFINITE univ(:'b) ==> !n. FINITE (partition (equiv0 (μ:'b itself)) {f| DEG f <= n /\ prop_letters f ⊆ s})
Proof
rw[] >> drule prop_2_29_strengthen >> rw[] >>
`{f | DEG f ≤ n ∧ ∀a. VAR a ∈ subforms f ⇒ a ∈ s} =
{f | DEG f ≤ n ∧ prop_letters f ⊆ s}` suffices_by metis_tac[] >>
rw[EXTENSION,SUBSET_DEF] >> metis_tac[prop_letters_subforms]
QED

Theorem ppprop_2_47_i:
!M w:'b phi (σ:num -> 'b) x:num. valuation (mm2folm M) σ
                       ==> (satis M (σ x) phi <=> fsatis (mm2folm M) σ (ST x phi))
Proof
rw[] >>
`IMAGE σ 𝕌(:num) ⊆ M.frame.world` suffices_by metis_tac[prop_2_47_i] >>
fs[valuation_def,IMAGE_DEF,SUBSET_DEF,mm2folm_def] >> metis_tac[]
QED

Theorem ppprop_2_47_i':
 !M w:'b phi σ x. valuation M σ
                       ==> (satis (folm2mm M) (σ x) phi <=> feval M σ (ST x phi))
Proof
rw[] >>
`IMAGE σ 𝕌(:num) ⊆ M.Dom` suffices_by metis_tac[prop_2_47_i'] >>
fs[valuation_def,IMAGE_DEF,SUBSET_DEF,mm2folm_def] >> metis_tac[]
QED


Theorem ppexpansion_shift_feval:
  !M A M' f σ phi. (BIJ f (count (CARD A)) A /\ valuation (mm2folm M) σ /\
                    (form_functions phi ⊆ {(c1,0) | c1 < (CARD A)})) ==>
                    (feval (expand (mm2folm M) A f) σ phi <=>
                    feval (mm2folm M) (shift_valuation (CARD A) σ f) (shift_form (CARD A) phi))
Proof
rw[] >> irule expansion_shift_feval >> rw[]
>- (fs[FC_def] >>
   qspec_then `phi` assume_tac FC_form_functions >>
   fs[SUBSET_DEF] >> first_x_assum drule >> rw[] >> Cases_on `c'` >> rw[] >>
   first_x_assum drule >> rw[]) >>
fs[mm2folm_def,valuation_def,IMAGE_DEF,SUBSET_DEF] >> metis_tac[]
QED


Theorem ppthm_A_19_i:
!t U I σ FMS. (ultrafilter U I /\
               (valuation (ultraproduct_folmodel U I FMS) σ /\
                   (!i. i IN I ==> wffm (FMS i)))) ==>
          termval (ultraproduct_folmodel U I FMS) σ t =
          {f | Uequiv U I (folmodels2Doms FMS) f
               (\i. termval (FMS i) (\n. CHOICE (σ n) i) t)}
Proof
rw[] >> drule thm_A_19_i >> rw[] >> first_x_assum irule >>
 fs[IMAGE_DEF,valuation_def,wffm_def,SUBSET_DEF,ultraproduct_folmodel_def] >>
metis_tac[]
QED


Theorem ppthm_A_19_ii:
!U I phi σ FMS. (ultrafilter U I /\
                 (valuation (ultraproduct_folmodel U I FMS) σ) /\
                 (!i. i IN I ==> wffm (FMS i))) ==>
                  (feval (ultraproduct_folmodel U I FMS) σ phi <=>
                  {i | i IN I /\ feval (FMS i) (\x. (CHOICE (σ x)) i) phi} IN U)
Proof
rw[] >> drule thm_A_19_ii >> rw[] >> first_x_assum irule >>
 fs[IMAGE_DEF,valuation_def,wffm_def,SUBSET_DEF,ultraproduct_folmodel_def] >>
metis_tac[]
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
rw[] >> drule ultraproduct_suffices_rep >> rw[] >> first_x_assum irule >>
fs[valuation_def,wffm_def] >> metis_tac[]
QED



Theorem ppcorollary_A_21:
 !U I FMS FM σ phi.
   (ultrafilter U I /\
    (!i. i IN I ==> FMS i = FM) /\ wffm FM /\ valuation FM σ) ==>
     (feval FM σ phi <=>
            feval (ultraproduct_folmodel U I FMS)
            (\x. {g | Uequiv U I (folmodels2Doms FMS) g (\i. σ x)}) phi)
Proof
rw[] >> drule corollary_A_21 >> rw[valuation_def,IMAGE_DEF,SUBSET_DEF] >>
fs[wffm_def] >> fs[valuation_def] >> first_x_assum irule >> metis_tac[]
QED

Theorem ppultraproduct_comm_feval:
  !phi U I MS σ.
 (ultrafilter U I /\
         form_functions phi = ∅ /\
         valuation (mm2folm (ultraproduct_model U I MS)) σ) ⇒
             (feval (mm2folm (ultraproduct_model U I MS)) σ phi ⇔
              feval (ultraproduct_folmodel U I (λi. mm2folm (MS i))) σ phi)
Proof
rw[] >> drule ultraproduct_comm_feval >>
strip_tac >>
rw[] >>
`IMAGE σ 𝕌(:num) ⊆ ultraproduct U I' (models2worlds MS)` suffices_by metis_tac[] >>
rw[IMAGE_DEF,SUBSET_DEF] >> fs[valuation_def,ultraproduct_model_def,mm2folm_def]
QED

Theorem ppprop_2_31_half1:
∀M M' n w w' f.
            (nbisim M M' f n w w' /\
            DEG phi ≤ n) ⇒ (satis M w phi ⇔ satis M' w' phi)
Proof
metis_tac[prop_2_31_half1]
QED

Theorem ppultraproduct_sat:
!U I FMS x f s.
   (countably_incomplete U I /\
    valuation (ultraproduct_folmodel U I FMS) f /\
    (∀i. i ∈ I ⇒ wffm (FMS i)) /\
   (!phi. phi IN s ==> L1tau phi /\ (FV phi) DIFF N ⊆ {x}) /\
       (!ss. (FINITE ss /\ ss ⊆ s) ==>
          ?σ. (valuation (ultraproduct_folmodel U I FMS) σ) /\
              (!n. n IN N ==> σ n = f n) /\
              (!phi. phi IN ss ==> feval (ultraproduct_folmodel U I FMS) σ phi))) ==>
       (?σ. valuation (ultraproduct_folmodel U I FMS) σ /\
            (!n. n IN N ==> σ n = f n)  /\
            (!phi. phi IN s ==> feval (ultraproduct_folmodel U I FMS) σ phi))
Proof
rw[valuation_def] >> drule ultraproduct_sat >> rw[] >>
`∃σ.
                IMAGE σ 𝕌(:num) ⊆ (ultraproduct_folmodel U I' FMS).Dom ∧
                (∀n. n ∈ N ⇒ σ n = f n) ∧
                ∀phi. phi ∈ s ⇒ feval (ultraproduct_folmodel U I' FMS) σ phi`
suffices_by
  (rw[] >> qexists_tac `σ` >> rw[] >> fs[IMAGE_DEF,SUBSET_DEF] >>
   fs[ultraproduct_folmodel_def] >> metis_tac[]) >>
first_x_assum irule >> rw[]
>- fs[wffm_def]
>- (qexists_tac `x` >> fs[L1tau_def])
>- (`∃σ.
                (∀n. σ n ∈ (ultraproduct_folmodel U I' FMS).Dom) ∧
                (∀n. n ∈ N ⇒ σ n = f n) ∧
                ∀phi. phi ∈ ss ⇒ feval (ultraproduct_folmodel U I' FMS) σ phi`
     suffices_by
       (rw[] >> first_x_assum drule_all >> strip_tac >> qexists_tac `σ` >>
        rw[] >> rw[IMAGE_DEF,SUBSET_DEF] >> fs[valuation_def]) >>
   metis_tac[])
>- (rw[IMAGE_DEF,SUBSET_DEF] >> fs[ultraproduct_folmodel_def])
QED

Theorem pppreserved_under_sim_def:
 ∀phi:chap1$form.
         preserved_under_sim (:α) (:β) phi ⇔
         ∀M M' Z w:α w':β.
             (w ∈ M.frame.world ∧ w' ∈ M'.frame.world ∧ sim Z M M' ∧ Z w w' /\
             satis M w phi) ⇒
             satis M' w' phi
Proof
metis_tac[preserved_under_sim_def]
QED

(*
Theorem ppthm_2_68_half1:
∀a x.
            (INFINITE 𝕌(:α) /\
            invar4bisim x (:(num -> α) -> bool) (:(num -> α) -> bool) a) ⇒
            ∃(phi:num chap1$form). ∀M v:num -> α. valuation M v ⇒ (feval M v a ⇔ feval M v (ST x phi))

Proof
rw[] >> drule thm_2_68_half1 >>  metis_tac[]
QED
*)

Theorem ppthm_2_68_half1:
∀a x.
            (INFINITE 𝕌(:α) /\
            invar4bisim x (:(num -> α) -> bool) (:(num -> α) -> bool) a) ⇒
            ∃(phi:chap1$form). feq (:α) a (ST x phi)

Proof
rw[] >> drule thm_2_68_half1 >>  rw[feq_def] >> metis_tac[]
QED




Theorem ppthm_2_78_half2:
(INFINITE 𝕌(:β) /\
preserved_under_sim (:(β -> bool) -> bool) (:(β -> bool) -> bool) phi) ⇒ ∃phi0:chap1$form. equiv0 (:β) phi phi0 ∧ PE phi0
Proof
metis_tac[thm_2_78_half2]
QED


Theorem ppL1tau_mm2folm_folm2mm_comm_feval:
 (L1tau f/\ valuation M v) ⇒
                (feval (mm2folm (folm2mm M)) v f ⇔ feval M v f)
Proof
metis_tac[L1tau_mm2folm_folm2mm_comm_feval]
QED

Theorem pptree_no_loop:
∀s r t0 t. (tree s r /\ (RESTRICT s.rel s.world)⁺ t0 t) ⇒ t0 ≠ t
Proof
metis_tac[tree_no_loop]
QED

Theorem pptree_height_rel_lemma:
∀M x w v.
        (tree M.frame x /\
        w ∈ M.frame.world ∧ height M x M w = n /\
        M.frame.rel w v ∧ v ∈ M.frame.world) ⇒
                    height M x M v = n + 1
Proof
metis_tac[tree_height_rel_lemma]
QED

Theorem pplemma_2_33:
∀M x M' k w.
            (rooted_model M x M'/\ w ∈ (hrestriction M x M' k).frame.world) ⇒
                ∃f.
                    nbisim (hrestriction M x M' k) M f (k − height M x M' w)
                      w w
Proof
metis_tac[lemma_2_33]
QED


Theorem ppLos_modal_thm:
∀U J Ms phi fc.
            (ultrafilter U J /\
                fc ∈ (ultraproduct_model U J Ms).frame.world) ⇒
                (satis (ultraproduct_model U J Ms) fc phi ⇔
                 ∃f. f ∈ fc ∧ {i | i ∈ J ∧ satis (Ms i) (f i) phi} ∈ U)
Proof
metis_tac[Los_modal_thm]
QED

Theorem ppexercise_2_7_1:
∀M M' w w'.
            (M_sat M ∧ M_sat M' ∧ w ∈ M.frame.world ∧ w' ∈ M'.frame.world /\
             (∀phi. PE phi ⇒ satis M w phi ⇒ satis M' w' phi)) ⇒
            ∃Z. sim Z M M' ∧ Z w w'
Proof
metis_tac[exercise_2_7_1]
QED

Theorem ppmodal_compactness_thm:
(INFINITE 𝕌(:α) /\ (∀ss:chap1$form -> bool.
                 FINITE ss ∧ ss ⊆ s ⇒
                 ∃M w:α. w ∈ M.frame.world ∧ ∀f. f ∈ ss ⇒ satis M w f)) ⇒
            ∃M w:α. w ∈ M.frame.world ∧ ∀f. f ∈ s ⇒ satis M w f
Proof
metis_tac[modal_compactness_thm]
QED


Theorem pphrestriction_def:
∀M x M' n.
            hrestriction M x M' n =
            <|frame :=
                <|world := {w | w ∈ M.frame.world ∧ height M x M' w ≤ n};
                  rel := M.frame.rel|>;
              valt := M.valt|>
Proof
rw[hrestriction_def,FUN_EQ_THM]
QED

Theorem ppmodal_compactness_corollary:
INFINITE 𝕌(:α) /\
        (∀M w:α.
                 w ∈ M.frame.world ⇒ (∀f. f ∈ s ⇒ satis M w f) ⇒ satis M w a) ⇒
            ∃ss:chap1$form -> bool.
                FINITE ss ∧ ss ⊆ s ∧
                ∀M w:α.
                    w ∈ M.frame.world ⇒
                    (∀f. f ∈ ss ⇒ satis M w f) ⇒
                    satis M w a
Proof
metis_tac[modal_compactness_corollary]
QED


val UE'_def = Define`
  UE' M = <| frame := <| world := {u | ultrafilter u M.frame.world};
                        rel :=  \u v.
            (ultrafilter u M.frame.world ∧ ultrafilter v M.frame.world ∧
            ∀X. X ∈ v ⇒ can_see M X ∈ u) |>;
            valt := \p v. (ultrafilter v M.frame.world /\
            {w | w IN M.frame.world /\  M.valt p w } IN v)|>`;


Theorem ppultraproduct_comm_feval':
∀phi U I MS σ.
         (ultrafilter U I /\
         L1tau phi /\
         (∀i. i ∈ I ⇒ wffm (MS i)) /\
          IMAGE σ 𝕌(:num) ⊆ ultraproduct U I (folmodels2Doms MS)) ⇒
             (feval (ultraproduct_folmodel U I MS) σ phi ⇔
              feval (mm2folm (ultraproduct_model U I (λi. folm2mm (MS i)))) σ
                phi)
Proof
rw[] >> irule ultraproduct_comm_feval' >> rw[] >> fs[wffm_def]
QED

Theorem ppL1tau_ultraproduct_mm2folm_folm2mm_comm_feval:
L1tau a ∧ FV a ⊆ {x} ∧ ultrafilter U I ∧ valuation M σ ⇒
            (feval M σ a ⇔
             feval (mm2folm (ultraproduct_model U I (λi. folm2mm M)))
               (λv.
                    {fw |
                     Uequiv U I (models2worlds (λi. folm2mm M)) (λi. σ v) fw})
               a)
Proof
metis_tac[L1tau_ultraproduct_mm2folm_folm2mm_comm_feval]
QED

val _ = overload_on("Mw", “λM. M.frame.world”);

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Mw)"],
                  term_name = "Mw", paren_style = OnlyIfNecessary}

val _ = overload_on("Mr", “\M. M.frame.rel”);

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
                                         TOK "(forces2)", BreakSpace (1,2)],
                          term_name = "satis", paren_style = OnlyIfNecessary}
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix(NONASSOC, 450),
                  pp_elements = [TOK "(nforces1)", TM,
                                 TOK "(nforces2)", BreakSpace (1,2)],
                  term_name = "nsatis", paren_style = OnlyIfNecessary}

val _ = overload_on("nsatis", “λM w f. ~satis M w f”);

val _ = app clear_overloads_on ["◇", "□"]

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Prefix 900, pp_elements = [TOK "◇"],
                  term_name = "DIAM", paren_style = OnlyIfNecessary}
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Prefix 900, pp_elements = [TOK "□"],
                  term_name = "BOX", paren_style = OnlyIfNecessary}


Overload UPM = ``\U MS. ultraproduct_folmodel U (J:α -> bool) MS``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(UPM1)", TM, TOK "(UPM2)"],
                  term_name = "UPM", paren_style = OnlyIfNecessary}


Overload UPMN = ``\U MS. ultraproduct_folmodel U (J:num -> bool) MS``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(UPMN1)", TM, TOK "(UPMN2)"],
                  term_name = "UPMN", paren_style = OnlyIfNecessary}


Overload myequiv = ``\f1 ty f2. equiv0 ty f1 f2``


val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(meq1)", TM, TOK "(meq2)"],
                  term_name = "myequiv", paren_style = OnlyIfNecessary}


Overload myfeq = ``\f1 ty f2. feq ty f1 f2``


val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [HardSpace 2, TOK "(mfeq1)", TM, TOK "(mfeq2)", BreakSpace (2,0)],
                  term_name = "myfeq", paren_style = OnlyIfNecessary}




Overload upr = ``\f U A g. Uequiv U (J: α -> bool) A f g``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(upr1)", TM, TOK "(upr2)",TM, TOK "(upr3)"],
                  term_name = "upr", paren_style = OnlyIfNecessary}

Overload uprr = ``\U A. Uequiv U (J: α -> bool) A``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix,
                  pp_elements = [TOK "(uprr1)", TM, TOK "(uprr2)",TM, TOK "(uprr3)"],
                  term_name = "uprr", paren_style = OnlyIfNecessary}

Overload uprn = ``\f U A g. Uequiv U (J: num -> bool) A f g``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(uprn1)", TM, TOK "(uprn2)",TM, TOK "(uprn3)"],
                  term_name = "uprn", paren_style = OnlyIfNecessary}

Overload uprrn = ``\U A. Uequiv U (J: num -> bool) A``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix,
                  pp_elements = [TOK "(uprrn1)", TM, TOK "(uprrn2)",TM, TOK "(uprrn3)"],
                  term_name = "uprrn", paren_style = OnlyIfNecessary}


Overload pt = ``\s r.partition r s``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (LEFT, 500),
                  pp_elements = [TOK "(ptt)"],
                  term_name = "pt", paren_style = OnlyIfNecessary}
(*
Overload cp = ``\J A. Cart_prod (J:α -> bool)  A``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(cp1)", TM, TOK "(cp2)", TM, TOK "(cp3)"],
                  term_name = "cp", paren_style = OnlyIfNecessary}
*)

Overload disj = ``\f1 f2. DISJ f1 f2``
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(disj)"],
                  term_name = "disj", paren_style = OnlyIfNecessary}

Overload fdisj = ``\f1 f2. fDISJ f1 f2``
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(fdisj)"],
                  term_name = "fdisj", paren_style = OnlyIfNecessary}

Overload fimp = ``\f1 f2. IMP (f1: folLang$form) f2``
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(fimp)"],
                  term_name = "fimp", paren_style = OnlyIfNecessary}


Overload ad = ``\f1 f2. AND f1 f2``
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(ad)"],
                  term_name = "ad", paren_style = OnlyIfNecessary}


Overload fad = ``\f1 f2. fAND f1 f2``
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(fad)"],
                  term_name = "fad", paren_style = OnlyIfNecessary}


Overload rst = ``\r s. RESTRICT r s``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(rst1)", TM, TOK "(rst2)", TM, TOK "(rst3)"],
                  term_name = "rst", paren_style = OnlyIfNecessary}

Overload mdeq = ``\M1 w1 M2 w2. modal_eq M1 M2 w1 w2``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(mdeq1)", TM, TOK "(mdeq2)", TM, TOK "(mdeq3)"],
                  term_name = "mdeq", paren_style = OnlyIfNecessary}


Overload gsm = ``\M1 M2. GENSUBMODEL M1 M2``
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(gsm)"],
                  term_name = "gsm", paren_style = OnlyIfNecessary}


Overload hom = ``\M1 f M2. hom f M1 M2``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(hom1)", TM, TOK "(hom2)"],
                  term_name = "hom", paren_style = OnlyIfNecessary}


Overload bisim' = ``\M1 Z M2. bisim Z M1 M2``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(bisim1)", TM, TOK "(bisim2)"],
                  term_name = "bisim'", paren_style = OnlyIfNecessary}


Overload bw = ``\M1 w1 M2 w2. bisim_world M1 M2 w1 w2``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(bw1)", TM, EndInitialBlock(PP.CONSISTENT,0), TOK "(bw2)",
                                 BeginFinalBlock(PP.CONSISTENT,0), TM, TOK "(bw3)"],
                  term_name = "bw", paren_style = OnlyIfNecessary}

Overload nbw = ``\M1 w1 f n M2 w2. nbisim M1 M2 f n w1 w2``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(nbw1)", TM, TOK "(nbw2)", TM, TOK "(nbw3)",TM, TOK "(nbw4)",TM, TOK "(nbw5)"],
                  term_name = "nbw", paren_style = OnlyIfNecessary}

Overload cs = ``\M X. can_see M (X: α -> bool)``
Overload cs = ``\M X. can_see M (X: β -> bool)``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(cs1)", TM, TOK "(cs2)",TM, TOK"(cs3)"],
                  term_name = "cs", paren_style = OnlyIfNecessary}



Overload os = ``\M X. only_see M (X:α -> bool) ``
Overload os = ``\M X. only_see M (X:β -> bool) ``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(os1)", TM, TOK "(os2)",TM, TOK "(os3)"],
                  term_name = "os", paren_style = OnlyIfNecessary}

Overload uer = ``\M. UE_rel M``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(uer1)", TM, TOK "(uer2)"],
                  term_name = "uer", paren_style = OnlyIfNecessary}

Overload ue = ``\M. UE M``
Overload ue = ``\M. UE' M``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(ue1)", TM, TOK "(ue2)"],
                  term_name = "ue", paren_style = OnlyIfNecessary}

Overload pf = ``\w s. principle_UF w s``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(pf1)", TM, TOK "(pf2)", TM, TOK "(pf3)"],
                  term_name = "pf", paren_style = OnlyIfNecessary}

Overload sim = ``\M1 Z M2. sim Z M1 M2``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(sim1)", TM, TOK "(sim2)"],
                  term_name = "sim", paren_style = OnlyIfNecessary}

Overload fev = ``\M σ f. feval M σ f``



val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                          fixity = Infix(NONASSOC, 450),
                          pp_elements = [TOK "(fev1)", TM,
                                         TOK "(fev2)", BreakSpace (1,2)],
                          term_name = "fev", paren_style = OnlyIfNecessary}

Overload bmi = ``\M1 f M2. bounded_mor_image f M1 M2``


val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(bmi1)", TM, TOK "(bmi2)"],
                  term_name = "bmi", paren_style = OnlyIfNecessary}

Overload fPred = “\a l. Pred a l”


val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix,
                  pp_elements = [TOK "(M3)"],
                  term_name = "M3", paren_style = OnlyIfNecessary}

Overload st = ``\x. ST x``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix,
                  pp_elements = [TOK "(st1)", TM, TOK "(st2)"],
                  term_name = "st", paren_style = OnlyIfNecessary}



Overload fst = ``\M σ f. fsatis M σ f``



val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                          fixity = Infix(NONASSOC, 450),
                          pp_elements = [TOK "(fst1)", TM,
                                         TOK "(fst2)", BreakSpace (1,2)],
                          term_name = "fst", paren_style = OnlyIfNecessary}


Overload UPMM = ``\U MS. ultraproduct_model U (J:α -> bool) MS``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(UPMM1)", TM, TOK "(UPMM2)"],
                  term_name = "UPMM", paren_style = OnlyIfNecessary}

Overload UPMMN = ``\U MS. ultraproduct_model U (J:num -> bool) MS``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(UPMMN1)", TM, TOK "(UPMMN2)"],
                  term_name = "UPMMN", paren_style = OnlyIfNecessary}

Overload Emu = ``\s. s //E μ``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(Emu1)", TM, TOK "(Emu2)"],
                  term_name = "Emu", paren_style = OnlyIfNecessary}

Overload univn = ``univ(:num)``
val _ = export_theory();
