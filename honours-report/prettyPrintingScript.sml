open HolKernel Parse boolLib bossLib;

open chap1Theory chap2_2Theory chap2_3Theory chap2_4revisedTheory chap2_6Theory chap2_7Theory lemma2_73Theory IBCDNFrevisedTheory

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
cheat
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
cheat
QED

Theorem ppprop_2_15_corollary:
!M (w:'b) form. satis M w form ==>
  ?M' (s:'b list). tree M'.frame s /\ satis M' s form
Proof
cheat
QED


Theorem ppREL_CUS_def:
REL_CUS Σ M w1 w2 <=> w1 IN M.frame.world /\
                    w2 IN M.frame.world /\
                    (!phi. phi IN Σ ==> (satis M w1 phi <=> satis M w2 phi))
Proof
cheat
QED

Theorem ppfiltration_def:
filtration M Σ L <=>
CUS Σ /\
(L.frame.world = EC_REP_SET Σ M) /\
(!w v. w IN M.frame.world /\ v IN M.frame.world /\ M.frame.rel w v ==> L.frame.rel (EC_REP Σ M w) (EC_REP Σ M v)) /\
(!w v. w IN M.frame.world /\ v IN M.frame.world /\ L.frame.rel (EC_REP Σ M w) (EC_REP Σ M v) ==> (!phi psi. (phi IN Σ /\ phi = DIAM psi /\ satis M v psi) ==> satis M w phi)) /\
(!p s. L.valt p s <=> (?w. s = EC_REP Σ M w /\ satis M w (VAR p)))
Proof
cheat
QED

Theorem ppprop_2_38:
!Σ M L. FINITE Σ /\ filtration M Σ L ==> CARD (L.frame.world) <= 2 ** (CARD (Σ))
Proof
cheat
QED

Theorem ppthm_2_39:
!phi. phi IN Σ ==> (!w. w IN M.frame.world /\ filtration M Σ L ==> (satis M w phi <=> satis L (EC_REP Σ M w) phi))
Proof
cheat
QED

Theorem ppREL_2_42_def:
    REL_2_42 Σ M w1 w2 = ?w. w IN M.frame.world /\ w1 = EC_CUS Σ M w /\
                         ?v. v IN M.frame.world /\ w2 = EC_CUS Σ M v /\
                         (!phi. (DIAM phi) IN Σ /\ satis M v (DISJ phi (DIAM phi)) ==> satis M w (DIAM phi))
Proof
cheat
QED


Theorem ppequiv0_def:
     equiv0 (:α) f1 f2 <=> !M w:'a. satis M w f1 <=> satis M w f2
Proof
cheat
QED

Theorem ppequiv0_DIAM:
 ∀f g μ. INFINITE 𝕌(:α) ⇒ (equiv0 (:α) (◇ f) (◇ g) ⇔ equiv0 (:α) f g)
Proof
cheat
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
cheat
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
cheat
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
cheat
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
cheat
QED

Theorem ppsubforms_def:
(∀a. subforms (VAR a) = {VAR a}) ∧ subforms ⊥ = {⊥} ∧
        (∀f. subforms (¬f) = {¬f} ∪ subforms f) ∧
        (∀f1 f2.
             subforms (DISJ f1 f2) =
             {DISJ f1 f2} ∪ subforms f1 ∪ subforms f2) ∧
        ∀f. subforms (◇ f) = {◇ f} ∪ subforms f
Proof
cheat
QED


Theorem pppeval_equiv0:
∀f1 f2.
            propform f1 ∧ propform f2 ∧ equiv0 μ f1 f2 ⇒
            (∀σ. peval σ f1 ⇔ peval σ f2)
Proof
cheat
QED

Theorem ppprop_2_3:
!i w f. i IN dom ==> (satis (f i) w phi <=> satis (DU (f, dom)) (i,w) phi)
Proof
cheat
QED

Theorem ppprop_2_29_strengthen:
!s. FINITE s /\ INFINITE univ(:'b) ==> !n. FINITE (partition (equiv0 (μ:'b itself)) {f| DEG f <= n /\ prop_letters f ⊆ s})
Proof
cheat
QED

Theorem ppIMAGE_peval_singlton_strengthen:
!x form. x IN {f | propform f /\ prop_letters f ⊆ s}//e /\ form IN x ==>
IMAGE (λf. {σ | peval σ f} ∩ POW s) x = {{σ | (peval σ form)} INTER (POW s)}
Proof
cheat
QED

Theorem ppequiv0_peval_strengthen:
!f1 f2.
( propform f1 /\ propform f2 /\
(prop_letters f1 ⊆ s) /\
(prop_letters f2 ⊆ s))==>
(!σ. σ IN (POW s) ==> peval σ f1 = peval σ f2) ==> (!M w. satis M w f1 <=> satis M w f2)
Proof
cheat
QED

Theorem ppINJ_peval_partition_strengthen:
INJ
  (\eqc. ((IMAGE (λf. {σ| peval σ f} INTER (POW s)) eqc)))
  {f | propform f /\ prop_letters f ⊆ s}//e
  (POW (POW (POW s)))
Proof
cheat
QED

Theorem ppDEG_IBC_strengthen:
∀x.
   DEG x ≤ n + 1 ∧ (prop_letters x ⊆ s) ⇔
   IBC x
     ({VAR v | v ∈ s} ∪
      {◇ psi | DEG psi ≤ n ∧ prop_letters psi ⊆ s})
Proof
cheat
QED


Theorem ppDNF_OF_DISJ_equiv0_case4:
∀p1 p2 fs.
            (DISJ_OF0 p1 fs /\ DISJ_OF0 p2 fs) ⇒ ∃f. DISJ_OF0 f fs ∧ equiv0 μ f (DISJ p1 p2)
Proof
cheat
QED


Theorem pplist_demorgan:
∀l.
         l ≠ [] ⇒
         equiv0 μ (AND e (lit_list_to_form2 l))
           (lit_list_to_form2 (MAP (AND e) l))
Proof
cheat
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
cheat
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
cheat
QED

Theorem ppdsatis_ALL_POSSIBLE_VALUE = REWRITE_RULE [GSYM CONJ_ASSOC, AND_IMP_INTRO] IBCDNFrevisedTheory.dsatis_ALL_POSSIBLE_VALUE

Theorem ppis_lset_DNF_OF_EXISTS = REWRITE_RULE [GSYM CONJ_ASSOC, AND_IMP_INTRO] IBCDNFrevisedTheory.is_lset_DNF_OF_EXISTS

Theorem ppmm2folm_folm2mm_feval:
∀f σ M. L1tau f /\ valuation M σ /\ wffm M ==>
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
                    (∀c. c ∈ FC phi ⇒ c < CARD A)) ==>
                    (feval M' σ phi <=>
                    feval (mm2folm M) (shift_valuation (CARD A) σ f) (shift_form (CARD A) phi))
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
!U I FMS.
  (ultrafilter U I /\
   (∀i. i IN I ==> wffm (FMS i)) /\
   (!rv i. valuation (FMS i) (\v. rv v i))) ==>
   !phi.
     {i | i IN I /\ feval (FMS i) (\v. rv v i) phi} IN U ==>
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

Theorem ppthm_2_68_half1:
!a x. (FV a ⊆ {x} /\ L1tau a /\
      invar4bisim x
      (t1: ((num -> α) -> bool) itself)
      (t2: ((num -> α) -> bool) itself) a) ==>
       ?phi.
          (!M:'a model σ.
             (wffm M /\
             valuation M σ) ==>
             (feval M σ (ST x phi) <=> feval M σ a))
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





val _ = export_theory();
