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
open ultrafilterTheory;


val _ = ParseExtras.tight_equality()

val _ = new_theory "chap2_7";


val sim_def = Define`
  sim Z M M' <=>
  !w w'. w IN M.frame.world /\ w' IN M'.frame.world /\ Z w w' ==>
  (!p. w IN M.valt p ==> w' IN M'.valt p) /\
  (!v. v IN M.frame.world /\ M.frame.rel w v ==> ?v'. v' IN M'.frame.world /\ Z v v' /\ M'.frame.rel w' v')`;

val preserved_under_sim_def = Define`
  preserved_under_sim (μ:'a itself) (ν:'b itself) phi <=> 
  (!M M' Z w w'. w:'a IN M.frame.world /\ w':'b IN M'.frame.world /\ sim Z M M' /\ Z w w' ==> (satis M w phi ==> satis M' w' phi))`;



val (PE_rules, PE_ind, PE_cases) = Hol_reln`
  (PE FALSE) /\ 
  (PE TRUE) /\
  (!p. PE (VAR p)) /\ 
  (!f1 f2. (PE f1 /\ PE f2) ==> PE (AND f1 f2)) /\ 
  (!f1 f2. (PE f1 /\ PE f2) ==> PE (DISJ f1 f2)) /\
  (!f. PE f ==> PE (DIAM f))`;    


val thm_2_78_half1_lemma = store_thm(
  "thm_2_78_half1_lemma",
  ``!phi. PE phi ==> (!μ ν. preserved_under_sim μ ν phi)``,
   Induct_on `PE phi` >> rw[preserved_under_sim_def] (* 6 *)
   >- fs[satis_def]
   >- fs[satis_def,TRUE_def]
   >- (fs[satis_def] >> metis_tac[sim_def])
   >- (fs[satis_AND] >> metis_tac[])
   >- (fs[satis_def] >> metis_tac[])
   >- (fs[satis_def] >> imp_res_tac sim_def >> metis_tac[]));

val thm_2_78_half1 = store_thm(
  "thm_2_78_half1",
  ``!phi phi0 μ ν. (PE phi0 /\ equiv0 μ phi phi0 /\ equiv0 ν phi phi0) ==> preserved_under_sim μ ν phi``,
  rw[] >> `preserved_under_sim μ ν phi0` by metis_tac[thm_2_78_half1_lemma] >>
  fs[preserved_under_sim_def] >> rw[] >> fs[equiv0_def] >> `satis M w phi0` by metis_tac[] >> metis_tac[]);


Theorem modal_compactness_thm:
!s. 
  (!ss. FINITE ss /\ ss ⊆ s ==> 
      ?M w:α. w IN M.frame.world /\ (!f. f IN ss ==> satis M w f)) ==>
  ?M w:α. w IN M.frame.world /\ (!f. f IN s ==> satis M w f)
Proof
cheat
QED

Theorem modal_compactness_corollary:
!s a. 
  (!M w:α. w IN M.frame.world ==>
      (!f:num chap1$form. f IN s ==> satis M w f) ==> satis M w a) ==>
   ?ss. FINITE ss /\ ss ⊆ s /\
        (!M w:α. w IN M.frame.world ==>
           (!f. f IN ss ==> satis M w f) ==> satis M w a)
Proof
rw[] >> SPOSE_NOT_THEN ASSUME_TAC >> 
`!ss. FINITE ss /\ ss ⊆ s ∪ {¬a} ==>
     ?M w:α. w IN M.frame.world /\ (!f. f IN ss ==> satis M w f)`
  by
   (rw[] >> 
    Cases_on `(NOT a) IN ss` (* 2 *)
    >- (`ss = ¬a INSERT (ss DELETE ¬a)` by metis_tac[INSERT_DELETE] >>
        `FINITE (ss DELETE ¬a)` by fs[] >>
        `ss DELETE ¬a ⊆ s` by (fs[SUBSET_DEF,DELETE_DEF] >> metis_tac[]) >>
        first_x_assum drule_all >> rw[] >>
        map_every qexists_tac [`M`,`w`] >> rw[] >> 
        Cases_on `f = ¬a` (* 2 *)
        >- fs[satis_def] >> 
        metis_tac[]) >>
    `ss ⊆ s` by (fs[SUBSET_DEF,UNION_DEF] >> metis_tac[]) >>
    metis_tac[]
   ) >>
drule modal_compactness_thm >> strip_tac >>
`satis M w ¬a` by fs[] >>
`!f. f IN s ==> satis M w f` by fs[UNION_DEF] >>
metis_tac[satis_def]
QED



Theorem PE_BIGCONJ:
!ss. FINITE ss ==> 
     (!f. f IN ss ==> PE f) ==>
      ?ff. PE ff /\
           !M w. w IN M.frame.world ==>
                  (satis M w ff <=> (!f. f IN ss ==> satis M w f))
Proof
Induct_on `FINITE` >> rw[] 
>- (qexists_tac `TRUE` >> rw[satis_def,TRUE_def,PE_rules]) >>
`∀f. f ∈ ss ⇒ PE f` by metis_tac[] >>
first_x_assum drule >> strip_tac >> 
qexists_tac `AND e ff` >> rw[] (* 2 *)
>- metis_tac[PE_rules] >>
rw[satis_AND] >> metis_tac[]
QED


Theorem PE_BIGDISJ:
!ss. FINITE ss ==> 
     (!f. f IN ss ==> PE f) ==>
      ?ff. PE ff /\
           !M w. w IN M.frame.world ==>
                  (satis M w ff <=> (?f. f IN ss /\ satis M w f))
Proof
Induct_on `FINITE` >> rw[] 
>- (qexists_tac `FALSE` >> rw[satis_def,PE_rules]) >>
`!f. f IN ss ==> PE f` by metis_tac[] >> 
first_x_assum drule >> strip_tac >> 
qexists_tac `DISJ e ff` >> rw[] (* 2 *)
>- metis_tac[PE_rules] >>
rw[satis_def] >> metis_tac[]
QED

Theorem PE_BIGCONJ_DIST_TYPE:
!ss. FINITE ss ==> 
     (!f. f IN ss ==> PE f) ==>
      ?ff. PE ff /\
           (!M w:β. w IN M.frame.world ==>
                  (satis M w ff <=> (!f. f IN ss ==> satis M w f))) /\
           (!M w:γ. w IN M.frame.world ==>
                  (satis M w ff <=> (!f. f IN ss ==> satis M w f)))
Proof
Induct_on `FINITE` >> rw[] 
>- (qexists_tac `TRUE` >> rw[satis_def,PE_rules,TRUE_def]) >>
`!f. f IN ss ==> PE f` by metis_tac[] >> 
first_x_assum drule >> strip_tac >> 
qexists_tac `AND e ff` >> rw[] (* 2 *)
>- metis_tac[PE_rules] >>
rw[satis_AND] >> metis_tac[]
QED


Theorem exercise_2_7_1:
!M M' w w'. 
   (M_sat M /\ M_sat M' /\ w IN M.frame.world /\ w' IN M'.frame.world)
     ==> 
     (!phi. PE phi ==> 
             (satis M w phi ==> satis M' w' phi)) ==>
     ?Z. sim Z M M' /\ Z w w'
Proof
rw[] >>
qexists_tac `\w1 w2. (!phi. PE phi ==> satis M w1 phi ==> satis M' w2 phi)` >> 
rw[sim_def] (* 2 *)
>- (`satis M w1 (VAR p) ==> satis M' w2 (VAR p)` by metis_tac[PE_rules] >>
    fs[satis_def]) >>
qabbrev_tac `d = {phi | PE phi /\ satis M w1' phi}` >> fs[M_sat_def] >>
`satisfiable_in d {v | v ∈ M'.frame.world ∧ M'.frame.rel w2 v} M'`
  suffices_by
   (rw[satisfiable_in_def] >> qexists_tac `x` >> rw[] >> fs[Abbr`d`]) >>
first_x_assum irule >> rw[fin_satisfiable_in_def,satisfiable_in_def,SUBSET_DEF] >>
drule PE_BIGCONJ_DIST_TYPE >> strip_tac >> 
`∀f. f ∈ S' ⇒ PE f` by fs[Abbr`d`] >> first_x_assum drule >> strip_tac >>
`∃x. (x ∈ M'.frame.world ∧ M'.frame.rel w2 x) ∧
     satis M' x ff` suffices_by metis_tac[] >>
`satis M' w2 (DIAM ff)` 
  suffices_by metis_tac[satis_def] >> 
first_x_assum irule >>
`PE (DIAM ff)` by metis_tac[PE_rules] >>
rw[satis_def] >>
`?v. M.frame.rel w1 v ∧ v ∈ M.frame.world ∧ 
     (∀f. f ∈ S' ⇒ satis M v f)` 
  suffices_by metis_tac[] >>
qexists_tac `w1'` >> rw[] >>
fs[Abbr`d`]
QED


Theorem thm_2_78_half2:
 !phi:num chap1$form (ν:((β -> bool) -> bool) itself) (μ:β itself). preserved_under_sim ν ν phi ==> 
     (?phi0. equiv0 μ phi phi0 /\ PE phi0)
Proof 
rw[] >> 
qabbrev_tac `PEC = {psi | PE psi /\ 
                          (!M w:β. w IN M.frame.world ==>
                               satis M w phi ==> satis M w psi)}` >>
`!M w:β. w IN M.frame.world ==>
      (!f. f IN PEC ==> satis M w f) ==> satis M w phi`
  suffices_by
   (rw[] >> 
    drule (modal_compactness_corollary |> INST_TYPE [alpha |-> ``:'b``]) >> 
    rw[] >> drule PE_BIGCONJ >> rw[] >>
    `!f. f IN ss ==> PE f` by fs[SUBSET_DEF,Abbr`PEC`] >>
    first_x_assum drule_all >> rw[] >> qexists_tac `ff` >>
    rw[EQ_equiv0_def,EQ_IMP_THM] >> fs[Abbr`PEC`,SUBSET_DEF]
   ) >>
rw[] >>  
qabbrev_tac `Γ = {NOT psi | PE psi /\ satis M w (NOT psi)}` >>
`!ss. FINITE ss /\ ss ⊆ (Γ ∪ {phi}) ==>
    ?N v:β. v IN N.frame.world /\ 
           (!f. f IN ss ==> satis N v f)`
  by
   (SPOSE_NOT_THEN ASSUME_TAC >> fs[] >> 
    `∀N v:β. v ∈ N.frame.world ⇒ 
           (satis N v phi ==> ?f. f IN (ss DELETE phi) /\ ¬satis N v f)`
      by (fs[DELETE_DEF] >> metis_tac[]) >>
    `ss DELETE phi ⊆ Γ` by (fs[SUBSET_DEF,DELETE_DEF] >> metis_tac[]) >>
    qabbrev_tac `ss0 = 
                 IMAGE (\f. case f of 
                            NOT phi => phi
                           | _  => ARB) 
                       (ss DELETE phi)` >>
    `FINITE (ss DELETE phi)` by fs[] >>
    `FINITE ss0` by metis_tac[IMAGE_FINITE,Abbr`ss0`] >>
    `!f. f IN ss0 ==> PE f`
      by
       (rw[] >> fs[Abbr`ss0`,IMAGE_DEF] >>
        fs[SUBSET_DEF,Abbr`Γ`] >> first_x_assum drule_all >> rw[] >> fs[]) >>
    drule PE_BIGDISJ >> strip_tac >> 
    (*`ss0 <> {}` by metis_tac[IMAGE_EQ_EMPTY] >> strip_tac >>*)
    first_x_assum drule_all >> strip_tac >> 
    `ff IN PEC` 
      by 
       (rw[Abbr`PEC`] >> last_x_assum drule_all >> strip_tac >>
        rw[Abbr`ss0`,IMAGE_DEF,PULL_EXISTS] >> qexists_tac `f` >>
        rw[] (* 2 *)
        >- metis_tac[] >>
        fs[Abbr`Γ`,SUBSET_DEF] >>
        `f <> phi` by metis_tac[] >> 
        `∃psi. f = ¬psi ∧ PE psi ∧ satis M w (¬psi)` by metis_tac[] >>
        fs[] >> metis_tac[satis_def]) >>
    `satis M w ff` by metis_tac[] >>
    `?f. f IN ss0 /\ satis M w f` by metis_tac[] >>
    `satis M w (NOT f)` suffices_by metis_tac[satis_def] >>
    fs[Abbr`ss0`,SUBSET_DEF,Abbr`Γ`] >> 
    `∃psi. f' = ¬psi ∧ PE psi ∧ satis M w (¬psi)` by metis_tac[] >> fs[]  
   ) >>
drule modal_compactness_thm >> rw[] >>
rename [`∀f. f ∈ Γ ∨ f = phi ⇒ satis N v f`] >>
`!psi. PE psi ==> (satis N v psi ==> satis M w psi)`
  by
   (SPOSE_NOT_THEN ASSUME_TAC >> fs[] >>
    `satis M w (¬psi)` by metis_tac[satis_def] >>
    `(¬psi) IN Γ` by fs[Abbr`Γ`] >>
    metis_tac[satis_def]) >>
`!psi. PE psi ==> 
         satis (UE N) (principle_UF v N.frame.world) psi ==>
         satis (UE M) (principle_UF w M.frame.world) psi`
  by metis_tac[prop_2_59_ii,modal_eq_tau] >>
`M_sat (UE M) /\ M_sat (UE N)` by metis_tac[prop_2_61] >>
drule (exercise_2_7_1|> INST_TYPE [gamma |-> ``:β``]) >> rw[] >> 
first_x_assum 
  (qspecl_then [`UE M`,
                `principle_UF v N.frame.world`,
                `principle_UF w M.frame.world`] assume_tac) >>
`principle_UF w M.frame.world ∈ (UE M).frame.world ∧
 principle_UF v N.frame.world ∈ (UE N).frame.world`
  by
   (simp[UE_def] >> metis_tac[principle_UF_UF,MEMBER_NOT_EMPTY]) >>
first_x_assum drule_all >> rw[] >>
fs[preserved_under_sim_def] >> 
last_x_assum drule >> rw[] >> 
first_x_assum 
  (qspecl_then [`UE M`,`Z`,`principle_UF w M.frame.world`] assume_tac) >>
rfs[] >>
`satis N v phi` by metis_tac[] >>
metis_tac[prop_2_59_ii,modal_eq_tau] 
QED

val _ = export_theory();
