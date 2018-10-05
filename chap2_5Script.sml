open HolKernel Parse boolLib bossLib;
open chap1Theory;
open numpairTheory;
open pred_setTheory;
open relationTheory;
open arithmeticTheory;
open set_relationTheory;
open pairTheory;

open chap2_1Theory;
open chap2_2Theory;

open ultrafilterTheory;

val _ = ParseExtras.tight_equality()

val _ = new_theory "chap2_5";

(* ultrafilter extensions *)

val HM_class_def = Define`
HM_class K = (!M M' w w'. (M IN K /\ M' IN K /\ w IN M.frame.world /\ w' IN M'.frame.world) ==>
(modal_eq M M' w w' ==> bisim_world M M' w w'))`;

val satisfiable_in_def = Define`
satisfiable_in Σ X M <=> X SUBSET M.frame.world /\
                         (?x. x IN X /\ (!form. form IN Σ ==> satis M x form))`;

val fin_satisfiable_in_def = Define`
fin_satisfiable_in Σ X M <=> (!S. S SUBSET Σ /\ FINITE S ==> satisfiable_in S X M)`;

val M_sat_def = Define`
M_sat M <=> !w Σ. w IN M.frame.world ==>
(fin_satisfiable_in Σ {v | v IN M.frame.world /\ M.frame.rel w v} M ==> satisfiable_in Σ {v | v IN M.frame.world /\ M.frame.rel w v} M)`;

val modal_eq_tau = store_thm(
"modal_eq_tau",
``!M M' w w'. modal_eq M M' w w' <=> (!form. satis M w form <=> satis M' w' form)``,
rw[EQ_IMP_THM] >> fs[modal_eq_def,tau_theory_def,EXTENSION]
>- metis_tac[]
>- rw[EQ_IMP_THM])

val BIGCONJ_EXISTS_2 = store_thm(
"BIGCONJ_EXISTS_2",
``∀s.
     FINITE s ⇒
     ?ff.
     ∀w M.
        w ∈ M.frame.world ⇒ (satis M w ff ⇔ ∀f. f ∈ s ⇒ satis M w f)``,
Induct_on `FINITE s` >> rpt strip_tac
>- (qexists_tac `TRUE` >> rw[] >> metis_tac[satis_def,TRUE_def])
>- (qexists_tac `AND ff e` >> rw[] >> eq_tac
   >- (rpt strip_tac >- metis_tac[satis_AND]
                     >- (`satis M w ff` by metis_tac[satis_AND] >> metis_tac[]))
   >- (rw[] >> `e = e ==> satis M w e` by metis_tac[] >> `e = e` by metis_tac[] >>
      `satis M w e` by metis_tac[] >>
      `!f. f IN s ==> satis M w f` by metis_tac[] >>
      `satis M w ff` by metis_tac[] >>
      metis_tac[satis_AND])));


val prop_2_54 = store_thm(
"prop_2_54",
``HM_class {M | M_sat M}``,
rw[HM_class_def,bisim_world_def,bisim_def] >>
qexists_tac `λn1 n2. (!form. satis M n1 form <=> satis M' n2 form)` >> rw[]
>- (fs[M_sat_def] >>
   `fin_satisfiable_in {form | satis M v form} {v | v ∈ M'.frame.world ∧ M'.frame.rel w''' v} M'` by
   (rw[fin_satisfiable_in_def,satisfiable_in_def]
    >- rw[SUBSET_DEF]
    >- (`∃ff.
        ∀w M.
           w ∈ M.frame.world ⇒ (satis M w ff ⇔ ∀f. f ∈ S' ⇒ satis M w f)` by metis_tac[BIGCONJ_EXISTS_2] >>
       `!f. f IN S' ==> satis M v f` by fs[SUBSET_DEF] >>
       `satis M v ff` by metis_tac[] >>
       `satis M w'' (DIAM ff)`  by metis_tac[satis_def] >>
       `satis M' w''' (DIAM ff)` by metis_tac[] >>
       `?v'. v' IN M'.frame.world /\ M'.frame.rel w''' v' /\ satis M' v' ff` by metis_tac[satis_def] >>
       qexists_tac `v'` >> rw[] >>
       `∀f. f ∈ S' ⇒ satis M' v' f` by metis_tac[] >> metis_tac[])) >>
   `satisfiable_in {form | satis M v form} {v | v ∈ M'.frame.world ∧ M'.frame.rel w''' v} M'` by metis_tac[] >> fs[satisfiable_in_def] >> qexists_tac `x` >> rw[] >>
   SPOSE_NOT_THEN ASSUME_TAC >>
   `¬((satis M v form ==> satis M' x form) /\ (satis M' x form ==> satis M v form))` by metis_tac[] >>
   `¬(satis M v form ==> satis M' x form) \/ ¬(satis M' x form ==> satis M v form)` by metis_tac[] 
     >- (`satis M v form /\ ¬(satis M' x form)` by metis_tac[] >> metis_tac[])
     >- (`satis M' x form /\ ¬(satis M v form)` by metis_tac[] >>
        `satis M v (NOT form)` by metis_tac[satis_def] >>
        `¬(satis M' x (NOT form))` by metis_tac[satis_def] >>
        metis_tac[]))
>- (fs[M_sat_def] >>
   `fin_satisfiable_in {form | satis M' v' form} {v | v ∈ M.frame.world ∧ M.frame.rel w'' v} M` by
   (rw[fin_satisfiable_in_def,satisfiable_in_def]
    >- rw[SUBSET_DEF]
    >- (`∃ff.
        ∀w M.
           w ∈ M.frame.world ⇒ (satis M w ff ⇔ ∀f. f ∈ S' ⇒ satis M w f)` by metis_tac[BIGCONJ_EXISTS_2] >>
       `!f. f IN S' ==> satis M' v' f` by fs[SUBSET_DEF] >>
       `satis M' v' ff` by metis_tac[] >>
       `satis M' w''' (DIAM ff)`  by metis_tac[satis_def] >>
       `satis M w'' (DIAM ff)` by metis_tac[] >>
       `?v. v IN M.frame.world /\ M.frame.rel w'' v /\ satis M v ff` by metis_tac[satis_def] >>
       qexists_tac `v` >> rw[] >>
       `∀f. f ∈ S' ⇒ satis M v f` by metis_tac[] >> metis_tac[])) >>
   `satisfiable_in {form | satis M' v' form} {v | v ∈ M.frame.world ∧ M.frame.rel w'' v} M` by metis_tac[] >> fs[satisfiable_in_def] >> qexists_tac `x` >> rw[] >>
   SPOSE_NOT_THEN ASSUME_TAC >>
   `¬((satis M x form ==> satis M' v' form) /\ (satis M' v' form ==> satis M x form))` by metis_tac[] >>
   `¬(satis M x form ==> satis M' v' form) \/ ¬(satis M' v' form ==> satis M x form)` by metis_tac[] 
     >- (`satis M x form /\ ¬(satis M' v' form)` by metis_tac[] >>
        `satis M' v' (NOT form)` by metis_tac[satis_def] >>
        `¬(satis M x (NOT form))` by metis_tac[satis_def] >>
        metis_tac[])
     >- (`satis M' v' form /\ ¬(satis M x form)` by metis_tac[] >>
        metis_tac[]))
>- metis_tac[modal_eq_tau]);


val can_see_def = Define`
can_see M X = {w | w IN M.frame.world /\ ?x. x IN X /\ M.frame.rel w x}`;

val only_see_def = Define`
only_see M X = {w | w IN M.frame.world /\ (!x. x IN M.frame.world /\ M.frame.rel w x ==> x IN X)}`;

val valt_can_see = store_thm(
"valt_can_see",
``!M form. {w | w IN M.frame.world /\ satis M w (DIAM form)} = can_see M {v | v IN M.frame.world /\ satis M v form}``,
rw[] >> simp[EXTENSION,can_see_def] >> rw[] >> simp[EQ_IMP_THM] >> rw[]
>> metis_tac[satis_def]);

val valt_only_see = store_thm(
"valt_only_see",
``!M form. {w | w IN M.frame.world /\ satis M w (BOX form)} = only_see M {v | v IN M.frame.world /\ satis M v form}``,
rw[] >> simp[only_see_def,BOX_def,EXTENSION] >> rw[] >> simp[EQ_IMP_THM] >> rw[]
>> metis_tac[satis_def]);

val only_can_dual = store_thm(
"only_can_dual",
``!M X. X SUBSET M.frame.world ==> only_see M X = M.frame.world DIFF (can_see M (M.frame.world DIFF X))``,
simp[only_see_def,can_see_def,DIFF_DEF,EXTENSION] >> rw[] >> eq_tac >> rw[]
>> metis_tac[]);

val can_only_dual = store_thm(
"can_only_dual",
``!M X. X SUBSET M.frame.world ==> can_see M X = M.frame.world DIFF (only_see M (M.frame.world DIFF X))``,
simp[only_see_def,can_see_def,DIFF_DEF,EXTENSION] >> rw[] >> eq_tac >> rw[]
>- (fs[SUBSET_DEF] >> metis_tac[]) >> metis_tac[]);

(* exercise 2.5.5 *)

val UE_rel_def = Define`
UE_rel M u v <=> ultrafilter u M.frame.world /\
                 ultrafilter v M.frame.world /\
                 (!X. X IN v ==> (can_see M X) IN u)`;


val ultrafilter_DIFF = store_thm(
"ultrafilter_DIFF",
``!u W. ultrafilter u W ==> (!x. x SUBSET W ==> (x IN u <=> W DIFF x ∉ u))``,
rw[] >> fs[ultrafilter_def] >> `x IN POW W'` by simp[POW_DEF] >> metis_tac[]);

val ultrafilter_SUBSET = store_thm(
"ultrafilter_SUBSET",
``!u W. ultrafilter u W ==> (!x. x IN u ==> x SUBSET W)``,
rw[] >> fs[ultrafilter_def,proper_filter_def,filter_def,POW_DEF,SUBSET_DEF] >> metis_tac[]);
                 
val exercise_2_5_5 = store_thm(
"exercise_2_5_5",
``!M u v. ultrafilter u M.frame.world /\ ultrafilter v M.frame.world ==>
(UE_rel M u v <=> {Y | (only_see M Y) IN u /\ Y SUBSET M.frame.world} SUBSET v)``,
rw[] >> eq_tac 
>- (rw[UE_rel_def] >> rw[Once SUBSET_DEF] >>
`!x. ¬(can_see M x IN u) ==> ¬(x IN v)` by metis_tac[] >>
`!x. x SUBSET M.frame.world ==> (x IN v <=> M.frame.world DIFF x ∉ v)` by metis_tac[ultrafilter_DIFF] >>
`!x. x SUBSET M.frame.world /\ can_see M x ∉ u ==> M.frame.world DIFF x IN v` by metis_tac[] >>
`!x. x SUBSET M.frame.world ==> only_see M x = M.frame.world DIFF (can_see M (M.frame.world DIFF x))` by metis_tac[only_can_dual] >>
`only_see M x = M.frame.world DIFF can_see M (M.frame.world DIFF x)` by metis_tac[] >>
`!x. x SUBSET M.frame.world ==> (x IN u <=> M.frame.world DIFF x ∉ u)` by metis_tac[ultrafilter_DIFF] >>
`can_see M (M.frame.world DIFF x) SUBSET M.frame.world` by simp[can_see_def,SUBSET_DEF] >>
`M.frame.world DIFF can_see M (M.frame.world DIFF x) IN u` by metis_tac[] >>
`can_see M (M.frame.world DIFF x) ∉ u` by metis_tac[] >>
`(M.frame.world DIFF x) ∉ v` by metis_tac[] >>
metis_tac[])
>- (rw[Once SUBSET_DEF] >> rw[UE_rel_def] >>
`X SUBSET M.frame.world` by metis_tac[ultrafilter_SUBSET] >>
`!x. ¬(x IN v) ==> ¬(only_see M x IN u) \/ ¬(x SUBSET M.frame.world)` by metis_tac[] >>
`!x. (¬(x IN v) /\ x SUBSET M.frame.world) ==> ¬(only_see M x IN u)` by metis_tac[] >>
`!x. x SUBSET M.frame.world ==> (x IN v <=> M.frame.world DIFF x ∉ v)` by metis_tac[ultrafilter_DIFF] >>
`¬((M.frame.world DIFF X) IN v)` by metis_tac[] >>
`(M.frame.world DIFF X) SUBSET M.frame.world` by metis_tac[DIFF_SUBSET] >>
`¬(only_see M (M.frame.world DIFF X) IN u)` by metis_tac[] >>
`only_see M (M.frame.world DIFF X) SUBSET M.frame.world` by simp[only_see_def,SUBSET_DEF] >>
`!x. x SUBSET M.frame.world ==> (x IN u <=> M.frame.world DIFF x ∉ u)` by metis_tac[ultrafilter_DIFF] >>
`M.frame.world DIFF (only_see M (M.frame.world DIFF X)) IN u` by metis_tac[] >>
metis_tac[can_only_dual]));


val _ = export_theory();