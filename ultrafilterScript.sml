open HolKernel Parse boolLib bossLib;
open chap1Theory;
open numpairTheory;
open pred_setTheory;
open relationTheory;
open arithmeticTheory;
open set_relationTheory;
open pairTheory;


val _ = ParseExtras.tight_equality()

val _ = new_theory "ultrafilter";

(* ultrafilters *)

val filter_def = Define`
filter FLT W <=> W <> {} /\
                 FLT SUBSET (POW W) /\
                 W IN FLT /\
                 (!X Y. X IN FLT /\ Y IN FLT ==> (X INTER Y) IN FLT) /\
                 (!X Z. X IN FLT /\ X SUBSET Z /\ Z SUBSET W ==> Z IN FLT)
                 `;

val POW_filter = store_thm(
"POW_filter",
``!W. W <> {} ==> filter (POW W) W``,
rw[filter_def] >> fs[POW_DEF] >> fs[SUBSET_DEF,INTER_DEF]);

val proper_filter_def = Define`
proper_filter FLT W <=> filter FLT W /\ FLT <> (POW W)`;

val ultrafilter_def = Define`
ultrafilter U W <=> proper_filter U W /\
                      (!X. X IN (POW W) ==> (X IN U <=> (W DIFF X) ∉ U))`;

val cofinite_def = Define`
cofinite X S <=> INFINITE S /\ X SUBSET S /\ FINITE (S DIFF X)`;

val cofinite_filter = store_thm(
"cofinite_filter",
``!S. INFINITE S ==> filter {X | cofinite X S} S``,
rw[filter_def]
>- (`∃x. x ∈ S'` by metis_tac[INFINITE_INHAB] >> metis_tac[NOT_IN_EMPTY])
>- fs[cofinite_def,POW_DEF,DIFF_DEF,SUBSET_DEF]
>- fs[cofinite_def,DIFF_DEF]
>- (fs[cofinite_def] >> rw[]
    >- fs[INTER_DEF,SUBSET_DEF]
    >- (`S' DIFF (X ∩ Y) = (S' DIFF X) ∪ (S' DIFF Y)` by
    (fs[DIFF_DEF] >> simp[EXTENSION] >> rw[] >> eq_tac >> rw[] >> fs[])
      >> metis_tac[FINITE_UNION]))
>- (fs[cofinite_def] >>
     `(S' DIFF Z) SUBSET (S' DIFF X)` suffices_by metis_tac[SUBSET_FINITE] >>
     fs[DIFF_DEF,SUBSET_DEF] >> metis_tac[]));

val generated_filter_def = Define`
generated_filter E W = BIGINTER {G | E SUBSET G /\ filter G W}`;

val generated_filter_ind = save_thm(
"generated_filter_ind",
``e IN generated_filter E (A: 'a -> bool)``
|> SIMP_CONV (srw_ss()) [generated_filter_def,filter_def]
|> EQ_IMP_RULE |> #1
|> UNDISCH |> SPEC_ALL |> UNDISCH
|> DISCH ``e IN generated_filter E A``
|> Q.GEN `e`
|> DISCH_ALL |> Q.GEN `P`);


val generated_FT_FT = store_thm(
"generated_FT_FT",
``!E W. E SUBSET (POW W) /\ W <> {} ==> filter (generated_filter E W) W``,
rw[filter_def]
>- (rw[SUBSET_DEF] >>
`!x. x IN generated_filter E W' ==> x IN POW W'` suffices_by metis_tac[]
>> ho_match_mp_tac generated_filter_ind >> rw[]
  >- fs[POW_DEF]
  >> fs[POW_DEF,SUBSET_DEF,INTER_DEF])
>- (rw[generated_filter_def] >> metis_tac[filter_def])
>- (fs[generated_filter_def,filter_def] >> rw[] >>
`X IN P /\ Y IN P` suffices_by metis_tac[] >> metis_tac[])
>- (fs[generated_filter_def,filter_def] >> rw[] >> metis_tac[]));


val principle_UF_def = Define`
principle_UF w W = {X | X SUBSET W /\ w IN X}`;

val principle_UF_UF = store_thm(
"principle_UF_UF",
``!W w. W <> {} /\ w IN W ==> ultrafilter (principle_UF w W) W``,
rw[ultrafilter_def]
>- (rw[proper_filter_def,filter_def,principle_UF_def]
  >- rw[SUBSET_DEF,POW_DEF]
  >- fs[SUBSET_DEF,INTER_DEF]
  >- fs[SUBSET_DEF]
  >- (SPOSE_NOT_THEN ASSUME_TAC >>
   `{} IN POW W'` by fs[POW_DEF] >>
   `{} IN  {X | X ⊆ W' ∧ w ∈ X}` by metis_tac[] >>
   fs[]))
>- (eq_tac >> fs[principle_UF_def] >> rw[] >> fs[POW_DEF]));

(* val UF_FINITE_principle = store_thm(
"UF_FINITE_principle",
``!U S.(ultrafilter U (S:'a -> bool) /\ (?X. X IN U /\ FINITE X)) ==> ?w. w IN S /\ U = principle_UF w S``,
rw[] >>

*)


val empty_improper_filter = store_thm(
"empty_improper_filter",
``!W U. filter U W /\ {} IN U ==> U = POW W``,
rw[SET_EQ_SUBSET]
>- metis_tac[filter_def]
>- (rw[SUBSET_DEF] >>
   `{} SUBSET x` by metis_tac[EMPTY_SUBSET] >>
   `x SUBSET W'` by fs[POW_DEF] >>
   metis_tac[filter_def]));

val ultrafilter_filter = store_thm(
"ultrafilter_filter",
``!W U. ultrafilter U W ==> filter U W``,
metis_tac[ultrafilter_def,proper_filter_def]);


val ultrafilter_subset_DIFF = store_thm(
"ultrafilter_subset_DIFF",
``!W U V. ultrafilter U W /\ filter V W /\ U PSUBSET V ==>
(?X. (X IN POW W) /\ X IN V /\ (W DIFF X) IN V)``,
rw[] >> fs[PSUBSET_MEMBER] >> qexists_tac `y` >> rw[]
>- (`filter U W'` by metis_tac[ultrafilter_filter] >>
   `V SUBSET (POW W')` by metis_tac[filter_def] >> fs[SUBSET_DEF])
>- (`y IN (POW W')` by (`filter U W'` by metis_tac[ultrafilter_filter] >>
   `V SUBSET (POW W')` by metis_tac[filter_def] >> fs[SUBSET_DEF]) >>
   `W' DIFF y IN U` by metis_tac[ultrafilter_def] >>
   fs[SUBSET_DEF]));
  
val ultrafilter_maximal = store_thm(
"ultrafilter_maximal",
``!W U. ultrafilter U W ==> (!S. filter S W /\ U PSUBSET S ==> S = POW W)``,
rw[SET_EQ_SUBSET]
>- metis_tac[filter_def]
>- (rw[SUBSET_DEF] >>
   `x SUBSET W'` by fs[POW_DEF] >>
   `{} SUBSET x` by metis_tac[EMPTY_SUBSET] >>
   `(?X. (X IN POW W') /\ X IN S' /\ (W' DIFF X) IN S')` by metis_tac[ultrafilter_subset_DIFF] >>
   `(X INTER (W' DIFF X)) IN S'` by metis_tac[filter_def] >>
   `X ∩ (W' DIFF X) = {}` by (fs[INTER_DEF,DIFF_DEF] >> simp[EXTENSION] >> metis_tac[]) >> metis_tac[filter_def]));

val FIP_def = Define`
!W S. FIP S W = (S SUBSET (POW W) /\
(!S'. (S' SUBSET S /\ FINITE S' /\ S' <> {}) ==> BIGINTER S' <> {}))`;



val generated_filter_alt_filter = store_thm(
"generated_filter_alt_filter",
``∀F W. W <> {} /\ F SUBSET (POW W) ==> filter {X | X SUBSET W /\ (X = W \/ (?S. S SUBSET F /\ FINITE S /\ S <> {} /\ (BIGINTER S) SUBSET X))} W``,
rw[filter_def]
>- (rw[Once SUBSET_DEF] >- simp[POW_DEF,SUBSET_REFL]
   >- fs[POW_DEF])
>- fs[INTER_DEF,SUBSET_DEF]
>- (`W' ∩ W' = W'` by fs[INTER_DEF,SUBSET_DEF] >> metis_tac[])
>- fs[INTER_DEF,SUBSET_DEF]
>- (`¬(W' ∩ Y = W') ==> ∃S. S ⊆ F' ∧ FINITE S ∧ S ≠ ∅ ∧ BIGINTER S ⊆ W' ∧ BIGINTER S ⊆ Y` suffices_by metis_tac[] >> rw[] >> qexists_tac `S'` >> metis_tac[SUBSET_DEF])
>- fs[INTER_DEF,SUBSET_DEF]
>- (`¬(X ∩ W' = W') ==> ∃S. S ⊆ F' ∧ FINITE S ∧ S <> {} /\ BIGINTER S ⊆ X ∧ BIGINTER S ⊆ W'` suffices_by metis_tac[] >> rw[] >> qexists_tac `S'` >> rw[] >>
   `!s x. (s IN S' /\ x IN s ==> x IN W')` by
   (rw[] >> `s IN POW W'` by fs[SUBSET_DEF] >>
   `s SUBSET W'` by fs[POW_DEF] >> fs[SUBSET_DEF]) >>
   rw[SUBSET_DEF] >>
   `?a. a IN S'` by metis_tac[MEMBER_NOT_EMPTY] >>
   `x IN a` by metis_tac[] >> metis_tac[])
>- fs[INTER_DEF,SUBSET_DEF]
>- (`¬(X ∩ Y = W') ==> ∃S. S ⊆ F' ∧ FINITE S /\ S <> {} ∧ BIGINTER S ⊆ X ∧ BIGINTER S ⊆ Y` suffices_by metis_tac[] >> rw[] >> qexists_tac `S' UNION S''` >> rw[]
  >- fs[UNION_DEF,SUBSET_DEF]
  >- fs[UNION_DEF,SUBSET_DEF])
>- metis_tac[SET_EQ_SUBSET]
>- (`¬(Z = W') ==> ∃S. S ⊆ F' ∧ FINITE S ∧ S <> {} /\ BIGINTER S ⊆ Z` suffices_by metis_tac[] >> rw[] >> qexists_tac `S'` >> rw[] >> fs[SUBSET_DEF]));


   
val FIP_PSUBSET_proper_filter = store_thm(
"FIP_PSUBSET_proper_filter",
``!W S. W <> {} /\ FIP S W ==>
?V. proper_filter V W /\ S SUBSET V``,
rw[FIP_def] >>
qexists_tac `{X | X ⊆ W' ∧ (X = W' ∨ ∃S. S ⊆ S' ∧ FINITE S ∧ S <> {} /\ BIGINTER S ⊆ X)}` >> rw[]
>- (rw[proper_filter_def]
   >- metis_tac[generated_filter_alt_filter]
   >- (`?x. x IN (POW W') /\ x NOTIN {X |
 X ⊆ W' ∧ (X = W' ∨ ∃S. S ⊆ S' ∧ FINITE S ∧ S ≠ ∅ ∧ BIGINTER S ⊆ X)}` by (qexists_tac `{}` >> rw[] >- fs[EMPTY_SUBSET,POW_DEF] >- (fs[FIP_def] >> metis_tac[])) >> simp[Once EXTENSION] >> qexists_tac `x` >> fs[POW_DEF] >> metis_tac[]))
>- (rw[Once SUBSET_DEF]
  >- (fs[POW_DEF,SUBSET_DEF] >> metis_tac[])
  >- (`∃S. S ⊆ S' ∧ FINITE S ∧ S ≠ ∅ ∧ BIGINTER S ⊆ x` by (qexists_tac `{x}` >> rw[]) >> metis_tac[])));



val BIGINTER_IN_filter = store_thm(
"BIGINTER_IN_filter",
``!s. FINITE s ==> (s <> {} ==> (!U W. filter U W  ==> (s SUBSET U ==> (BIGINTER s) IN U)))``,
Induct_on `FINITE s` >> rw[] >> Cases_on `s = {}`
>- (`BIGINTER s = 𝕌(:α)` by simp[BIGINTER_EMPTY] >>
   `e INTER (BIGINTER s) = e` by simp[INTER_DEF] >> metis_tac[])
>- (`BIGINTER s ∈ U` by metis_tac[] >> metis_tac[filter_def]));



val proper_filter_FIP = store_thm(
"proper_filter_FIP",
``!W U. proper_filter U W ==> FIP U W``,
rw[] >> SPOSE_NOT_THEN ASSUME_TAC >>
fs[FIP_def]
>- metis_tac[filter_def,proper_filter_def]
>- (`filter U W'` by metis_tac[proper_filter_def] >>
   `S' <> {}` by (SPOSE_NOT_THEN ASSUME_TAC >> `BIGINTER S' = 𝕌(:α)` by metis_tac[BIGINTER_EMPTY] >> metis_tac[UNIV_NOT_EMPTY]) >>
   `BIGINTER S' IN U` by metis_tac[BIGINTER_IN_filter] >>
   `U = POW W'` suffices_by metis_tac[proper_filter_def] >>
   simp[EXTENSION] >> rw[] >> eq_tac >> rw[]
   >- metis_tac[filter_def,SUBSET_DEF]
   >- (`{} SUBSET x` by metis_tac[EMPTY_SUBSET] >>
      `x SUBSET W'` by fs[POW_DEF] >>
      metis_tac[filter_def])));

val SUBSET_INTER_DIFF = store_thm(
"SUBSET_INTER_DIFF",
``!A B C. A SUBSET C /\ B SUBSET C ==> (A INTER B = {} <=> B SUBSET (C DIFF A))``,
rw[SUBSET_DEF, EXTENSION] >> metis_tac[]);

val proper_filter_INSERT_FIP = store_thm(
"proper_filter_INSERT_FIP",
``!U W B. proper_filter U W /\ B IN (POW W) /\ B NOTIN U /\ (W DIFF B) NOTIN U ==> FIP ({B} UNION U) W``,
rw[FIP_def]
>- metis_tac[proper_filter_def,filter_def]
>- (`FIP U W'` by metis_tac[proper_filter_FIP] >>
   Cases_on `B IN S'`
   >- (`?U'. U' SUBSET U /\ S' = {B} UNION U'` by
      (qexists_tac `S' DIFF {B}` >> fs[SUBSET_DEF,DIFF_DEF] >> rw[]
       >- metis_tac[]
       >- (rw[EXTENSION,EQ_IMP_THM] >- metis_tac[]
                                    >- (`x = B` by simp[SET_EQ_SUBSET,SUBSET_DEF] >> metis_tac[]))) >> `{B} UNION U' = B INSERT U'` by rw[EXTENSION,INSERT_DEF] >> rw[BIGINTER_INSERT] >>
      `B <> {}` by (SPOSE_NOT_THEN ASSUME_TAC >> `W' DIFF B = W'` by simp[DIFF_DEF] >>
      metis_tac[proper_filter_def,filter_def]) >> 
      Cases_on `U' = {}`
      >- metis_tac[BIGINTER_EMPTY,INTER_UNIV]
      >- (SPOSE_NOT_THEN ASSUME_TAC >>
      `FINITE U'` by fs[] >> 
      `(BIGINTER U') IN U` by metis_tac[BIGINTER_IN_filter,proper_filter_def] >>
      `filter U W'` by metis_tac[proper_filter_def] >> 
      `BIGINTER U' SUBSET W'` by
      (`U SUBSET (POW W')` by metis_tac[filter_def] >>
      `BIGINTER U' IN (POW W')` by metis_tac[SUBSET_DEF] >> fs[POW_DEF]) >>
      `(BIGINTER U') SUBSET (W' DIFF B)` by
      (`B SUBSET W'` by fs[POW_DEF] >> metis_tac[INTER_COMM,SUBSET_INTER_DIFF]) >>
      `(W' DIFF B) SUBSET W'` by fs[DIFF_DEF] >>
      `(W' DIFF B) IN U` by metis_tac[filter_def]))
    >- (fs[FIP_def] >>
      `S' SUBSET U` by
      (rw[SUBSET_DEF] >> `x IN {B} ∪ U` by metis_tac[SUBSET_DEF] >> `x = B \/ x IN U` by fs[] >> metis_tac[]) >> metis_tac[])));
      
val maximal_ultrafilter = store_thm(
"maximal_ultrafilter",
``!W U. proper_filter U W /\ (!S. filter S W /\ U PSUBSET S ==> S = POW W) ==> ultrafilter U W``,
fs[ultrafilter_def] >> strip_tac >> strip_tac >> strip_tac >> SPOSE_NOT_THEN ASSUME_TAC >>
`∃X. X ∈ POW W' ∧ (X ∈ U ⇎ W' DIFF X ∉ U)` by metis_tac[] >>
`¬(X ∈ U ==> W' DIFF X ∉ U) \/ ¬(W' DIFF X ∉ U ==> X ∈ U)` by metis_tac[] 
>- (`X IN U /\ (W' DIFF X) IN U` by metis_tac[] >>
`(X INTER (W' DIFF X)) IN U` by metis_tac[filter_def,proper_filter_def] >>
`X ∩ (W' DIFF X) = {}` by (fs[DIFF_DEF,INTER_DEF,EXTENSION] >> metis_tac[]) >>
`U = POW W'` by
(simp[EXTENSION] >> rw[EQ_IMP_THM]
                   >- (`U SUBSET POW W'` by metis_tac[proper_filter_def,filter_def] >> metis_tac[SUBSET_DEF])
                   >- (`U SUBSET POW W'` by metis_tac[proper_filter_def,filter_def] >> metis_tac[SUBSET_DEF])
                   >- (`{} IN U` by fs[] >>
                      `{} SUBSET x` by metis_tac[EMPTY_SUBSET] >>
                      `filter U W'` by metis_tac[proper_filter_def] >>
                      `!A B. A IN U /\ A SUBSET B /\ B SUBSET W' ==> B IN U` by metis_tac[filter_def] >>
                      `x SUBSET W'` by fs[POW_DEF] >> metis_tac[])
                   >- (`{} IN U` by fs[] >>
                      `{} SUBSET x` by metis_tac[EMPTY_SUBSET] >>
                      `filter U W'` by metis_tac[proper_filter_def] >>
                      `!A B. A IN U /\ A SUBSET B /\ B SUBSET W' ==> B IN U` by metis_tac[filter_def] >>
                      `x SUBSET W'` by fs[POW_DEF] >> metis_tac[])) >>
metis_tac[proper_filter_def])
>- (`W' DIFF X NOTIN U /\ X NOTIN U` by metis_tac[] >>
   `FIP ({X} UNION U) W'` by metis_tac[proper_filter_INSERT_FIP] >>
   `W' <> {}` by metis_tac[proper_filter_def,filter_def] >>
   `∃V. proper_filter V W' ∧ ({X} ∪ U) ⊆ V` by metis_tac[FIP_PSUBSET_proper_filter] >>
   `U PSUBSET V` by
   (`?x. x NOTIN U /\ X INSERT U SUBSET V` by (qexists_tac `X` >> fs[]) >> metis_tac[PSUBSET_INSERT_SUBSET]) >>
   `V <> POW W'` by metis_tac[proper_filter_def] >>
   `filter V W'` by metis_tac[proper_filter_def] >> metis_tac[]));
   

val UNION_filter_filter = store_thm(
"UNION_filter_filter",
``!W U. W <> {} /\ U <> {} /\ (!A. A IN U ==> filter A W) /\ (!A B. A IN U /\ B IN U ==> (A SUBSET B \/ B SUBSET A))==> filter (BIGUNION U) W``,
rw[filter_def]
>- (simp[SUBSET_DEF] >> rw[] >> `s SUBSET POW W'` by metis_tac[] >> fs[SUBSET_DEF])
>- (`?s. s IN U` by metis_tac[MEMBER_NOT_EMPTY] >> qexists_tac `s` >> metis_tac[])
>- (`s SUBSET s' \/ s' SUBSET s` by metis_tac[]
   >- (`X IN s'` by fs[SUBSET_DEF] >> qexists_tac `s'` >> metis_tac[])
   >- (`Y IN s` by fs[SUBSET_DEF] >> qexists_tac `s` >> metis_tac[]))
>- (qexists_tac `s` >> metis_tac[]));
   

val partial_order_SUBSET = store_thm(
"partial_order_SUBSET",
``!s. partial_order (λ(s1, s2). (s1 SUBSET s2) /\ s1 IN s /\ s2 IN s) s``,
rw[partial_order_def,SUBSET_DEF]
>- (fs[domain_def] >> fs[IN_DEF])
>- fs[range_def,IN_DEF]
>- fs[transitive_def,IN_DEF]
>- fs[reflexive_def,IN_DEF]
>- (fs[antisym_def,IN_DEF]
>> (rw[SUBSET_DEF,SET_EQ_SUBSET] >> metis_tac[IN_DEF])));



(* val filter_chain_upper_bound = store_thm(
"filter_chain_upper_bound",
``!t. chain t (λ(s1, s2). (s1 SUBSET s2) /\ s1 IN s /\ s2 IN s)



val zorn_lemma_applied = store_thm(
"zorn_lemma_applied",
``!W. ?x. x IN maximal_elements {U | filter U M} (λ(s1, s2). (s1 SUBSET s2) /\ s1 IN {U | filter U M} /\ s2 IN {U | filter U M})``,
rw[] >> irule zorns_lemma
>- rw[] >> `?x. x IN upper_bounds t (λ(s1,s2). s1 ⊆ s2 ∧ filter s1 M ∧ filter s2 M)` suffices_by simp[MEMBER_NOT_EMPTY] >> simp[upper_bounds_def] >> rw[range_def] >> 



val ultrafilter_theorem = store_thm(
"ultrafilter_theorem",
``!S W. filter S W ==> ?U. ultrafilter U W /\ S SUBSET U``,


*)

val _ = export_theory();