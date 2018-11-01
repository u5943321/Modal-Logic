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



val ultrafilter_UNION = store_thm(
  "ultrafilter_UNION",
  ``!u W. ultrafilter u W ==> (!A B. A SUBSET W /\ B SUBSET W ==> ((A ∪ B) IN u <=> A IN u \/ B IN u))``,
  rw[EQ_IMP_THM] 
  >- (fs[ultrafilter_def,proper_filter_def,filter_def] >>
     `A IN (POW W')` by rw[POW_DEF] >>
     `B IN (POW W')` by rw[POW_DEF] >>
     SPOSE_NOT_THEN ASSUME_TAC >>
     `(W' DIFF A) IN u /\ (W' DIFF B) IN u` by metis_tac[] >>
     `(W' DIFF A) ∩ (W' DIFF B) IN u` by metis_tac[] >>
     `(W' DIFF A) ∩ (W' DIFF B) = W' DIFF (A ∪ B)` by (rw[DIFF_DEF,UNION_DEF,EXTENSION] >> metis_tac[]) >>
     fs[] >>
     `A ∪ B IN (POW W')` by rw[POW_DEF] >>
     metis_tac[])
  >- (fs[ultrafilter_def,proper_filter_def,filter_def] >>
     `A SUBSET (A ∪ B)` by fs[UNION_DEF,SUBSET_DEF] >>
     `(A UNION B) SUBSET W'` by fs[UNION_DEF,SUBSET_DEF] >>
     metis_tac[])
  >- (fs[ultrafilter_def,proper_filter_def,filter_def] >>
     `B SUBSET (A ∪ B)` by fs[UNION_DEF,SUBSET_DEF] >>
     `(A UNION B) SUBSET W'` by fs[UNION_DEF,SUBSET_DEF] >>
     metis_tac[]));
     
val EMPTY_NOTIN_ultrafilter = store_thm(
  "EMPTY_NOTIN_ultrafilter",
  ``!W u. ultrafilter u W ==> {} NOTIN u``,
  fs[ultrafilter_def,proper_filter_def,filter_def] >> rw[]>>
  `W' IN (POW W')` by rw[POW_DEF] >>
  `W' DIFF W' = {}` by fs[DIFF_DEF] >> metis_tac[]);



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
   



val UNION_proper_proper = store_thm(
  "UNION_proper_proper",
  ``∀W U.
     W ≠ ∅ ∧ U ≠ ∅ ∧ (∀A. A ∈ U ⇒ proper_filter A W) ∧
     (∀A B. A ∈ U ∧ B ∈ U ⇒ A ⊆ B ∨ B ⊆ A) ⇒
     proper_filter (BIGUNION U) W``,
  rw[proper_filter_def]
  >- metis_tac[UNION_filter_filter]
  >- (rw[BIGUNION] >> SPOSE_NOT_THEN ASSUME_TAC >>
     `POW W' SUBSET ({x | ∃s. s ∈ U ∧ x ∈ s})` by metis_tac[EQ_SUBSET_SUBSET] >>
     `!p. p IN (POW W') ==> p IN {x | ∃s. s ∈ U ∧ x ∈ s}` by metis_tac[SUBSET_DEF] >> `{} IN (POW W')` by rw[POW_DEF,SUBSET_DEF,EMPTY_SUBSET] >> fs[] >>
     `∃s. s ∈ U ∧ {} ∈ s` by metis_tac[] >>
     `filter s W' ∧ s ≠ POW W'` by metis_tac[] >> metis_tac[empty_improper_filter]));
     
     
    
  


val ultrafilter_theorem = store_thm(
"ultrafilter_theorem",
``!f w. proper_filter f w ==> ?U. ultrafilter U w /\ f SUBSET U``,
rpt strip_tac >>
qabbrev_tac
  `r = { (s1,s2) | proper_filter s2 w /\ proper_filter s1 w /\ f SUBSET s1 /\ s1 ⊆ s2}` >>
qabbrev_tac `s = { g | proper_filter g w /\ f ⊆ g }` >>
`partial_order r s`
  by (simp[Abbr`r`, Abbr`s`, partial_order_def, reflexive_def, transitive_def,
           domain_def, range_def] >> rw[] >> simp[]
      >- (rw[SUBSET_DEF] >> metis_tac[])
      >- (rw[SUBSET_DEF] >> metis_tac[])
      >- metis_tac[SUBSET_TRANS]
      >- (simp[antisym_def] >> rw[] >> fs[] >> metis_tac[SUBSET_ANTISYM])) >>
`s ≠ ∅` by (simp[EXTENSION, Abbr`s`] >> metis_tac[SUBSET_REFL]) >>
`∀t. chain t r ==> upper_bounds t r ≠ ∅`
  by (rw[] >> Cases_on `t = {}`
        >- (simp[chain_def, upper_bounds_def, Abbr`r`] >> rw[] >>
            simp[Once EXTENSION] >>
            qexists_tac `f` >>
            simp[range_def] >> qexists_tac `f` >> rw[])
        >- (simp[chain_def, upper_bounds_def, Abbr`r`] >> rw[] >>
            simp[Once EXTENSION] >>
            qexists_tac `BIGUNION t` >> rw[]
          >- (* BIGUNION is in (range of) relation *)
             (* BIGUNION is proper filter *)
	     (simp[range_def] >> qexists_tac `f` >> rw[]
	     (* is proper filter *)
	    >- (irule UNION_proper_proper
	      >- (fs[chain_def] >> metis_tac[])
	      >- (fs[chain_def] >> metis_tac[])
	      >- metis_tac[proper_filter_def,filter_def]
	      >- rw[])
             (* contain f *)
	    >- (fs[chain_def,Abbr`s`] >> rw[SUBSET_DEF] >>
	      `?a. a IN t` by metis_tac[MEMBER_NOT_EMPTY] >> qexists_tac `a` >> rw[] >> metis_tac[SUBSET_DEF]))
             (* indeed upper bound *)
          >- (`y IN t ==> proper_filter (BIGUNION t) w ∧ proper_filter y w ∧ f ⊆ y ∧ y ⊆ BIGUNION t` suffices_by metis_tac[] >> rw[]
	    >- (irule UNION_proper_proper >> rw[]
	        >- (fs[chain_def] >> metis_tac[])
	        >- (fs[chain_def] >> metis_tac[])
	        >- metis_tac[proper_filter_def,filter_def])
	    >- (fs[chain_def] >> metis_tac[])
	    >- (fs[chain_def] >> metis_tac[])
	    >- (rw[SUBSET_DEF,BIGUNION] >> metis_tac[])))) >>
 `?x. x IN maximal_elements s r` by metis_tac[zorns_lemma] >>
 fs[maximal_elements_def,Abbr`r`,Abbr`s`] >> qexists_tac `x` >> rw[] >>
 irule maximal_ultrafilter >> rw[] >> SPOSE_NOT_THEN ASSUME_TAC >>
 `proper_filter S' w` by metis_tac[proper_filter_def] >>
 `x <> S'` by metis_tac[PSUBSET_DEF] >>
 `x = S'` by (first_x_assum irule >> fs[] (* 2 *)
 >> metis_tac[PSUBSET_DEF,SUBSET_TRANS]));


val ultrafilter_theorem_corollary = store_thm(
  "ultrafilter_theorem_corollary",
  ``!s W. FIP s W /\ W <> {} ==> ?u. ultrafilter u W /\ s SUBSET u``,
  rw[] >>
  `∃V. proper_filter V W' ∧ s ⊆ V` by metis_tac[FIP_PSUBSET_proper_filter] >>
  `∃U. ultrafilter U W' ∧ V SUBSET U` by metis_tac[ultrafilter_theorem] >>
  qexists_tac `U` >> rw[] >> fs[SUBSET_DEF]);

val BIGINTER_FINITE = store_thm(
"BIGINTER_FINITE",
``!s'. FINITE s' ==> s' <> {} /\ s' SUBSET s ==> (∀a b. a ∈ s ∧ b ∈ s ⇒ a ∩ b ∈ s) ==> BIGINTER s' IN s``,
Induct_on `FINITE s'` >> rw[] >> Cases_on `s' = {}`
>- fs[]
>- metis_tac[]);




val FIP_closed_under_intersection = store_thm(
  "FIP_closed_under_intersection",
  ``!A B. A SUBSET POW w /\ B SUBSET POW w /\ A <> {} /\ B <> {} /\
        (!a a'. a IN A /\ a' IN A ==> (a ∩ a') IN A) /\
	(!b b'. b IN B /\ b' IN B ==> (b ∩ b') IN B) ==>
	(!a b. a IN A /\ b IN B ==> (a ∩ b) <> {}) ==>
	FIP (A ∪ B) w``,
   rw[FIP_def] >>
   `!s. FINITE s ==> s SUBSET (A ∪ B) /\ s <> {} ==> BIGINTER s <> {}` suffices_by metis_tac[] >>
   Induct_on `FINITE` >> rw[] (* 2 *)
   (* case 1 *)
   >- (Cases_on `s = {}` (* 2 *)
      >- (fs[] >> SPOSE_NOT_THEN ASSUME_TAC >> 
         `?b. b IN B` by metis_tac[MEMBER_NOT_EMPTY] >>
	 `e ∩ b = {}` by fs[EXTENSION] >> metis_tac[])
      >- (`s = (s ∩ A) ∪ (s ∩ B)` by (rw[EXTENSION,EQ_IMP_THM] >> fs[SUBSET_DEF]) >>
         `s ∩ A SUBSET A` by fs[SUBSET_DEF] >>
	 `s ∩ B SUBSET B` by fs[SUBSET_DEF] >>
	 `FINITE (s ∩ A)` by fs[] >>
	 `FINITE (s ∩ B)` by fs[] >>
	 `s ∩ A <> {} ==> BIGINTER (s ∩ A) IN A` by metis_tac[BIGINTER_FINITE] >>
	 `s ∩ B <> {} ==> BIGINTER (s ∩ B) IN B` by metis_tac[BIGINTER_FINITE] >>
	 Cases_on `s ∩ A = {}`
	 >- (`s = s ∩ B` by (fs[EXTENSION,SUBSET_DEF] >> metis_tac[]) >>
	    `BIGINTER s ∈ B` by metis_tac[] >> metis_tac[])
	 >- (Cases_on `s ∩ B = {}`
	    >- (`s = s ∩ A` by (fs[EXTENSION,SUBSET_DEF] >> metis_tac[]) >>
	       `BIGINTER s ∈ A` by metis_tac[] >>
	       `e ∩ (BIGINTER s) IN A` by metis_tac[] >>
	       `{} NOTIN A`
	           by (SPOSE_NOT_THEN ASSUME_TAC >>
		       `?b. b IN B` by metis_tac[MEMBER_NOT_EMPTY] >>
		       `{} ∩ b = {}` by fs[EXTENSION] >> metis_tac[]) >>
	       metis_tac[])
	    >- (`BIGINTER (s ∩ A) ∈ A` by metis_tac[] >>
	       `BIGINTER (s ∩ B) ∈ B` by metis_tac[] >>
	       `BIGINTER s = BIGINTER ((s ∩ A) ∪ (s ∩ B))` by metis_tac[] >>
	       fs[BIGINTER_UNION] >>
	       fs[INTER_ASSOC]))))
   >- (Cases_on `s = {}` (* 2 *)
      >- (fs[] >> SPOSE_NOT_THEN ASSUME_TAC >> 
         `?a. a IN A` by metis_tac[MEMBER_NOT_EMPTY] >>
	 `e ∩ a = {}` by fs[EXTENSION] >> metis_tac[INTER_COMM])
      >- (`s = (s ∩ A) ∪ (s ∩ B)` by (rw[EXTENSION,EQ_IMP_THM] >> fs[SUBSET_DEF]) >>
         `s ∩ A SUBSET A` by fs[SUBSET_DEF] >>
	 `s ∩ B SUBSET B` by fs[SUBSET_DEF] >>
	 `FINITE (s ∩ A)` by fs[] >>
	 `FINITE (s ∩ B)` by fs[] >>
	 `s ∩ A <> {} ==> BIGINTER (s ∩ A) IN A` by metis_tac[BIGINTER_FINITE] >>
	 `s ∩ B <> {} ==> BIGINTER (s ∩ B) IN B` by metis_tac[BIGINTER_FINITE] >>
	 Cases_on `s ∩ B = {}`
	 >- (`s = s ∩ A` by (fs[EXTENSION,SUBSET_DEF] >> metis_tac[]) >>
	    `BIGINTER s ∈ A` by metis_tac[] >> metis_tac[INTER_COMM])
	 >- (Cases_on `s ∩ A = {}`
	    >- (`s = s ∩ B` by (fs[EXTENSION,SUBSET_DEF] >> metis_tac[]) >>
	       `BIGINTER s ∈ B` by metis_tac[] >>
	       `e ∩ (BIGINTER s) IN B` by metis_tac[] >>
	       `{} NOTIN B`
	           by (SPOSE_NOT_THEN ASSUME_TAC >>
		       `?a. a IN A` by metis_tac[MEMBER_NOT_EMPTY] >>
		       `{} ∩ a = {}` by fs[EXTENSION] >> metis_tac[INTER_COMM]) >>
	       metis_tac[])
	    >- (`BIGINTER (s ∩ A) ∈ A` by metis_tac[] >>
	       `BIGINTER (s ∩ B) ∈ B` by metis_tac[] >>
	       `BIGINTER s = BIGINTER ((s ∩ A) ∪ (s ∩ B))` by metis_tac[] >>
	       fs[BIGINTER_UNION] >>
	       `BIGINTER (s ∩ A) ∩ BIGINTER (s ∩ B) = BIGINTER (s ∩ B) ∩ BIGINTER (s ∩ A)` by metis_tac[INTER_COMM] >>
	       `e ∩ (BIGINTER (s ∩ A) ∩ BIGINTER (s ∩ B)) =
	       e ∩ (BIGINTER (s ∩ B) ∩ BIGINTER (s ∩ A))` by metis_tac[] >>
	       `e ∩ (BIGINTER (s ∩ B) ∩ BIGINTER (s ∩ A)) <> {}` suffices_by metis_tac[] >>
	       simp[INTER_ASSOC] >>
	       `e ∩ BIGINTER (s ∩ B) IN B` by metis_tac[] >>
	       metis_tac[INTER_COMM])))));
	       


val _ = export_theory();