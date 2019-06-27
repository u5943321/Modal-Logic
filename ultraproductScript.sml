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
val _ = ParseExtras.tight_equality()
val _ = new_theory "ultraproduct";

val Cart_prod_def = Define`
  Cart_prod I A = {f | !i. i IN I ==> f i IN A i}`;

val Uequiv_def = Define`
  Uequiv U I A f g <=> ultrafilter U I /\
                     (!i. i IN I ==> A i <> {}) /\
		     f IN Cart_prod I A /\ g IN Cart_prod I A /\
		     {i | i IN I /\ f i = g i} IN U`;

val prop_A_16 = store_thm(
  "prop_A_16",
  ``!U I A. ultrafilter U I ==> (Uequiv U I A) equiv_on Cart_prod I A``,
  rw[Uequiv_def,Cart_prod_def,equiv_on_def] (* 4 *)
  >- metis_tac[MEMBER_NOT_EMPTY]
  >- metis_tac[ultrafilter_def,proper_filter_def,filter_def]
  >- fs[EQ_SYM_EQ]
  >- (`{i | i ∈ I' ∧ x i = y i} ∩ {i | i ∈ I' ∧ y i = z i} IN U` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     `{i | i ∈ I' ∧ x i = y i} ∩ {i | i ∈ I' ∧ y i = z i} ⊆ {i | i ∈ I' ∧ x i = z i}` by rw[SUBSET_DEF,INTER_DEF,EXTENSION] >>
     `{i | i ∈ I' ∧ x i = z i} ⊆ I'` by rw[SUBSET_DEF] >>
     metis_tac[ultrafilter_def,proper_filter_def,filter_def]));



val ultraproduct_def = Define`
  ultraproduct U I A = partition (Uequiv U I A) (Cart_prod I A)`;

Theorem ultraproduct_same_eqclass:
  !U I A. ultrafilter U I ==> 
      !fc. fc IN (ultraproduct U I A) ==>
         !x y. x IN fc /\ y IN fc ==>
              {i | i IN I /\ x i = y i} IN U
Proof
  rw[] >> fs[ultraproduct_def,partition_def] >> rfs[] >> drule prop_A_16 >> rw[] >> 
  fs[equiv_on_def] >> `Uequiv U I' A x y` by metis_tac[] >> fs[Uequiv_def]
QED


Theorem ultraproduct_go_to_same_eq_class:
  !U I A. ultrafilter U I ==> 
     !x y. (!i. i IN I ==> (x i) IN (A i)) /\ 
           (!i. i IN I ==> (y i) IN (A i)) /\
           ({i | i IN I /\ x i = y i} IN U) ==>
       !fc. fc IN (ultraproduct U I A) ==> (y IN fc <=> x IN fc)
Proof
  rw[] >> drule prop_A_16 >> rw[] >> fs[ultraproduct_def,partition_def,equiv_on_def] >> 
  `y ∈ Cart_prod I' A /\ x ∈ Cart_prod I' A` by rw[Cart_prod_def] >>
  `Uequiv U I' A x y` by (rw[Uequiv_def] >> rw[GSYM MEMBER_NOT_EMPTY] >>
                         qexists_tac `x i` >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ultraproduct_eqclass_non_empty:
  !U I A. ultrafilter U I ==> 
      !fc. fc IN (ultraproduct U I A) ==> fc <> {}
Proof
  rw[ultraproduct_def] >> drule prop_A_16 >> rw[] >> metis_tac[EMPTY_NOT_IN_partition]
QED

val models2worlds_def = Define`
  models2worlds MS = \i. (MS i).frame.world`;

val ultraproduct_model_def = Define`
  ultraproduct_model U I MS = <| frame := <| world := ultraproduct U I (models2worlds MS);
                                               rel := \fu gu. (?f g. f IN fu /\ g IN gu /\
					                      {i | i IN I /\ (MS i).frame.rel (f i) (g i)} IN U) |>;
			          valt := \p fu. (?f. f IN fu /\ {i | i IN I /\ (f i) IN (MS i).valt p} IN U) |>`;


val ultraproduct_world_NOT_EMPTY = store_thm(
  "ultraproduct_world_NOT_EMPTY",
  ``!U J MS v. ultrafilter U J ==> v IN (ultraproduct_model U J MS).frame.world ==> v <> {}``,
  rw[ultraproduct_def,ultraproduct_model_def, models2worlds_def] >> metis_tac[prop_A_16,EMPTY_NOT_IN_partition]);

val ultraproduct_world = store_thm(
  "ultraproduct_world",
  ``!U J MS.
    ultrafilter U J ==>
       (!v.
           v ∈ (ultraproduct_model U J MS).frame.world <=>
               (!i. i IN J ==> (MS i).frame.world <> {}) /\
               (∃x.
                   (∀i. i ∈ J ⇒ x i ∈ (MS i).frame.world) /\
                   v = {y | (∀i. i ∈ J ⇒ y i ∈ (MS i).frame.world) /\ {i | i ∈ J ∧ x i = y i} ∈ U}))``,
  rw[ultraproduct_def,ultraproduct_model_def, models2worlds_def,partition_def,Uequiv_def,Cart_prod_def] >> rw[EQ_IMP_THM] (* 3 *)
  >- metis_tac[MEMBER_NOT_EMPTY]
  >> qexists_tac `x` >> rw[EXTENSION,EQ_IMP_THM] >> metis_tac[]);

  
val ultraproduct_rel = save_thm(
  "ultraproduct_rel",
  ``(ultraproduct_model U J MS).frame.rel w v``
    |> SIMP_CONV (srw_ss()) [ultraproduct_def,ultraproduct_model_def, models2worlds_def,partition_def,Uequiv_def,Cart_prod_def])

val ultraproduct_valt = save_thm(
  "ultraproduct_valt",
  ``v IN (ultraproduct_model U J MS).valt p``
    |> SIMP_CONV (srw_ss()) [ultraproduct_def,ultraproduct_model_def, models2worlds_def,partition_def,Uequiv_def,Cart_prod_def])



val ultraproduct_world_constant = store_thm(
  "ultraproduct_world_constant",
  ``!U J MS w.
  ultrafilter U J ⇒
  (∀i. i ∈ J ⇒ MS i = M) ⇒
  ({fw | Uequiv U J (models2worlds MS) (λi. w) fw} ∈ (ultraproduct_model U J MS).frame.world
  <=> w ∈ M.frame.world)``,
  rw[EQ_IMP_THM] 
  >- (`?i. i IN J`
       by metis_tac[ultrafilter_def,proper_filter_def,filter_def,MEMBER_NOT_EMPTY] >>
     `{fw | Uequiv U J (models2worlds MS) (λi. w) fw} <> {}`
       by metis_tac[ultraproduct_world_NOT_EMPTY] >> fs[ultraproduct_world] >>
     fs[Uequiv_def,models2worlds_def,Cart_prod_def] >>
     `?a. a IN {fw |
       ultrafilter U J ∧ (∀i. i ∈ J ⇒ (MS i).frame.world ≠ ∅) ∧
       (∀i. i ∈ J ⇒ w ∈ (MS i).frame.world) ∧
       (∀i. i ∈ J ⇒ fw i ∈ (MS i).frame.world) ∧
       {i | i ∈ J ∧ w = fw i} ∈ U}` by metis_tac[MEMBER_NOT_EMPTY] >> fs[] >> metis_tac[])
  >- (rw[ultraproduct_world] (* 2 *)
     >- metis_tac[MEMBER_NOT_EMPTY]
     >- (qexists_tac `\i.w` >> rw[Uequiv_def,models2worlds_def,Cart_prod_def] >>
        simp[EXTENSION] >> metis_tac[])));



val ultrapower_valt_well_defined = store_thm(
  "ultrapower_valt_well_defined",
  ``!U J Ms. ultrafilter U J ==> !f g. Uequiv U J (models2worlds Ms) f g ==>
             ({i | i IN J /\ (f i) IN (Ms i).valt p} IN U <=>
	     {i | i IN J /\ (g i) IN (Ms i).valt p} IN U)``,
  rw[Uequiv_def,models2worlds_def,Cart_prod_def] >> eq_tac >> rw[]
  >- (`{i | i IN J /\ f i = g i} ∩ {i | i IN J /\ f i IN (Ms i).valt p} IN U`
       by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     `{i | i IN J /\ g i IN (Ms i).valt p} ⊆ J` by fs[SUBSET_DEF] >>
     `({i | i IN J /\ f i = g i} ∩ {i | i IN J /\ f i IN (Ms i).valt p}) ⊆
     {i | i IN J /\ g i IN (Ms i).valt p}` suffices_by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     rw[INTER_DEF,SUBSET_DEF] >> metis_tac[])
  >- (`{i | i IN J /\ f i = g i} ∩ {i | i IN J /\ g i IN (Ms i).valt p} IN U`
       by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     `{i | i IN J /\ f i IN (Ms i).valt p} ⊆ J` by fs[SUBSET_DEF] >>
     `({i | i IN J /\ f i = g i} ∩ {i | i IN J /\ g i IN (Ms i).valt p}) ⊆
     {i | i IN J /\ f i IN (Ms i).valt p}` suffices_by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     rw[INTER_DEF,SUBSET_DEF] >> metis_tac[]));


val Los_modal_thm = store_thm(
  "Los_modal_thm",
  ``!U J Ms. ultrafilter U J ==>
             !phi fc. fc IN (ultraproduct_model U J Ms).frame.world ==>
	              (satis (ultraproduct_model U J Ms) fc phi <=>
	              ?f. f IN fc /\ {i | i IN J /\ satis (Ms i) (f i) phi} IN U)``,
  strip_tac >> strip_tac >> strip_tac  >> strip_tac >> Induct_on `phi` >> rw[] (* 5 *)
(*-----------------------------block 1 `` VAR case``------------------------------------- *)
>- 
(fs[satis_def,ultraproduct_world,ultraproduct_valt] >> eq_tac >> rw[] (* 2 *)
>- (qexists_tac `f` >> rw[] >> fs[] >>
        `{i | i IN J /\ f i IN (Ms i).frame.world /\ f i IN (Ms i).valt a} =
	{i | i IN J /\ f i IN (Ms i).valt a}` suffices_by metis_tac[] >>
	simp[EXTENSION] >> rw[] >> eq_tac >> rw[] >>
	`(!i. i IN J ==> (Ms i).frame.world <> {}) /\
         ?x.
            (!i. i IN J ==> x i IN (Ms i).frame.world) /\
            fc =
            {y |
             (!i. i IN J ==> y i IN (Ms i).frame.world) /\
             {i | i IN J /\ x i = y i} IN U}` by metis_tac[ultraproduct_world] >>
	`f IN {y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\ {i | i IN J /\ x' i = y i} IN U}`
	  by metis_tac[] >> fs[])
>- (`(!i. i IN J ==> (Ms i).frame.world <> {}) /\
   ?x. (!i. i IN J ==> x i IN (Ms i).frame.world) /\
       fc = {y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\ {i | i IN J /\ x i = y i} IN U}`
     by metis_tac[ultraproduct_world] >>
   fs[] >> qexists_tac `f` >> rw[] >>
   `{i | i IN J /\ f i IN (Ms i).frame.world /\ f i IN (Ms i).valt a} = {i | i IN J /\ f i IN (Ms i).valt a}`
     by rw[EXTENSION,EQ_IMP_THM] >>
   metis_tac[]))
(*-----------------------------block 2 `` \/ case``------------------------------------- *)
>-
(rw[satis_def,EQ_IMP_THM,ultraproduct_world] (* 3 *)
>- (qexists_tac `f` >> rw[] >> 
        `{i | i IN J /\ (satis (Ms i) (f i) phi \/ satis (Ms i) (f i) phi')} ⊆ J` by fs[SUBSET_DEF] >>
	`{i | i IN J /\ satis (Ms i) (f i) phi} ⊆ {i | i IN J /\ (satis (Ms i) (f i) phi \/ satis (Ms i) (f i) phi')}` suffices_by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >> fs[SUBSET_DEF])
>- (qexists_tac `f` >> rw[] >> 
        `{i | i IN J /\ (satis (Ms i) (f i) phi \/ satis (Ms i) (f i) phi')} ⊆ J` by fs[SUBSET_DEF] >>
	`{i | i IN J /\ satis (Ms i) (f i) phi'} ⊆ {i | i IN J /\ (satis (Ms i) (f i) phi \/ satis (Ms i) (f i) phi')}` suffices_by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >> fs[SUBSET_DEF])
>- (`{i | i IN J /\ (satis (Ms i) (f i) phi \/ satis (Ms i) (f i) phi')} =
        {i | i IN J /\ satis (Ms i) (f i) phi} ∪ {i | i IN J /\ satis (Ms i) (f i) phi'}`
	  by (rw[EXTENSION,EQ_IMP_THM] >> metis_tac[]) >>
	`{i | i IN J /\ satis (Ms i) (f i) phi} ⊆ J /\
	 {i | i IN J /\ satis (Ms i) (f i) phi'} ⊆ J` by fs[SUBSET_DEF] >>
	`{i | i IN J /\ satis (Ms i) (f i) phi} IN U \/
	{i | i IN J /\ satis (Ms i) (f i) phi'} IN U` by metis_tac[ultrafilter_UNION]
	>> metis_tac[]))
(*-----------------------------block 3 `` FALSE case``------------------------------------- *)
>-
(`((satis (ultraproduct_model U J Ms) fc FALSE) = F) /\
((?f. f IN fc /\ {i | i IN J /\ satis (Ms i) (f i) FALSE} IN U) = F)` suffices_by metis_tac[] >> rw[] (* 2 *)
>- rw[satis_def]
>- (`{i | i IN J /\ satis (Ms i) (f i) FALSE} NOTIN U` suffices_by metis_tac[] >>
   `{i | i IN J /\ satis (Ms i) (f i) FALSE} = {}`
     by rw[EXTENSION,EQ_IMP_THM,satis_def] >>
   metis_tac[EMPTY_NOTIN_ultrafilter]))
(*-----------------------------block 4 `` ¬ case``------------------------------------- *)
>-
(rw[satis_def,EQ_IMP_THM,ultraproduct_world] (* 2 *)
>- (`(!i. i IN J ==> (Ms i).frame.world <> {}) /\
    ?x. (!i. i IN J ==> x i IN (Ms i).frame.world) /\
        fc = {y |
             (!i. i IN J ==> y i IN (Ms i).frame.world) /\
             {i | i IN J /\ x i = y i} IN U}` by metis_tac[ultraproduct_world] >>
   qexists_tac `x` >> rw[] (* 2 *)
   >- metis_tac[ultrafilter_def,proper_filter_def,filter_def]
   >- (`x IN {y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\ {i | i IN J /\ x i = y i} IN U}`
        by (rw[] >> metis_tac[ultrafilter_def,proper_filter_def,filter_def]) >>
      `{i | i IN J /\ satis (Ms i) (x i) phi} NOTIN U` by metis_tac[] >>
      `{i | i IN J /\ satis (Ms i) (x i) phi} IN (POW J)` by fs[SUBSET_DEF,POW_DEF] >>
      `J DIFF {i | i IN J /\ satis (Ms i) (x i) phi} IN U` by metis_tac[ultrafilter_def] >>
      fs[DIFF_DEF] >>
      `{i | i IN J /\ x i IN (Ms i).frame.world /\ ~satis (Ms i) (x i) phi} =
      {x' | x' IN J /\ (x' NOTIN J \/ ~satis (Ms x') (x x') phi)}`
        by rw[EXTENSION,EQ_IMP_THM] >>
      metis_tac[]))
>- (`!f'. f' IN fc ==> {i | i IN J /\ satis (Ms i) (f' i) phi} NOTIN U` suffices_by metis_tac[] >> rw[] >>
   `(!i. i IN J ==> (Ms i).frame.world <> {}) /\
    ?x. (!i. i IN J ==> x i IN (Ms i).frame.world) /\
        fc = {y |
             (!i. i IN J ==> y i IN (Ms i).frame.world) /\
             {i | i IN J /\ x i = y i} IN U}` by metis_tac[ultraproduct_world] >>
   fs[] >>
   `{i | i IN J /\ satis (Ms i) (f' i) phi} IN (POW J)` by fs[SUBSET_DEF,POW_DEF] >>
   `J DIFF {i | i IN J /\ satis (Ms i) (f' i) phi} IN U` suffices_by metis_tac[ultrafilter_def] >>
   rw[DIFF_DEF] >>
   `{x | x IN J /\ (x NOTIN J \/ ~satis (Ms x) (f' x) phi)} =
   {x | x IN J /\ ~satis (Ms x) (f' x) phi}` by rw[EXTENSION,EQ_IMP_THM] >> fs[] >>
   `{i | i IN J /\ f i IN (Ms i).frame.world /\ ~satis (Ms i) (f i) phi} ∩
   {i | i IN J /\ x i = f i} IN U` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
   `({i | i IN J /\ f i IN (Ms i).frame.world /\ ~satis (Ms i) (f i) phi} ∩
   {i | i IN J /\ x i = f i}) ∩  {i | i IN J /\ x i = f' i} IN U` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
   `({i | i IN J /\ f i IN (Ms i).frame.world /\ ~satis (Ms i) (f i) phi} ∩
   {i | i IN J /\ x i = f i}) ∩  {i | i IN J /\ x i = f' i} ⊆
   {x | x IN J /\ ~satis (Ms x) (f' x) phi}` by (rw[SUBSET_DEF] >> metis_tac[]) >>
   `{x | x IN J /\ ~satis (Ms x) (f' x) phi} ⊆ J` by rw[SUBSET_DEF] >>
   metis_tac[ultrafilter_def,proper_filter_def,filter_def]))
(*-----------------------------block 4 ``DIAM case``------------------------------------- *)
>-
(rw[satis_def,EQ_IMP_THM,ultraproduct_world] (* 2 *)
(*-------------------------------half 1---------------------------------------------------*)
>- (`(!i. i IN J ==> (Ms i).frame.world <> {}) /\
   ?x. (!i. i IN J ==> x i IN (Ms i).frame.world) /\
   fc = {y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\ {i | i IN J /\ x i = y i} IN U}` by metis_tac[ultraproduct_world] >> qexists_tac `x'` >> rw[] >> fs[] (* 2 *)
  >- metis_tac[ultrafilter_def,proper_filter_def,filter_def]
  >- (`?f g.
      f IN {y |
         (!i. i IN J ==> y i IN (Ms i).frame.world) /\
         {i | i IN J /\ x' i = y i} IN U} /\ g IN {y |
         (!i. i IN J ==> y i IN (Ms i).frame.world) /\
         {i | i IN J /\ x i = y i} IN U} /\
      {i | i IN J /\ (Ms i).frame.rel (f i) (g i)} IN U` by metis_tac[ultraproduct_rel] >> fs[] >>
     `{i | i IN J /\ x' i = f i} ∩ {i | i IN J /\ (Ms i).frame.rel (f i) (g i)} IN U`
       by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     `{i | i IN J /\ x' i = f i} INTER {i | i IN J /\ (Ms i).frame.rel (f i) (g i)} ⊆ {i | i IN J /\ (Ms i).frame.rel (x' i) (g i)} `
       by rw[SUBSET_DEF] >>
     `{i | i IN J /\ (Ms i).frame.rel (x' i) (g i)} ⊆ J` by fs[SUBSET_DEF] >>
     `{i | i IN J /\ (Ms i).frame.rel (x' i) (g i)} IN U` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     `{i | i IN J /\ satis (Ms i) (g i) phi} IN U`
       by (`?r. r IN {y |
          (!i. i IN J ==> y i IN (Ms i).frame.world) /\
          {i | i IN J /\ x i = y i} IN U} /\ {i | i IN J /\ satis (Ms i) (r i) phi} IN U` by metis_tac[satis_in_world] >> fs[] >> `{i | i IN J /\ satis (Ms i) (r i) phi} ∩ {i | i IN J /\ x i = r i} IN U` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
	  `{i | i IN J /\ satis (Ms i) (r i) phi} INTER {i | i IN J /\ x i = r i} ⊆ {i | i IN J /\ satis (Ms i) (x i) phi}` by fs[SUBSET_DEF] >>
	  `{i | i IN J /\ satis (Ms i) (x i) phi} ⊆ J` by fs[SUBSET_DEF] >>
	  `{i | i IN J /\ satis (Ms i) (x i) phi} IN U` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
	  `{i | i IN J /\ g i = x i} = {i | i IN J /\ x i = g i}` by rw[EXTENSION,EQ_IMP_THM] >>
	  `{i | i IN J /\ satis (Ms i) (x i) phi} INTER {i | i IN J /\ g i = x i} IN U` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
	  `{i | i IN J /\ satis (Ms i) (x i) phi} INTER {i | i IN J /\ g i = x i} ⊆ {i | i IN J /\ satis (Ms i) (g i) phi}` by fs[SUBSET_DEF] >>
	  `{i | i IN J /\ satis (Ms i) (g i) phi} ⊆ J` by fs[SUBSET_DEF] >>
	  metis_tac[ultrafilter_def,proper_filter_def,filter_def]) >>
     `{i | i IN J /\ (Ms i).frame.rel (x' i) (g i)} ∩ {i | i IN J /\ satis (Ms i) (g i) phi} IN U`
       by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     `{i | i IN J /\ (Ms i).frame.rel (x' i) (g i) /\ satis (Ms i) (g i) phi} =
     {i | i IN J /\ (Ms i).frame.rel (x' i) (g i)} ∩ {i | i IN J /\ satis (Ms i) (g i) phi}`
       by rw[EXTENSION,EQ_IMP_THM] >>
     `{i | i IN J /\ (Ms i).frame.rel (x' i) (g i) /\ satis (Ms i) (g i) phi} ⊆
     {i | i IN J /\ x' i IN (Ms i).frame.world /\
     ?v. (Ms i).frame.rel (x' i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}`
       by (rw[SUBSET_DEF] >> qexists_tac `g x''` >> rw[]) >>
     `{i | i IN J /\ x' i IN (Ms i).frame.world /\
      ?v. (Ms i).frame.rel (x' i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} ⊆ J` by fs[SUBSET_DEF] >>
      metis_tac[ultrafilter_def,proper_filter_def,filter_def]))
(*-------------------------------half 2---------------------------------------------------*)
>- (`{i | i IN J /\ f i IN (Ms i).frame.world /\
      ?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} <> {}`
        by metis_tac[EMPTY_NOTIN_ultrafilter] >> fs[GSYM MEMBER_NOT_EMPTY] >>
     simp[PULL_EXISTS] >> rw[ultraproduct_rel] >>
     `?x g. (f IN fc /\
     ((!i. i IN J ==> g i IN (Ms i).frame.world) /\
     {i | i IN J /\ x i = g i} IN U) /\
     {i | i IN J /\ (Ms i).frame.rel (f i) (g i)} IN U) /\
     (!i. i IN J ==> (Ms i).frame.world <> {}) /\
     (!i. i IN J ==> x i IN (Ms i).frame.world) /\
     satis (ultraproduct_model U J Ms)
     {y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\ {i | i IN J /\ x i = y i} IN U} phi`
     suffices_by (rw[] >> qexists_tac `x'` >> rw[] (* 2 *)
                 >- (map_every qexists_tac [`f`,`g`] >> rw[])
		 >- metis_tac[MEMBER_NOT_EMPTY]) >>
     map_every qexists_tac
     [`\i. if (?v.
          (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\
          satis (Ms i) v phi) then CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
	  else CHOICE (Ms i).frame.world`,
     `\i. if (?v.
          (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\
          satis (Ms i) v phi) then CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
	  else CHOICE (Ms i).frame.world`]>> rw[] (* 8 *)
     >- (`{v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} <> {}`
          by (`v' IN {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}` by fs[] >>
	     metis_tac[MEMBER_NOT_EMPTY]) >>
	`CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} IN
	{v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}` by metis_tac[CHOICE_DEF] >>
	fs[])
     >- (`!i. i IN J ==> (Ms i).frame.world <> {}` by metis_tac[ultraproduct_world] >>
        `(Ms i).frame.world <> {}` by metis_tac[] >> metis_tac[CHOICE_DEF])
     >- metis_tac[ultrafilter_def,proper_filter_def,filter_def]
     >- (`{i | i IN J /\ f i IN (Ms i).frame.world /\
         ?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} ⊆
	{i | i IN J /\ (Ms i).frame.rel (f i)
        (if
           (?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi)
        then
            CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
        else CHOICE (Ms i).frame.world)}`
	  by (rw[SUBSET_DEF] >>
	     `{v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi} <> {}`
	       by (`v' IN {v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi}`
	             by fs[] >>
		  metis_tac[MEMBER_NOT_EMPTY]) >>
             `CHOICE {v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi} IN
	     {v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi}`
	       by metis_tac[CHOICE_DEF] >> fs[]) >>
	`{i | i IN J /\ (Ms i).frame.rel (f i)
        (if
           (?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi)
        then
            CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
        else CHOICE (Ms i).frame.world)} ⊆ J` by fs[SUBSET_DEF] >>
	metis_tac[ultrafilter_def,proper_filter_def,filter_def]) 
     >- metis_tac[ultraproduct_world]
     >- (`{v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} <> {}`
          by (`v' IN {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}` by fs[] >>
	     metis_tac[MEMBER_NOT_EMPTY]) >>
	`CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} IN
	{v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}` by metis_tac[CHOICE_DEF] >>
	fs[])
     >- (`!i. i IN J ==> (Ms i).frame.world <> {}` by metis_tac[ultraproduct_world] >>
        `(Ms i).frame.world <> {}` by metis_tac[] >> metis_tac[CHOICE_DEF])
     >- (`{i | i IN J /\
        satis (Ms i)
        (if
           (?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi)
        then
            CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
        else CHOICE (Ms i).frame.world) phi} IN U`
	  by (`{i | i IN J /\ f i IN (Ms i).frame.world /\
             ?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} ⊆
	     {i | i IN J /\ satis (Ms i)
             (if
             (?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi)
             then
             CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
             else CHOICE (Ms i).frame.world) phi}`
	       by (rw[SUBSET_DEF] >>
	          `{v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi} <> {}`
		    by (`v' IN {v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi}`
		          by fs[] >> metis_tac[MEMBER_NOT_EMPTY]) >>
		  `CHOICE {v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi} IN
		  {v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi}`
		    by metis_tac[CHOICE_DEF] >> fs[]) >>
             `{i | i IN J /\ satis (Ms i)
             (if
             (?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi)
             then
             CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
             else CHOICE (Ms i).frame.world) phi} ⊆ J` by fs[SUBSET_DEF] >>
	     metis_tac[ultrafilter_def,proper_filter_def,filter_def]) >>
        `{y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\
              {i | i IN J /\
                  (if
                  ?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi
                  then
                  CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
                  else CHOICE (Ms i).frame.world) = y i} IN U} IN (ultraproduct_model U J Ms).frame.world`
	  by
	  (`!i. i IN J ==> (Ms i).frame.world <> {}` by metis_tac[ultraproduct_world] >>
	  `?x.
            (!i. i IN J ==> x i IN (Ms i).frame.world) /\
          {y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\
              {i | i IN J /\
                  (if
                  ?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi
                  then
                  CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
                  else CHOICE (Ms i).frame.world) = y i} IN U} =
          {y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\ {i | i IN J /\ x i = y i} IN U}`
	  suffices_by metis_tac[ultraproduct_world] >>
	  qexists_tac
	  `\i. (if
             (?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi)
             then
             CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
             else CHOICE (Ms i).frame.world)` >> rw[] (* 2 *)
	  >- (`{v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} <> {}`
	       by (`v' IN {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}`
	             by fs[] >> metis_tac[MEMBER_NOT_EMPTY]) >>
	     `CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} IN
	     {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}`
	       by metis_tac[CHOICE_DEF] >> fs[])
	  >- metis_tac[CHOICE_DEF]) >>
	`(\i. (if
             (?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi)
             then
             CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
             else CHOICE (Ms i).frame.world)) IN
	{y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\
              {i | i IN J /\
                  (if
                  ?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi
                  then
                  CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
                  else CHOICE (Ms i).frame.world) = y i} IN U}`     
	  by (rw[] (* 2 *)
	     >- (Cases_on `?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi` (* 2 *)
	        >- (rw[] >>
		   `{v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} <> {}`
	             by (`v' IN {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}`
	                   by fs[] >> metis_tac[MEMBER_NOT_EMPTY]) >>
		   `CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} IN
	           {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}`
	             by metis_tac[CHOICE_DEF] >> fs[])
		>- (rw[] >> metis_tac[CHOICE_DEF,ultraproduct_world]))
	     >- metis_tac[ultrafilter_def,proper_filter_def,filter_def]) >> metis_tac[]))));



val prop_2_71 = store_thm(
  "prop_2_71",
  ``!U J Ms. (!i. i IN J ==> (Ms i) = M) /\ ultrafilter U J ==>
         !phi w. satis (ultraproduct_model U J Ms) {fw | Uequiv U J (models2worlds Ms) (\i.w) fw} phi <=> satis M w phi``,
  rw[EQ_IMP_THM] (* 2 *)
  >- (`!phi fc.
              fc IN (ultraproduct_model U J Ms).frame.world ==>
              (satis (ultraproduct_model U J Ms) fc phi <=>
               ?f.
                  f IN fc /\
                  {i | i IN J /\ satis (Ms i) (f i) phi} IN U)` by metis_tac[Los_modal_thm] >>
     `{fw | Uequiv U J (models2worlds Ms) (\i. w) fw} IN (ultraproduct_model U J Ms).frame.world`
       by metis_tac[satis_in_world] >>
     `?f. f IN {fw | Uequiv U J (models2worlds Ms) (\i. w) fw} /\ {i | i IN J /\ satis (Ms i) (f i) phi} IN U`
       by metis_tac[] >>
     fs[Uequiv_def,models2worlds_def,Cart_prod_def] >>
     `{i | i IN J /\ w = f i} ∩ {i | i IN J /\ satis (Ms i) (f i) phi} IN U`
       by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     `{i | i IN J /\ w = f i} ∩ {i | i IN J /\ satis (Ms i) (f i) phi} <> {}`
       by metis_tac[EMPTY_NOTIN_ultrafilter] >>
     fs[GSYM MEMBER_NOT_EMPTY] >> metis_tac[])
  >- (` !phi fc.
              fc IN (ultraproduct_model U J Ms).frame.world ==>
              (satis (ultraproduct_model U J Ms) fc phi <=>
               ?f.
                  f IN fc /\
                  {i | i IN J /\ satis (Ms i) (f i) phi} IN U)` by metis_tac[Los_modal_thm] >>
     `{fw | Uequiv U J (models2worlds Ms) (\i. w) fw} IN (ultraproduct_model U J Ms).frame.world`
       by (`w IN M.frame.world` by metis_tac[satis_in_world] >>
          metis_tac[ultraproduct_world_constant]) >>
     `?f. f IN {fw | Uequiv U J (models2worlds Ms) (\i. w) fw} /\ {i | i IN J /\ satis (Ms i) (f i) phi} IN U`
       suffices_by metis_tac[] >>
     qexists_tac `\i.w` >> rw[] (* 2 *)
     >- (fs[Uequiv_def,models2worlds_def,Cart_prod_def] >>
        `w IN M.frame.world` by metis_tac[satis_in_world] >>
	metis_tac[ultrafilter_def,proper_filter_def,filter_def,MEMBER_NOT_EMPTY])
     >- (`{i | i IN J /\ satis (Ms i) w phi} = J`
          suffices_by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
	rw[EXTENSION,EQ_IMP_THM])));





val folmodels2Doms_def = Define`
  folmodels2Doms FMS = \i. (FMS i).Dom`


 (* 
val _ = overload_on ("fP", “λp t. Pred p [t]”);
val _ = overload_on ("fR", “λw1 w2. Pred 0 [w1; w2]”); *)
(*
val ultraproduct_folmodel_def = Define`
   ultraproduct_folmodel U I FMS = 
    <| Dom := ultraproduct U I (folmodels2Doms FMS) ;
       Fun := \n fs fc. (\i. ((FMS i).Fun n (MAP ((\f. f i) o CHOICE) fs)) IN U);
       Pred := \p zs. ({i IN I | (FMS i).Pred p (MAP ((\f. f i) zs) o CHOICE) zs} IN U) |>`;
*)



val ultraproduct_folmodel_def = Define`
   ultraproduct_folmodel U I FMS = 
    <| Dom := ultraproduct U I (folmodels2Doms FMS) ;
       Fun := \n fs. {y | (!i. i IN I ==> (y i) IN (FMS i).Dom) /\
                          {i | i IN I /\ 
                               (y i) = (FMS i).Fun n (MAP (\fc. (CHOICE fc) i)fs)} IN U
                     };
       Pred := \p zs. {i | i IN I /\ (FMS i).Pred p (MAP (\fc. (CHOICE fc) i) zs)} IN U |>`;

Theorem thm_A_19_i_V_l3:
  !U I A m eqc. ultrafilter U I ==>  (m IN eqc /\ eqc IN (ultraproduct U I A)) ==>
      !i. i IN I ==> (m i) IN (A i)
Proof
  rw[ultraproduct_def,partition_def] >> fs[] >> fs[Cart_prod_def]
QED

Theorem thm_A_19_i_V_l2:
  !U I A m eqc. ultrafilter U I ==>  (m IN eqc /\ eqc IN (ultraproduct U I A)) ==> m ∈ Cart_prod I A
Proof
  rw[Cart_prod_def] >> metis_tac[thm_A_19_i_V_l3]
QED


Theorem thm_A_19_i_V_l1:
  !U I A m eqc. ultrafilter U I ==>  (m IN eqc /\ eqc IN (ultraproduct U I A)) ==> Uequiv U I A m m
Proof
  rw[] >> drule prop_A_16 >> rw[] >> first_x_assum (qspec_then `A` assume_tac) >> 
  `m IN (Cart_prod I' A)` suffices_by fs[equiv_on_def] >> metis_tac[thm_A_19_i_V_l2]
QED

Theorem thm_A_19_i_V_l4:
  !U I A. ultrafilter U I ==> !eqc. eqc IN (ultraproduct U I A) ==> (CHOICE eqc) IN eqc
Proof
  rw[] >> drule ultraproduct_eqclass_non_empty >> rw[] >> metis_tac[CHOICE_DEF]
QED


Theorem Uequiv_SYM:
  !U I A x y. ultrafilter U I ==> (Uequiv U I A x y <=> Uequiv U I A y x)
Proof
  rw[] >> drule prop_A_16 >> fs[equiv_on_def] >> fs[Uequiv_def] >> metis_tac[]
QED 
  

Theorem thm_A_19_i_V_l5:
  !U I A. ultrafilter U I ==> !eqc. eqc IN (ultraproduct U I A) ==> 
          {f | Uequiv U I A f (CHOICE eqc)} ∈ ultraproduct U I A
Proof
  rw[] >> rw[ultraproduct_def,partition_def] >> qexists_tac `CHOICE eqc` >> rw[] (* 2 *)
  >- (irule thm_A_19_i_V_l2 >> map_every qexists_tac [`U`,`eqc`] >> rw[] >> irule thm_A_19_i_V_l4 >>
     metis_tac[])
  >- (`{f | Uequiv U I' A f (CHOICE eqc)} =  {f | Uequiv U I' A (CHOICE eqc) f}` by 
        (rw[EXTENSION] >> metis_tac[Uequiv_SYM]) >>
     rw[EXTENSION] >> rw[Uequiv_def] >> eq_tac >> rw[] (* 2 *) >> 
     `{i | i ∈ I' ∧ x i = CHOICE eqc i} = {i | i ∈ I' ∧ CHOICE eqc i = x i}` 
           by (rw[EXTENSION] >> metis_tac[]) >> metis_tac[])
QED

Theorem thm_A_19_i_Fn_l1:
  !σ U I A. IMAGE σ 𝕌(:num) ⊆ ultraproduct U I A ==> (!i. i IN I ==> A i <> {})
Proof
  rw[] >> fs[ultraproduct_def,partition_def,Cart_prod_def] >> strip_tac >> 
  `{t |
         ∃x.
             (∀i. i ∈ I' ⇒ x i ∈ A i) ∧
             t = {y | (∀i. i ∈ I' ⇒ y i ∈ A i) ∧ Uequiv U I' A x y}} = {}`
    by (SPOSE_NOT_THEN ASSUME_TAC >> fs[GSYM MEMBER_NOT_EMPTY] >> metis_tac[MEMBER_NOT_EMPTY]) >>
  fs[IMAGE_EQ_EMPTY]
QED



Theorem thm_A_19_i:
  !t U I. ultrafilter U I ==>
          !σ FMS. IMAGE σ (univ(:num)) ⊆ ultraproduct U I (folmodels2Doms FMS) ==>
             (!i ff ll. i IN I ==> (FMS i).Fun ff ll IN (FMS i).Dom) ==>
          termval (ultraproduct_folmodel U I FMS) σ t = 
          {f | Uequiv U I (folmodels2Doms FMS) f 
               (\i. termval (FMS i) (\n. CHOICE (σ n) i) t)}
Proof
completeInduct_on `term_size t` >> rw[] >> Cases_on `t` (* 2 *)
  >- (rw[termval_def] >> irule equiv_on_same_partition >> 
     map_every qexists_tac [`Uequiv U I' (folmodels2Doms FMS)`, 
                            `Cart_prod I' (folmodels2Doms FMS)`, `CHOICE (σ n)`,`CHOICE (σ n)`] >>
     rw[] (* 6 *)
     >- (* uequiv is equiv rel so refl *) 
        (irule thm_A_19_i_V_l1 >> rw[] >>
        qexists_tac `σ n` >> rw[] (* 2 *)
        >- (irule thm_A_19_i_V_l4 >> 
           map_every qexists_tac [`(folmodels2Doms FMS)`,`I'`,`U`] >> rw[] >> 
           fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
        >- (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]))
       
     >- (* each world is non empty *) 
        (irule thm_A_19_i_V_l4 >> 
           map_every qexists_tac [`(folmodels2Doms FMS)`,`I'`,`U`] >> rw[] >> 
           fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
     >- (* uequiv is equiv *) 
        (`Uequiv U I' (folmodels2Doms FMS) (CHOICE (σ n)) (CHOICE (σ n))`
           by (irule thm_A_19_i_V_l1 >> rw[] >>
               qexists_tac `σ n` >> rw[] (* 2 *)
               >- (irule thm_A_19_i_V_l4 >> 
                  map_every qexists_tac [`(folmodels2Doms FMS)`,`I'`,`U`] >> rw[] >> 
                  fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
               >- (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])) >>
        `(λi. CHOICE (σ n) i) = CHOICE (σ n)` suffices_by metis_tac[] >> simp[FUN_EQ_THM])
     >- (* definition of ultraprod *) 
        (`partition (Uequiv U I' (folmodels2Doms FMS))
          (Cart_prod I' (folmodels2Doms FMS)) = ultraproduct U I' (folmodels2Doms FMS)`
          by rw[ultraproduct_def] >> rw[] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) 
     >- (* definition of partition *) 
        (`partition (Uequiv U I' (folmodels2Doms FMS))
          (Cart_prod I' (folmodels2Doms FMS)) = ultraproduct U I' (folmodels2Doms FMS)`
          by rw[ultraproduct_def] >> rw[] >> 
        `(λi. CHOICE (σ n) i) = CHOICE (σ n)` by (rw[FUN_EQ_THM] >> fs[]) >> fs[] >> 
        irule thm_A_19_i_V_l5 >> rw[] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) 
     >- (* proved thm *) metis_tac[prop_A_16]) 
  >- Cases_on `l = []`
   >- (fs[] >> rw[termval_def,ultraproduct_folmodel_def] (* seems fine, nothing tricky *)) 
   >- rw[termval_def,ultraproduct_folmodel_def] >>
     qabbrev_tac `UPM  =  <|Dom := ultraproduct U I' (folmodels2Doms FMS);
                         Fun :=
                           (λn fs.
                                {y |
                                 (∀i. i ∈ I' ⇒ y i ∈ (FMS i).Dom) ∧
                                 {i |
                                  i ∈ I' ∧
                                  y i =
                                  (FMS i).Fun n (MAP (λfc. CHOICE fc i) fs)} ∈
                                 U});
                         Pred :=
                           (λp zs.
                                {i |
                                 i ∈ I' ∧
                                 (FMS i).Pred p (MAP (λfc. CHOICE fc i) zs)} ∈
                                U)|>` >> rw[MAP_MAP_o,o_DEF] >> 
    irule equiv_on_same_partition >>
    map_every qexists_tac [`Uequiv U I' (folmodels2Doms FMS)`,
                           `Cart_prod I' (folmodels2Doms FMS)`,
                           `\i. (FMS i).Fun n (MAP (λa. CHOICE (termval UPM σ a) i) l)`,
                           `λi. (FMS i).Fun n
                           (MAP (λa. termval (FMS i) (λn. CHOICE (σ n) i) a) l)`] >> rw[]  >>
    `UPM = (ultraproduct_folmodel U I' FMS)`
       by fs[Abbr`UPM`,ultraproduct_folmodel_def] (* 6 *)
    >- `(λi. (FMS i).Fun n (MAP (λa. CHOICE (termval UPM σ a) i) l))=
        (λi. (FMS i).Fun n (MAP (λa. CHOICE 
                        {f |
                         Uequiv U I' (folmodels2Doms FMS) f
                           (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} i) l))` 
            by (rw[FUN_EQ_THM] >> AP_TERM_TAC >> irule MAP_LIST_EQ >> rw[] >>
                `(termval (ultraproduct_folmodel U I' FMS) σ m) = 
                 {f | Uequiv U I' (folmodels2Doms FMS) f
                     (λi. termval (FMS i) (λn. CHOICE (σ n) i) m)}` suffices_by metis_tac[] >>
                rw[] >> first_x_assum irule >> rw[] >> drule term_size_lemma >> strip_tac >>
                first_x_assum (qspec_then `n` assume_tac) >> fs[] >> metis_tac[]) >> rw[] >> 
      rw[Uequiv_def] (* 4 *)
      >- (`!i. i IN I' ==> folmodels2Doms FMS i ≠ ∅` suffices_by metis_tac[] >>
         drule thm_A_19_i_Fn_l1 >> rw[])
      >- rw[Cart_prod_def,folmodels2Doms_def]
      >- rw[Cart_prod_def,folmodels2Doms_def]
      >- `{i | i IN I' /\
              (FMS i).Fun n (MAP (λa. CHOICE 
                        {f |
                         Uequiv U I' (folmodels2Doms FMS) f
                           (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} i) l) =
               (FMS i).Fun n
                 (MAP (λa. termval (FMS i) (λn. CHOICE (σ n) i) a) l)} IN U` 
         suffices_by fs[Uequiv_def] >> 
        qmatch_abbrev_tac `BIGSET IN U` >> 
        `{i | i IN I' /\ 
         (MAP
              (λa.
                   CHOICE
                     {f |
                      Uequiv U I' (folmodels2Doms FMS) f
                        (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} i) l) = 
         (MAP (λa. termval (FMS i) (λn. CHOICE (σ n) i) a) l)
         } ⊆ BIGSET` by rw[SUBSET_DEF,Abbr`BIGSET`] >> 
        `{i |
         i ∈ I' ∧
         MAP
           (λa.
                CHOICE                  {f |
                   Uequiv U I' (folmodels2Doms FMS) f
                     (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} i) l =
         MAP (λa. termval (FMS i) (λn. CHOICE (σ n) i) a) l} IN U` suffices_by
          (qmatch_abbrev_tac `BS IN U ==> BIGSET IN U` >> 
          fs[ultrafilter_def,proper_filter_def,filter_def] >> 
          `BIGSET ⊆ I' /\ BS ⊆ I'` suffices_by metis_tac[] >> fs[Abbr`BIGSET`,Abbr`BS`,SUBSET_DEF]) >>
        (* the above reduce the goal into proving another set is in U *)
        `{i |
         i ∈ I' ∧
         (!a. MEM a l ==> 
            CHOICE
                  {f |
                   Uequiv U I' (folmodels2Doms FMS) f
                     (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} i = 
                 termval (FMS i) (λn. CHOICE (σ n) i) a)} ⊆
        {i |
         i ∈ I' ∧
         MAP
           (λa.
                CHOICE
                  {f |
                   Uequiv U I' (folmodels2Doms FMS) f
                     (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} i) l =
         MAP (λa. termval (FMS i) (λn. CHOICE (σ n) i) a) l}` by 
         (rw[SUBSET_DEF] >> irule MAP_LIST_EQ >> fs[] >> qmatch_abbrev_tac `BS IN U` >> 
         `{i |
         i ∈ I' ∧
         ∀a.
             MEM a l ⇒
             CHOICE
               {f |
                Uequiv U I' (folmodels2Doms FMS) f
                  (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} i =
             termval (FMS i) (λn. CHOICE (σ n) i) a} IN U` suffices_by
              (qmatch_abbrev_tac `BS' IN U ==> BS IN U` >> 
              fs[ultrafilter_def,proper_filter_def,filter_def] >> 
              `BS ⊆ I' /\ BS' ⊆ I'` suffices_by metis_tac[] >> fs[Abbr`BS`,Abbr`BS'`,SUBSET_DEF]) >> 
         qmatch_abbrev_tac `SS IN U` >> 
         `BIGINTER ({{i | i IN I' /\ CHOICE
                  {f |
                   Uequiv U I' (folmodels2Doms FMS) f
                     (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} i =
                termval (FMS i) (λn. CHOICE (σ n) i) a} | MEM a l}) IN U` suffices_by 
             (qmatch_abbrev_tac `BS' IN U ==> SS IN U` >> 
             `BS' ⊆ SS` suffices_by
                  (fs[ultrafilter_def,proper_filter_def,filter_def] >> 
                   `SS ⊆ I' /\ BS' ⊆ I'` suffices_by metis_tac[] >> rw[] (* 2 *)
                   >- (rw[SUBSET_DEF,Abbr`SS`] >> fs[])
                   >- (rw[SUBSET_DEF] >> fs[Abbr`BS'`] >> fs[PULL_EXISTS,PULL_FORALL] >> 
                       (* cheated ! need extra case argument for whether l is empty *)
                      `?mm. MEM mm l` by cheat >> metis_tac[])) >>
              rw[Abbr`BS'`,Abbr`SS`,SUBSET_DEF] >> fs[PULL_EXISTS,PULL_FORALL] >> 
              `?mm. MEM mm l` by cheat (* cheated! same reason as above*) >> metis_tac[]) >>
        `!a. MEM a l ==> {i |
            i ∈ I' ∧
            CHOICE
              {f |
               Uequiv U I' (folmodels2Doms FMS) f
                 (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} i =
            termval (FMS i) (λn. CHOICE (σ n) i) a} IN U` suffices_by cheat (* cheated! need a lemma here saying ultrafilter closed under finite inter *) >> rw[] >> 
        `Uequiv U I' (folmodels2Doms FMS)
         (\i.CHOICE
           {f |
            Uequiv U I' (folmodels2Doms FMS) f
              (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} i) 
         (\i.termval (FMS i) (λn. CHOICE (σ n) i) a)` suffices_by
          (rw[Uequiv_def] >> fs[] >> cheat (* cheated! need assumption  (∀i. i ∈ I' ⇒ folmodels2Doms FMS i ≠ ∅) *)) >> 
        `(λi.
               CHOICE
                 {f |
                  Uequiv U I' (folmodels2Doms FMS) f
                    (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} i) =
         CHOICE
                 {f |
                  Uequiv U I' (folmodels2Doms FMS) f
                    (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)}` by rw[FUN_EQ_THM] >> rw[] >> 
        `CHOICE
             {f |
              Uequiv U I' (folmodels2Doms FMS) f
                (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} IN 
         {f |
              Uequiv U I' (folmodels2Doms FMS) f
                (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)}` suffices_by fs[] >> 
        `{f |
         Uequiv U I' (folmodels2Doms FMS) f
           (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} <> {}` suffices_by fs[CHOICE_DEF] >>
        rw[GSYM MEMBER_NOT_EMPTY] >> qexists_tac `(λi. termval (FMS i) (λn. CHOICE (σ n) i) a)` >> 
        rw[] >> drule prop_A_16 >> rw[] >> 
        first_x_assum (qspec_then `(folmodels2Doms FMS)` assume_tac) >> fs[equiv_on_def] >> 
        `(λi. termval (FMS i) (λn. CHOICE (σ n) i) a) IN Cart_prod I' (folmodels2Doms FMS)` suffices_by metis_tac[] >> fs[Cart_prod_def] >> rw[folmodels2Doms_def] >> cheat 
    (* cheated!!! need a lemma (λi. termval (FMS i) (λn. CHOICE (σ n) i) a) ∈
        Cart_prod I' (folmodels2Doms FMS)-----termval (FMS i) (λn. CHOICE (σ n) i) a ∈ (FMS i).Dom *)
      (* 5 goals remain *)
   >- (* by definition of ultrafilter *) cheat
   >- (* Uequiv is equiv_on *) cheat
   >- (* in card prod by definition, need lemmas *) cheat
   >- (* same as above *) cheat
   >- metis_tac[prop_A_16]
QED



Theorem thm_A_19_i:
  !t U I. ultrafilter U I ==>
          !σ. IMAGE σ (univ(:num)) ⊆ ultraproduct U I (folmodels2Doms FMS) ==>
             
          termval (ultraproduct_folmodel U I FMS) σ t = 
          {f | Uequiv U I (folmodels2Doms FMS) f 
               (\i. termval (FMS i) (\n. CHOICE (σ n) i) t)}
Proof
cheat
QED

Theorem thm_A_19_ii:
   !U I phi. ultrafilter U I ==>
         (feval (ultraproduct_folmodel U I FMS) σ phi <=>
         {i | i IN I /\ feval (FMS i) (\x. (CHOICE (σ x)) i) phi} IN U)
Proof
  Induct_on `phi`
  >- cheat
  >- rw[feval_def] >> rw[ultraproduct_folmodel_def,feval_def] >> fs[MAP_MAP_o,o_DEF] >> 
     `((ultraproduct_folmodel U I' FMS).Pred n
       (MAP (\t. {f |
              Uequiv U I' (folmodels2Doms FMS) f
                (λi. termval (FMS i) (λn. CHOICE (σ n) i) t)}) l)) ⇔
        {i |
         i ∈ I' ∧
         (FMS i).Pred n (MAP (termval (FMS i) (λx. CHOICE (σ x) i)) l)} ∈ U`
     
     rw
      cheat


  >- rw[feval_def] >> rw[EQ_IMP_THM] >>
     `{i |
         i ∈ I' ∧
         ¬(feval (FMS i) (λx. CHOICE (σ x) i) phi \/
          feval (FMS i) (λx. CHOICE (σ x) i) phi')} ∈ U` suffices_by cheat >>
     ` {i | i ∈ I' ∧
         ¬(feval (FMS i) (λx. CHOICE (σ x) i) phi)} IN U \/
        {i |
         i ∈ I' ∧
          feval (FMS i) (λx. CHOICE (σ x) i) phi'} IN U` suffices_by cheat >> cheat
  >- rw[feval_def] >> rw[EQ_IMP_THM] >> 
     `∀a.
            a ∈ (ultraproduct_folmodel U I' FMS).Dom ⇒
            {i | i ∈ I' ∧ feval (FMS i) (λx. CHOICE (σ(|n |-> a|) x) i) phi} ∈ U` by cheat >>
     
 
    `!n phi. FALL n phi = fNOT (fEXISTS n (fNOT phi))` by cheat >> rw[] >>
    ` ∀n U I.
            ultrafilter U I ⇒
            (feval (ultraproduct_folmodel U I FMS) σ (fNOT (fEXISTS n (fNOT phi))) ⇔
             {i | i ∈ I ∧ feval (FMS i) (λx. CHOICE (σ x) i) (fNOT (fEXISTS n (fNOT phi)))} ∈
             U)` suffices_by cheat >>
     rw[EQ_IMP_THM] 
     >- `{i |
         i ∈ I' ∧
         ?a. a ∈ (FMS i).Dom /\ ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi} NOTIN
        U` suffices_by cheat >>
        `∀a.
            a ∈ (ultraproduct_folmodel U I' FMS).Dom ⇒
            {i | i ∈ I' ∧ feval (FMS i) (λx. CHOICE (σ(|n |-> a|) x) i) phi} ∈ U` by cheat >> 
        `{i | i ∈ I' ∧ ?a.feval (FMS i) (λx. CHOICE (σ⦇n ↦ a⦈ x) i) phi /\ a ∈ (ultraproduct_folmodel U I' FMS).Dom} IN U` by cheat



 >> rw[ultraproduct_folmodel_def,feval_def] >> 
     qabbrev_tac `UPM = <|Dom := ultraproduct U I' (folmodels2Doms FMS);
                    Fun :=
                      (λn fs.
                           {y |
                            (∀i. i ∈ I' ⇒ y i ∈ (FMS i).Dom) ∧
                            {i |
                             i ∈ I' ∧
                             y i = (FMS i).Fun n (MAP (λfc. CHOICE fc i) fs)} ∈
                            U});
                    Pred :=
                      (λp zs.
                           {i |
                            i ∈ I' ∧
                            (FMS i).Pred p (MAP (λfc. CHOICE fc i) zs)} ∈ U)|>` >> fs[MAP_MAP_o] >> 
  rw[o_DEF] >> 
  cheat
  >- rw[feval_def] >> rw[EQ_IMP_THM] >> 
     Cases_on `{i | i ∈ I' ∧ feval (FMS i) (λx. CHOICE (σ x) i) phi} ∈ U` 
     >- first_x_assum drule >> rw[] >> cheat >>
  >- 

 (* two directions *)
 >- SPOSE_NOT_THEN ASSUME_TAC >> 
    `{i |
         i ∈ I' ∧
         ?a. a ∈ (FMS i).Dom /\¬ feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi} IN
        U` by cheat >> 
    qabbrev_tac `f = \i. CHOICE {a | a IN (FMS i).Dom /\ ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi}` >>
    `{i |
         i ∈ I' ∧
         ∃a. a ∈ (FMS i).Dom ∧ ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi} = 
     {i |
         i ∈ I' ∧
         ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ f i⦈ phi}` by cheat >> 
   `{i | i ∈ I' ∧ ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ f i⦈ phi} IN U` by metis_tac[] >>
   `{i | i ∈ I' ∧ feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ f i⦈ phi} NOTIN U` by cheat >>
   `{i | i ∈ I' ∧ feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ f i⦈ phi} = 
    {i | i ∈ I' ∧ feval (FMS i) (λx. CHOICE (σ(|n |-> {y | Uequiv U I' (folmodels2Doms FMS) y f}|)  x) i) phi}` by cheat >> 
   `!σ.  (feval (ultraproduct_folmodel U I' FMS) σ phi ⇔
             {i | i ∈ I' ∧ feval (FMS i) (λx. CHOICE (σ x) i) phi} ∈ U)` by cheat >> 
   `?a. a IN (ultraproduct_folmodel U I' FMS).Dom /\
            ¬feval (ultraproduct_folmodel U I' FMS) σ⦇n ↦ a⦈ phi` suffices_by metis_tac[] >>
   qexists_tac `{y | Uequiv U I' (folmodels2Doms FMS) y f}` >> rw[] >- cheat 
   first_x_assum (qspecl_then `)

   

QED



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

(*
Theorem expansion_shift_feval:
  !M A M' f. expansion (mm2folm M) A M' f ==>
            !phi. (∀c. c ∈ FC phi ⇒ c < CARD A) ==>
                 !σ. 
                    IMAGE σ (univ(:num)) ⊆ M.frame.world ==>
                    (feval M' σ phi <=> 
                    feval (mm2folm M) (shift_valuation (CARD A) σ f) (shift_form (CARD A) phi))
Proof
  rw[] >> Induct_on `phi` (* 4 *)
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
  >- rw[FC_def] >> first_x_assum 
QED
*)

Theorem expansion_shift_feval:
  !M A M' f. expansion (mm2folm M) A M' f ==>
            !phi σ. (∀c. c ∈ FC phi ⇒ c < CARD A) ==>
                  
                    IMAGE σ (univ(:num)) ⊆ M.frame.world ==>
                    (feval M' σ phi <=> 
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


Theorem mm2folm_ultrapower_folmodel_comm:
  !phi U I. 
    ultrafilter U I ==>
    (feval (mm2folm (ultraproduct_model U I MS)) σ phi <=>
    feval (ultraproduct_folmodel U I (\i. mm2folm (MS i))) σ phi)
Proof
  cheat
QED



Theorem lemma_2_73:
  !U I MS M. 
         countably_incomplete U I /\
         (!i. i IN I ==> MS i = M) ==>
             countably_saturated (mm2folm (ultraproduct_model U I MS))
Proof
  rw[countably_saturated_def,n_saturated_def,consistent_def,ftype_def,frealizes_def] >>
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

