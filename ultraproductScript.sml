open HolKernel Parse boolLib bossLib;
open ultrafilterTheory;
open HolKernel Parse boolLib bossLib;
open chap1Theory;
open pred_setTheory;
open relationTheory;
open arithmeticTheory;
open set_relationTheory;
open pairTheory;

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


Theorem A_19_i:
  !t σp σs.
      (!i. i IN I ==> (σs i n) IN (σp n)) ==> 
      termval (ultraproduct_folmodel U I FMS) σp t =
      {y | (!i. i IN I ==> (y i) IN (FMS i).Dom) /\
           {i | i IN I /\ 
                (y i) = termval (FMS i) (σs i) t} IN U
                     }
Proof
  
QED

Theorem mm2folm_fsatis_ST_EXISTS:
  !M f. ?mf. feval (mm2folm M) σ(|x |-> w|) f <=> 
             feval (mm2folm M) σ(|x |-> w|) (ST x mf)
Proof
  Induct_on `f`
  
  `(?a b. l = [a;b]) \/ (?a. l = [a])` by cheat >> 
  >- qexists_tac `VAR n` >> rw[ST_def,termval_def,mm2folm_def,APPLY_UPDATE_THM]
  
 


  >- qexists_tac `

  >- Cases_on `(?a b. l = [a;b]) \/ (?a. l = [a])` 

rw[] >> 
     

   qexists_tac 




  `∃w.
            w ∈ (mm2folm (ultraproduct_model U I' MS)).Dom ∧
            ∀σ phi.
                IMAGE σ 𝕌(:num) ⊆ M'.Dom ∧ phi ∈ G ⇒ 
                ?f. f IN w /\ {i| i IN I' /\ fsatis M σ⦇x ↦ f i⦈ phi} IN U 


fsatis M' σ⦇x ↦ w⦈ phi` 
    (mm2folm (ultraproduct_model U I' MS))
  `fsatis (mm2folm (ultraproduct_model U I' MS))
          σ⦇x ↦
             {f |
              (∀i. i ∈ I' ⇒ f i ∈ M.frame.world) ∧
              {i | i ∈ I' ∧ f i = fi i} ∈ U}⦈ phi'` suffices_by cheat >>
  `?f0. f0 IN {f |
              (∀i. i ∈ I' ⇒ f i ∈ M.frame.world) ∧
              {i | i ∈ I' ∧ f i = fi i} ∈ U} /\
        {i| i IN I' /\ !σ. fsatis (mm2folm M) σ(|x |-> (f0 i)|) phi'} IN U` 
   suffices_by cheat >>
  qexists_tac `fi` >> rw[]
  >- cheat
  >- cheat 
     `!i σ. i IN I' ==> fsatis (mm2folm M) σ⦇x ↦ fi i⦈ phi'` suffices_by cheat


fsatis (mm2folm (ultraproduct_model U I' MS))
          σ⦇x ↦
             {f |
              (∀i. i ∈ I' ⇒ f i ∈ M.frame.world) ∧
              {i | i ∈ I' ∧ f i = fi i} ∈ U}⦈ phi'                                                                 

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
        rw[] >> cheat))
QED


Theorem Los_mm2folm_thm:
  !U I MS.
     ultrafilter U I ==> (!i. i IN I ==> MS i = M) ==> 
    !phi. FV phi ⊆ {x} ==>
       !fc. fc IN (ultraproduct_model U I MS).frame.world ==>
             
             !σ. (feval (mm2folm (ultraproduct_model U I MS)) σ(|x |-> fc|) phi <=>
                 ?f0. f0 IN (σ x) /\
                      {i | i IN I /\ !σ0. feval (mm2folm M) σ0(|x |-> (f0 i)|) phi} IN U)
Proof
  strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>
  strip_tac >> Induct_on `phi` (* 4 *)
  >- fs[FV_def] >> rw[] >> cheat
  >- rw[FV_def,EQ_IMP_THM] >> qexists_tac `CHOICE fc` >> rw[]
     >- cheat
     >- `l = [a;b] \/ l = [c]` by cheat 
        >- `n = 0 /\ (ultraproduct_model U I' MS).frame.rel (termval (mm2folm (ultraproduct_model U I' MS)) σ⦇x ↦ fc⦈ a) (termval (mm2folm (ultraproduct_model U I' MS)) σ⦇x ↦ fc⦈ b)` by cheat >> fs[ultraproduct_rel] >>
           `{i |
         i ∈ I' ∧
         ∀σ0.
         M.frame.rel 
               (termval (mm2folm M) σ0⦇x ↦ CHOICE fc i⦈ a)
               (termval (mm2folm M) σ0⦇x ↦ CHOICE fc i⦈ b)} ∈ U` suffices_by cheat
        `{i | i ∈ I' ∧ (MS i).frame.rel (f i) (g i)} =
        {i |
         i ∈ I' ∧
         ∀σ0.
             M.frame.rel (termval (mm2folm M) σ0⦇x ↦ CHOICE fc i⦈ a)
               (termval (mm2folm M) σ0⦇x ↦ CHOICE fc i⦈ b)}` suffices_by cheat >>
        rw[EXTENSION,EQ_IMP_THM]
        `(f x') = (termval (mm2folm M) σ0⦇x ↦ CHOICE fc x'⦈ a)` suffices_by cheat >>
        Cases_on `a` >> rw[termval_def]
        >- `f x' = (CHOICE fc) x'` suffices_by cheat


fs[]


         fs[mm2folm_def]
QED 


`?fr. fr IN w /\ 
        {i | i IN I' /\ feval M (f i) (shift_form (CARD A) phi)} IN U`

Theorem lemma_2_73:
  !U I MS M. 
         countably_incomplete U I /\
         (!i. i IN I ==> MS i = M) ==> 
             countably_saturated (mm2folm (ultraproduct_model U I MS))
Proof
  rw[countably_saturated_def,n_saturated_def] >>
  `countable G` by cheat >> fs[countable_def] >>
  `?In. (!n: num. In (n+1) ⊆ In n) /\
        (!n. (In n) IN U) /\
        BIGINTER {(In n)| n IN (univ (:num))} = {}` by cheat >>
  `?k. BIJ k (univ(:num)) G` by cheat >> 
  rw[frealizes_def] >> 
  `∃w.
                 w ∈ M'.Dom ∧
                 ∀σ phi.
                     IMAGE σ 𝕌(:num) ⊆ M'.Dom ∧ phi ∈ G ⇒
                     feval (mm2folm (ultraproduct_model U I' MS)) 
                           (shift_valuation (CARD A) σ⦇x ↦ w⦈ f)
                       (shift_form (CARD A) phi)` suffices_by cheat >> 
  qexists_tac `w` >> rw[]
  >- cheat 
  >- fs[consistent_def] >> 
     `∀G0.
            FINITE G0 ∧ G0 ⊆ G ⇒
            ∃σ. IMAGE σ 𝕌(:num) ⊆ M'.Dom ∧ ∀phi. phi ∈ G0 ⇒ 
                feval (mm2folm (ultraproduct_model U I' MS)) (shift_valuation (CARD A) σ f)
                (shift_form (CARD A) phi)` by cheat >>


     `∀G0.
                 FINITE G0 ∧ G0 ⊆ G ⇒
                 ∃σ.
                     IMAGE σ 𝕌(:num) ⊆ M'.Dom ∧
                     ∀phi.
                         phi ∈ G0 ⇒
                         ?f0. f0 IN ((shift_valuation (CARD A) σ f) (x + CARD A))
                              {i| i IN I /\ !σ0. feval (mm2folm M) 



}
                         feval (mm2folm (ultraproduct_model U I' MS))
                           (shift_valuation (CARD A) σ f)
                           (shift_form (CARD A) phi)`
    

  `?fr. fr IN w /\ 
        {i | i IN I' /\ feval M (f i) (shift_form (CARD A) phi)} IN U`



  qabbrev_tac 
   `Xn = \n. if n = 0 then (In 0)
             else ((In n) ∩ 
                  (if (?σ. !m. m < n ==> fsatis (mm2folm M) σ (k m)) then I' else {}))` >>
  rw[frealizes_def] >> 
  `∃w.
      w ∈ (mm2folm (ultraproduct_model U I' MS)).Dom ∧
            ∀σ phi.
                IMAGE σ 𝕌(:num) ⊆ M'.Dom ∧ phi ∈ G ⇒ fsatis M' σ⦇x ↦ w⦈ phi`
   suffices_by metis_tac[expansion_def] >>
  qabbrev_tac `ni = \i. MAX_SET { n | i IN In n}` >> 
  qabbrev_tac `fi = \i. if (ni i = 0) then CHOICE M.frame.world 
                   else (CHOICE 
                       {w | w IN M.frame.world /\ 
                           (!m. m <= (ni i) ==> ?σ. fsatis (mm2folm M) σ(|x |-> w|) (k m))})`
  `!f. f IN G ==> ?mf. feval M' σ(|x |-> w|) f <=> 
                       feval M' σ(|x |-> w|) (ST x mf)` by cheat
  `∃w.
            w ∈ (mm2folm (ultraproduct_model U I' MS)).Dom ∧
            ∀σ phi.
                IMAGE σ 𝕌(:num) ⊆ M'.Dom ∧ phi ∈ G0 ⇒ fsatis M' σ⦇x ↦ w⦈ (ST x phi)` suffices_by cheat >> 

  `∃w.
      w ∈ (mm2folm (ultraproduct_model U I' MS)).Dom ∧
            ∀σ phi.
                IMAGE σ 𝕌(:num) ⊆ M'.Dom ∧ phi ∈ G0 ⇒
                satis (ultraproduct_model U I' MS) w phi` suffices_by cheat >>
  `∃w.
            w ∈ (mm2folm (ultraproduct_model U I' MS)).Dom ∧
            ∀σ phi.
                IMAGE σ 𝕌(:num) ⊆ M'.Dom ∧ phi ∈ G0 ⇒
                ?rp. rp IN w /\ {i | i IN I' /\ satis M (rp i) phi} IN U`
  qexists_tac `{f | (!i. i IN I' ==> (f i) IN M.frame.world) /\
                    {i | i IN I' /\ f i = fi i} IN U}` >> rw[]
  >- cheat
  >- `?f0. f0 IN {f |
              (∀i. i ∈ I' ⇒ f i ∈ M.frame.world) ∧
              {i | i ∈ I' ∧ f i = fi i} ∈ U} /\
          {i | i IN I' /\ (!σ. fsatis M' σ(|x |-> (f0 i)|) phi)} IN U` 
  


  Induct_on `f`


  ho_match_mp_tac form_induction >> rw[]
  (* trivial cheat *)
  


(ultraproduct_model U J MS).frame.world


                  {i | i IN I' /\ (?w. w IN M.frame.world /\
                  !m. m < n ==> satis M w (k m))}`

QED


Theorem Los_Thm :
  !D I. ultrafilter D I ==> 
        !phi. 
             (feval σ (ultraproduct_model U I MS) phi) <=> 
             {i IN I | feval (\n. σ n i) (MS i) phi} IN U
Proof


QED





val _ = export_theory();

