open HolKernel Parse boolLib bossLib;
open ultrafilterTheory;
open ultrafilterTheory;

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

val prop_2_71 = store_thm(
  "prop_2_71",
  ``!U I MS. (!i. i IN I ==> (MS i) = M) /\ ultrafilter U I ==>
         !phi. satis M w phi <=> satis (ultraproduct_model U I MS) {fw | Uequiv U I (models2worlds MS) (\i.w) fw} phi``,
  strip_tac >> strip_tac >> strip_tac >> strip_tac >> Induct_on `phi` >> rw[] (* 5 *)
  >- (rw[EQ_IMP_THM,satis_def] (* 4 *)
     >- (rw[ultraproduct_model_def,ultraproduct_def] >> rw[partition_def] >>
        qexists_tac `\i.w` >> rw[] (* 2 *)
	>- (rw[Cart_prod_def] >> rw[models2worlds_def])
	>- (rw[Uequiv_def] >> simp[EXTENSION] >> metis_tac[]))
     >- (rw[ultraproduct_model_def] >> qexists_tac `\i.w` >> rw[] (* 2 *)
        >- (`(Uequiv U I' (models2worlds MS)) equiv_on (Cart_prod I' (models2worlds MS))` by metis_tac[prop_A_16] >>
	   fs[equiv_on_def] >>
	   `(λi. w) IN (Cart_prod I' (models2worlds MS))` suffices_by metis_tac[] >>
	   rw[models2worlds_def,Cart_prod_def])
	>- (`!i. i IN I' ==> w IN ((MS i).valt) a` by rw[] >>
	   `{i | i ∈ I' ∧ w ∈ (MS i).valt a} = I'` by (simp[EXTENSION] >> metis_tac[]) >>
	   fs[ultrafilter_def,proper_filter_def,filter_def]))
     >- (fs[ultraproduct_model_def,models2worlds_def,ultraproduct_def] >> fs[Uequiv_def] >> fs[Cart_prod_def] >>
        `I' <> {}` by fs[ultrafilter_def,proper_filter_def,filter_def] >>
	`?i. i IN I'` by metis_tac[MEMBER_NOT_EMPTY] >>
	metis_tac[])
     >- (fs[ultraproduct_model_def,models2worlds_def,ultraproduct_def] >> fs[Uequiv_def,Cart_prod_def] >>
        `({i | i ∈ I' ∧ w = f i} INTER {i | i ∈ I' ∧ f i ∈ (MS i).valt a}) IN U` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
	`{i | i ∈ I' ∧ w = f i} INTER {i | i ∈ I' ∧ f i ∈ (MS i).valt a} <> {}` by metis_tac[EMPTY_NOTIN_ultrafilter] >>
	`?i. i IN ({i | i ∈ I' ∧ w = f i} INTER {i | i ∈ I' ∧ f i ∈ (MS i).valt a})` by metis_tac[MEMBER_NOT_EMPTY] >>
	fs[] >> metis_tac[]))
  >- rw[satis_def,EQ_IMP_THM]
  >- rw[satis_def,EQ_IMP_THM]
  >- (rw[satis_def,EQ_IMP_THM] (* 2 *)
     >- (rw[ultraproduct_model_def,ultraproduct_def] >> rw[partition_def,Uequiv_def,Cart_prod_def,models2worlds_def] >>
        qexists_tac `\i.w` >> rw[] >> simp[EXTENSION] >> metis_tac[])
     >- (fs[ultraproduct_model_def,ultraproduct_def,partition_def,Uequiv_def,Cart_prod_def,models2worlds_def] >>
        `{y |
        (∀i. i ∈ I' ⇒ y i ∈ (MS i).frame.world) ∧ ultrafilter U I' ∧
        (∀i. i ∈ I' ⇒ (MS i).frame.world ≠ ∅) ∧
        (∀i. i ∈ I' ⇒ x i ∈ (MS i).frame.world) ∧
        (∀i. i ∈ I' ⇒ y i ∈ (MS i).frame.world) ∧
        {i | i ∈ I' ∧ x i = y i} ∈ U} <> {}`
            by (`x IN {y |
                         (∀i. i ∈ I' ⇒ y i ∈ (MS i).frame.world) ∧ ultrafilter U I' ∧
                         (∀i. i ∈ I' ⇒ (MS i).frame.world ≠ ∅) ∧
                         (∀i. i ∈ I' ⇒ x i ∈ (MS i).frame.world) ∧
                         (∀i. i ∈ I' ⇒ y i ∈ (MS i).frame.world) ∧
                         {i | i ∈ I' ∧ x i = y i} ∈ U}` suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
		fs[] >> rw[] (* 2 *)
		>- metis_tac[MEMBER_NOT_EMPTY]
		>- metis_tac[ultrafilter_def,proper_filter_def,filter_def]) >>
	`{fw |
        ultrafilter U I' ∧ (∀i. i ∈ I' ⇒ (MS i).frame.world ≠ ∅) ∧
        (∀i. i ∈ I' ⇒ w ∈ (MS i).frame.world) ∧
        (∀i. i ∈ I' ⇒ fw i ∈ (MS i).frame.world) ∧
        {i | i ∈ I' ∧ w = fw i} ∈ U} <> {}` by metis_tac[] >>
	`?fw. fw IN {fw |
                    ultrafilter U I' ∧ (∀i. i ∈ I' ⇒ (MS i).frame.world ≠ ∅) ∧
                    (∀i. i ∈ I' ⇒ w ∈ (MS i).frame.world) ∧
                    (∀i. i ∈ I' ⇒ fw i ∈ (MS i).frame.world) ∧
                    {i | i ∈ I' ∧ w = fw i} ∈ U}` by metis_tac[MEMBER_NOT_EMPTY] >> fs[] >>
	`{i | i ∈ I' ∧ w = fw i} <> {}` by metis_tac[EMPTY_NOTIN_ultrafilter] >>
	`?i. i IN {i | i ∈ I' ∧ w = fw i}` by metis_tac[MEMBER_NOT_EMPTY] >>
	fs[] >> metis_tac[]))
  >- rw[satis_def,EQ_IMP_THM] (* 4 *)
     >- (rw[ultraproduct_model_def,ultraproduct_def] >> rw[partition_def,Uequiv_def,Cart_prod_def,models2worlds_def] >>
        qexists_tac `\i.w` >> rw[] >> simp[EXTENSION] >> metis_tac[])
     >- rw[ultraproduct_model_def] >> simp[PULL_EXISTS] >> rw[ultraproduct_def,partition_def,Cart_prod_def] >>
        simp[PULL_EXISTS] >>
	map_every qexists_tac [`\i.w`,`\i.v`,`\i.v`] >> rw[] (* 6 *)
	>- (`(Uequiv U I' (models2worlds MS)) equiv_on (Cart_prod I' (models2worlds MS))` by metis_tac[prop_A_16] >>
	   fs[equiv_on_def] >>
	   `(λi. w) IN (Cart_prod I' (models2worlds MS))` suffices_by metis_tac[] >>
	   rw[models2worlds_def,Cart_prod_def])
	>- rw[models2worlds_def]
	>- (`(Uequiv U I' (models2worlds MS)) equiv_on (Cart_prod I' (models2worlds MS))` by metis_tac[prop_A_16] >>
	   fs[equiv_on_def] >>
	   `(λi. v) IN (Cart_prod I' (models2worlds MS))` suffices_by metis_tac[] >>
	   rw[models2worlds_def,Cart_prod_def])
	>- (`{i | i ∈ I' ∧ (MS i).frame.rel w v} = I'` suffices_by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >> simp[EXTENSION] >> `I' <> {}` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
	   metis_tac[MEMBER_NOT_EMPTY])
	>- rw[models2worlds_def]
	>- 
	




val prop_2_71 = store_thm(
  "prop_2_71",
  ``!U I MS. (!i. i IN I ==> (MS i) = M) /\ ultrafilter U I ==>
         !phi w. satis M w phi <=> satis (ultraproduct_model U I MS) {fw | Uequiv U I (models2worlds MS) (\i.w) fw} phi``,
  strip_tac >> strip_tac >> strip_tac >> strip_tac >> Induct_on `phi` >> rw[] (* 5 *)
  >- (rw[EQ_IMP_THM,satis_def] (* 4 *)
     >- (rw[ultraproduct_model_def,ultraproduct_def] >> rw[partition_def] >>
        qexists_tac `\i.w` >> rw[] (* 2 *)
	>- (rw[Cart_prod_def] >> rw[models2worlds_def])
	>- (rw[Uequiv_def] >> simp[EXTENSION] >> metis_tac[]))
     >- (rw[ultraproduct_model_def] >> qexists_tac `\i.w` >> rw[] (* 2 *)
        >- (`(Uequiv U I' (models2worlds MS)) equiv_on (Cart_prod I' (models2worlds MS))` by metis_tac[prop_A_16] >>
	   fs[equiv_on_def] >>
	   `(λi. w) IN (Cart_prod I' (models2worlds MS))` suffices_by metis_tac[] >>
	   rw[models2worlds_def,Cart_prod_def])
	>- (`!i. i IN I' ==> w IN ((MS i).valt) a` by rw[] >>
	   `{i | i ∈ I' ∧ w ∈ (MS i).valt a} = I'` by (simp[EXTENSION] >> metis_tac[]) >>
	   fs[ultrafilter_def,proper_filter_def,filter_def]))
     >- (fs[ultraproduct_model_def,models2worlds_def,ultraproduct_def] >> fs[Uequiv_def] >> fs[Cart_prod_def] >>
        `I' <> {}` by fs[ultrafilter_def,proper_filter_def,filter_def] >>
	`?i. i IN I'` by metis_tac[MEMBER_NOT_EMPTY] >>
	metis_tac[])
     >- (fs[ultraproduct_model_def,models2worlds_def,ultraproduct_def] >> fs[Uequiv_def,Cart_prod_def] >>
        `({i | i ∈ I' ∧ w = f i} INTER {i | i ∈ I' ∧ f i ∈ (MS i).valt a}) IN U` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
	`{i | i ∈ I' ∧ w = f i} INTER {i | i ∈ I' ∧ f i ∈ (MS i).valt a} <> {}` by metis_tac[EMPTY_NOTIN_ultrafilter] >>
	`?i. i IN ({i | i ∈ I' ∧ w = f i} INTER {i | i ∈ I' ∧ f i ∈ (MS i).valt a})` by metis_tac[MEMBER_NOT_EMPTY] >>
	fs[] >> metis_tac[]))
  >- rw[satis_def,EQ_IMP_THM]
  >- rw[satis_def,EQ_IMP_THM]
  >- (rw[satis_def,EQ_IMP_THM] (* 2 *)
     >- (rw[ultraproduct_model_def,ultraproduct_def] >> rw[partition_def,Uequiv_def,Cart_prod_def,models2worlds_def] >>
        qexists_tac `\i.w` >> rw[] >> simp[EXTENSION] >> metis_tac[])
     >- (fs[ultraproduct_model_def,ultraproduct_def,partition_def,Uequiv_def,Cart_prod_def,models2worlds_def] >>
        `{y |
        (∀i. i ∈ I' ⇒ y i ∈ (MS i).frame.world) ∧ ultrafilter U I' ∧
        (∀i. i ∈ I' ⇒ (MS i).frame.world ≠ ∅) ∧
        (∀i. i ∈ I' ⇒ x i ∈ (MS i).frame.world) ∧
        (∀i. i ∈ I' ⇒ y i ∈ (MS i).frame.world) ∧
        {i | i ∈ I' ∧ x i = y i} ∈ U} <> {}`
            by (`x IN {y |
                         (∀i. i ∈ I' ⇒ y i ∈ (MS i).frame.world) ∧ ultrafilter U I' ∧
                         (∀i. i ∈ I' ⇒ (MS i).frame.world ≠ ∅) ∧
                         (∀i. i ∈ I' ⇒ x i ∈ (MS i).frame.world) ∧
                         (∀i. i ∈ I' ⇒ y i ∈ (MS i).frame.world) ∧
                         {i | i ∈ I' ∧ x i = y i} ∈ U}` suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
		fs[] >> rw[] (* 2 *)
		>- metis_tac[MEMBER_NOT_EMPTY]
		>- metis_tac[ultrafilter_def,proper_filter_def,filter_def]) >>
	`{fw |
        ultrafilter U I' ∧ (∀i. i ∈ I' ⇒ (MS i).frame.world ≠ ∅) ∧
        (∀i. i ∈ I' ⇒ w ∈ (MS i).frame.world) ∧
        (∀i. i ∈ I' ⇒ fw i ∈ (MS i).frame.world) ∧
        {i | i ∈ I' ∧ w = fw i} ∈ U} <> {}` by metis_tac[] >>
	`?fw. fw IN {fw |
                    ultrafilter U I' ∧ (∀i. i ∈ I' ⇒ (MS i).frame.world ≠ ∅) ∧
                    (∀i. i ∈ I' ⇒ w ∈ (MS i).frame.world) ∧
                    (∀i. i ∈ I' ⇒ fw i ∈ (MS i).frame.world) ∧
                    {i | i ∈ I' ∧ w = fw i} ∈ U}` by metis_tac[MEMBER_NOT_EMPTY] >> fs[] >>
	`{i | i ∈ I' ∧ w = fw i} <> {}` by metis_tac[EMPTY_NOTIN_ultrafilter] >>
	`?i. i IN {i | i ∈ I' ∧ w = fw i}` by metis_tac[MEMBER_NOT_EMPTY] >>
	fs[] >> metis_tac[]))
  >- rw[satis_def,EQ_IMP_THM] (* 4 *)
     >- (rw[ultraproduct_model_def,ultraproduct_def] >> rw[partition_def,Uequiv_def,Cart_prod_def,models2worlds_def] >>
        qexists_tac `\i.w` >> rw[] >> simp[EXTENSION] >> metis_tac[])
     >- (fs[ultraproduct_model_def] >> simp[PULL_EXISTS] >> fs[ultraproduct_def,partition_def,Cart_prod_def] >>
        simp[PULL_EXISTS] >>
	map_every qexists_tac [`\i.w`,`\i.v`,`\i.v`] >> rw[] (* 6 *)
	>- (`(Uequiv U I' (models2worlds MS)) equiv_on (Cart_prod I' (models2worlds MS))` by metis_tac[prop_A_16] >>
	   fs[equiv_on_def] >>
	   `(λi. w) IN (Cart_prod I' (models2worlds MS))` suffices_by metis_tac[] >>
	   rw[models2worlds_def,Cart_prod_def])
	>- rw[models2worlds_def]
	>- (`(Uequiv U I' (models2worlds MS)) equiv_on (Cart_prod I' (models2worlds MS))` by metis_tac[prop_A_16] >>
	   fs[equiv_on_def] >>
	   `(λi. v) IN (Cart_prod I' (models2worlds MS))` suffices_by metis_tac[] >>
	   rw[models2worlds_def,Cart_prod_def])
	>- (`{i | i ∈ I' ∧ (MS i).frame.rel w v} = I'` suffices_by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >> simp[EXTENSION] >> `I' <> {}` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
	   metis_tac[MEMBER_NOT_EMPTY])
	>- rw[models2worlds_def]
	>- (`{y | (∀i. i ∈ I' ⇒ y i ∈ models2worlds MS i) ∧ Uequiv U I' (models2worlds MS) (λi. v) y} =
	   {fw | Uequiv U I' (models2worlds MS) (λi. v) fw}` suffices_by metis_tac[] >>
	   simp[EXTENSION] >>
	   `!x. Uequiv U I' (models2worlds MS) (λi. v) x ==> (∀i. i ∈ I' ⇒ x i ∈ models2worlds MS i)`
	   suffices_by metis_tac[] >>
	   rw[Uequiv_def,models2worlds_def,Cart_prod_def]))
     >- (fs[ultraproduct_model_def,models2worlds_def,ultraproduct_def] >> fs[Uequiv_def,Cart_prod_def] >>
        `I' <> {}` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
	`?i. i IN I'` by metis_tac[MEMBER_NOT_EMPTY] >>
	metis_tac[])
     >- fs[ultraproduct_model_def] >>
        `{i | i ∈ I' ∧ (MS i).frame.rel (f i) (g i)} <> {}` by metis_tac[EMPTY_NOTIN_ultrafilter] >>
	fs[Uequiv_def,ultraproduct_def,Cart_prod_def] >>
	`({i | i ∈ I' ∧ w = f i} INTER {i | i ∈ I' ∧ (MS i).frame.rel (f i) (g i)}) IN U`
	    by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
	`?i. i IN ({i | i ∈ I' ∧ w = f i} INTER {i | i ∈ I' ∧ (MS i).frame.rel (f i) (g i)})`
	    by metis_tac[MEMBER_NOT_EMPTY,EMPTY_NOTIN_ultrafilter] >>
	fs[] >> qexists_tac `g i'` >> rw[] (* 3 *)
	>- metis_tac[]
	>- (fs[partition_def,Uequiv_def] >> fs[Cart_prod_def] >> metis_tac[models2worlds_def])
	>- `v = {fw |
                (∀i''. i'' ∈ I' ⇒ g i' ∈ models2worlds MS i'') ∧
                (∀i. i ∈ I' ⇒ fw i ∈ models2worlds MS i) ∧
                {i | i ∈ I' ∧ g i' = fw i} ∈ U}` suffices_by metis_tac[] >>
           fs[partition_def,Uequiv_def,Cart_prod_def] >>
	   `g IN {y |
                 (∀i. i ∈ I' ⇒ y i ∈ models2worlds MS i) ∧ ultrafilter U I' ∧
                 (∀i. i ∈ I' ⇒ models2worlds MS i ≠ ∅) ∧
                 (∀i. i ∈ I' ⇒ x' i ∈ models2worlds MS i) ∧
                 (∀i. i ∈ I' ⇒ y i ∈ models2worlds MS i) ∧
                 {i | i ∈ I' ∧ x' i = y i} ∈ U}` by metis_tac[] >> fs[] >>
	   rw[EXTENSION,EQ_IMP_THM] (* 3 *)
	   >- metis_tac[models2worlds_def]
	   >- 
	   
	

  


val _ = export_theory();

