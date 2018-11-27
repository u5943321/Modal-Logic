open HolKernel Parse boolLib bossLib;
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




val _ = export_theory();

