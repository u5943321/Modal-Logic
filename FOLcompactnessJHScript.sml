open HolKernel Parse boolLib bossLib;

open combinTheory pred_setTheory relationTheory arithmeticTheory set_relationTheory
     numpairTheory nlistTheory listTheory rich_listTheory


val _ = ParseExtras.tight_equality()

val _ = new_theory "FOLcompactnessJH";


val _ = Datatype`
        fterm = V num
               | Fn num (fterm list) ;
        fform = fFALSE
               | fR num fterm fterm
               | fP num fterm
               | fIMP fform fform
               | fFORALL num fform
               | fEXISTS num fform`


val fNOT_def = Define`
  fNOT ff = fIMP ff fFALSE`

val ELIM_fEXISTS_def = Define`
  ELIM_fEXISTS fFALSE = fFALSE /\
  ELIM_fEXISTS (fR a t1 t2) = fR a t1 t2 /\
  ELIM_fEXISTS (fP a t) = fP a t /\
  ELIM_fEXISTS (fIMP ff1 ff2) = fIMP (ELIM_fEXISTS ff1) (ELIM_fEXISTS ff2) /\
  ELIM_fEXISTS (fFORALL n ff) = fFORALL n (ELIM_fEXISTS ff) /\
  ELIM_fEXISTS (fEXISTS n ff) = fNOT (fFORALL n (fNOT ff))`

val tvars_def = tDefine "tvars" `
  tvars (V a) = {a} /\
  tvars (Fn a ts) = BIGUNION (set (MAP tvars ts))
` (WF_REL_TAC `measure fterm_size` >> rpt gen_tac >> Induct_on `ts` >>
     simp[definition "fterm_size_def"] >> rpt strip_tac >> rw[] >>
     fs[])


val tfns_def = tDefine "tfns" `
  tfns (V a) = {} /\
  (tfns (Fn a ts) = (a, LENGTH ts) INSERT (BIGUNION (set (MAP tfns ts))))
  ` (WF_REL_TAC `measure fterm_size` >> rpt gen_tac >> Induct_on `ts` 
     >- simp[definition "fterm_size_def"]
     >- (simp[definition "fterm_size_def"] >> rw[]
        >- fs[]
        >> first_x_assum drule >> rw[]))

val ffns_def = Define`
  ffns fFALSE = {} /\
  ffns (fR a ft1 ft2) = (tfns ft1) ∪ (tfns ft2) /\ 
  ffns (fP a ft) = tfns ft /\
  ffns (fIMP ff1 ff2) = (ffns ff1) ∪ (ffns ff2) /\
  ffns (fFORALL n ff) = ffns ff /\
  ffns (fEXISTS n ff) = ffns ff`;

val fprs_def = Define`
  fprs fFALSE = {} /\
  fprs (fR a ft1 ft2) = {(a,2)} /\
  fprs (fP a ft) ={(a,1)} /\
  fprs (fIMP ff1 ff2) = (fprs ff1) ∪ (fprs ff2) /\
  fprs (fFORALL n ff) = fprs ff /\
  fprs (fEXISTS n ff) = fprs ff`;

val fns_def = Define`
  fns fms = BIGUNION {ffns f| f IN fms}`;

val prs_def = Define`
  prs fms = BIGUNION {fprs f| f IN fms}`;

val language_def = Define`
  language fms = (fns fms, prs fms)`;

val tfvs_def = tDefine "tfvs" `
  tfvs (V x) = {x} /\
  tfvs (Fn a ts) = BIGUNION (set (MAP tfvs ts))
  ` (WF_REL_TAC `measure fterm_size` >> rpt gen_tac >> Induct_on `ts` 
     >- simp[definition "fterm_size_def"]
     >- (simp[definition "fterm_size_def"] >> rw[]
        >- fs[]
        >> first_x_assum drule >> rw[]))

val ffvs_def = Define`
  ffvs fFALSE = {} /\
  ffvs (fR a ft1 ft2) = (tfvs ft1) ∪ (tfvs ft2) /\
  ffvs (fP a ft) = tfvs ft /\
  ffvs (fIMP ff1 ff2) = (ffvs ff1) ∪ (ffvs ff2) /\
  ffvs (fFORALL n ff) = (ffvs ff) DELETE n /\
  ffvs (fEXISTS n ff) = (ffvs ff) DELETE n`

val tsubst_def = tDefine "tsubst" `
  tsubst v (V x) = v x /\
  tsubst v (Fn a ts) = Fn a (MAP (tsubst v) ts)
  ` (WF_REL_TAC `measure (fterm_size o SND)` >> rpt gen_tac >> Induct_on `ts` 
     >- simp[definition "fterm_size_def"]
     >- (simp[definition "fterm_size_def"] >> rw[]
        >- fs[]
        >> first_x_assum drule >> rw[]))

val VARIANT_def = Define`
  VARIANT vs = (MAX_SET vs) + 1`;


val fsubst_def = Define`
  fsubst v fFALSE = fFALSE /\
  fsubst v (fR a ft1 ft2) = fR a (tsubst v ft1) (tsubst v ft2) /\
  fsubst v (fP a ft) = fP a (tsubst v ft) /\
  fsubst v (fIMP ff1 ff2) = fIMP (fsubst v ff1) (fsubst v ff2) /\
  (fsubst v (fFORALL n ff) = if (?y. y IN (ffvs (fFORALL n ff)) /\ n IN tfvs ((n =+ V n) v y))
                               then (fFORALL (VARIANT (ffvs (fsubst ((n =+ V n) v) ff))) (fsubst ((n =+ V n) v) ff))
                            else (fFORALL n (fsubst ((n =+ V n) v) ff))) /\
  fsubst v (fEXISTS n ff) = if (?y. y IN (ffvs (fEXISTS n ff)) /\ n IN tfvs ((n =+ V n) v y))
                               then (fEXISTS (VARIANT (ffvs (fsubst ((n =+ V n) v) ff))) (fsubst ((n =+ V n) v) ff))
                            else (fEXISTS n (fsubst ((n =+ V n) v) ff))`

val qfree_def = Define`
  (qfree fFALSE = T) /\
  (qfree (fR a t1 t2) = T) /\
  (qfree (fP a t) = T) /\
  (qfree (fIMP ff1 ff2) = (qfree ff1 /\ qfree ff2)) /\
  (qfree (fFORALL n ff) = F) /\
  qfree (fEXISTS n ff) = F `;
val _ = export_rewrites ["qfree_def"]

val (prenex_rules, prenex_ind, prenex_cases) = Hol_reln`
  (!ff. qfree ff ==> prenex ff) /\
  (!ff n. prenex ff ==> prenex (fEXISTS n ff)) /\
  (!ff n. prenex ff ==> prenex (fFORALL n ff))`

val (universal_rules, universal_ind, universal_cases) = Hol_reln`
  (!ff. qfree ff ==> universal ff) /\
  (!ff n. prenex ff ==> universal (fFORALL n ff))`


val size_def = Define`
  size fFALSE = 1n /\
  size (fR a t1 t2) = 1 /\
  size (fP a f) = 1 /\
  (size (fIMP ff1 ff2) = size ff1 + size ff2) /\
  size (fFORALL n ff) = size ff + 1 /\
  size (fEXISTS n ff) = size ff + 3`


  
val size_fsubst = store_thm(
  "size_fsubst",
  ``!p i. size p = size (fsubst i p)``,
   Induct_on `p` >> rw[] (* 6 *)
   >- rw[fsubst_def]
   >- (rw[fsubst_def] >> Cases_on `f` >> Cases_on `f0` >> fs[tsubst_def,size_def]) (* 4 *)
   >- (rw[fsubst_def] >> Cases_on `f` >> fs[tsubst_def,size_def])
   >- (rw[fsubst_def] >> fs[tsubst_def,size_def] >> metis_tac[])
   >- (rw[fsubst_def] >> fs[tsubst_def,size_def])
   >- (rw[fsubst_def] >> fs[tsubst_def,size_def]));



val Prenex_right_def = tDefine "Prenex_right" `
Prenex_right p fFALSE = fIMP p fFALSE /\
Prenex_right p (fR a t1 t2) = fIMP p (fR a t1 t2) /\
Prenex_right p (fP a t) = fIMP p (fP a t) /\
Prenex_right p (fIMP ff1 ff2) = fIMP p (fIMP ff1 ff2) /\
(Prenex_right p (fFORALL n ff) = let y = VARIANT ((ffvs (fFORALL n ff) ∪ (ffvs p))) in
                                    fFORALL y (Prenex_right p (fsubst ((n =+ V y) V) ff))) /\
Prenex_right p (fEXISTS n ff) = let y = VARIANT ((ffvs (fEXISTS n ff) ∪ (ffvs p))) in
                                    fEXISTS y (Prenex_right p (fsubst ((n =+ V y) V) ff))`
 (WF_REL_TAC `measure (size o SND)` >> rw[] (* 2 *)
     >- (`size (fsubst V⦇n ↦ V (VARIANT (ffvs (fEXISTS n ff) ∪ ffvs p))⦈ ff) = size ff`
          by metis_tac[size_fsubst] >> rw[size_def] >> fs[])
     >- (`size (fsubst V⦇n ↦ V (VARIANT (ffvs (fFORALL n ff) ∪ ffvs p))⦈ ff) = size ff`
          by metis_tac[size_fsubst] >> rw[size_def] >> fs[]))




val Prenex_left_def = tDefine "Prenex_left" `
Prenex_left fFALSE p = Prenex_right fFALSE p /\
Prenex_left (fR a t1 t2) p = Prenex_right (fR a t1 t2) p /\
Prenex_left (fP a t) p = Prenex_right (fP a t) p /\
Prenex_left (fIMP ff1 ff2) p = Prenex_right (fIMP ff1 ff2) p /\
(Prenex_left (fFORALL n q) p = let y = VARIANT ((ffvs (fFORALL n q) ∪ (ffvs p))) in
                                  fEXISTS y (Prenex_left (fsubst ((n =+ V y) V) q) p)) /\
Prenex_left (fEXISTS n q) p = let y = VARIANT ((ffvs (fEXISTS n q) ∪ (ffvs p))) in
                                  fFORALL y (Prenex_left (fsubst ((n =+ V y) V) q) p)`
(WF_REL_TAC `measure (size o FST)` >> rw[] (* 2 *)
     >- (`size (fsubst V⦇n ↦ V (VARIANT (ffvs (fEXISTS n q) ∪ ffvs p))⦈ q) = size q`
          by metis_tac[size_fsubst] >> rw[size_def] >> fs[])
     >- (`size (fsubst V⦇n ↦ V (VARIANT (ffvs (fFORALL n q) ∪ ffvs p))⦈ q) = size q`
          by metis_tac[size_fsubst] >> rw[size_def] >> fs[]))

Theorem prenex_rwts[simp]:
  (prenex fFALSE <=> T) /\
  (prenex (fIMP f1 f2) <=> qfree f1 /\ qfree f2) /\
  (prenex (fR a t1 t2) <=> T) /\
  (prenex (fP a t) <=> T) /\
  (prenex (fEXISTS n f) <=> prenex f) /\
  (prenex (fFORALL n f) <=> prenex f)
Proof
  rpt conj_tac >> simp[Once prenex_cases, SimpLHS]
QED
                        
Theorem qfree_fsubst[simp]:
  !f s. qfree (fsubst s f) <=> qfree f
Proof
  Induct_on `f` >> rw[fsubst_def]
QED

Theorem prenex_fsubst[simp]:
  !f s. prenex (fsubst s f) <=> prenex f
Proof
  Induct_on `f` >> rw[fsubst_def]
QED
         
Theorem tsubst_composition : 
  (∀t s1 s2. tsubst s1 (tsubst s2 t) = tsubst (tsubst s1 o s2) t) ∧
  (∀tl s1 s2. MAP (\a. tsubst s1 (tsubst s2 a)) tl = MAP (tsubst (tsubst s1 o s2)) tl)
Proof
  ho_match_mp_tac (TypeBase.induction_of ``:fterm``) >> 
  simp[tsubst_def, listTheory.MAP_MAP_o] >>
  simp_tac (bool_ss ++ boolSimps.ETA_ss) [] >> 
  rpt strip_tac >> pop_assum (fn th => simp[GSYM th]) >> 
  simp[combinTheory.o_DEF]
QED


Theorem Prenex_right_subst:
  !f1 f2 s. qfree f1 /\ prenex f2 ==> prenex (Prenex_right f1 f2)
Proof                                          
  completeInduct_on `size f2` >> fs[PULL_FORALL] >> Cases >> 
  rw[size_def, fsubst_def, Prenex_right_def] 
  >> (first_x_assum irule >> simp[prenex_fsubst, GSYM size_fsubst])
QED
     
val prenex_Prenex_left = store_thm(
  "prenex_Prenex_left",                                                        
  ``!f1 f2. prenex f1 /\ prenex f2 ==> prenex (Prenex_left f1 f2)``,
  completeInduct_on `size f1` >> fs[PULL_FORALL] >> Cases >> 
  rw[fsubst_def, Prenex_left_def, Prenex_right_subst] (* 2 *) >>
  first_x_assum irule >> simp[size_def, GSYM size_fsubst]);



        
val Prenex_def = Define`
  Prenex fFALSE = fFALSE /\
  Prenex (fR a t1 t2) = fR a t1 t2 /\
  Prenex (fP a t) = fP a t /\
  Prenex (fIMP ff1 ff2) = Prenex_left (Prenex ff1) (Prenex ff2) /\
  Prenex (fFORALL n p) = fFORALL n (Prenex p) /\
  Prenex (fEXISTS n p) = fEXISTS n (Prenex p)`;




                                
val prenex_Prenex = store_thm(
        "prenex_Prenex",
``!ff. prenex (Prenex ff)``,
Induct_on `ff` (* 6 *)
>- (rw[Prenex_def] >> `qfree fFALSE` by fs[qfree_def] >> metis_tac[prenex_rules])
>- (rw[Prenex_def] >> `qfree (fR n f f0)` by fs[qfree_def] >> metis_tac[prenex_rules])
>- (rw[Prenex_def] >> `qfree (fP n f)` by fs[qfree_def] >> metis_tac[prenex_rules])
>- rw[Prenex_def,prenex_Prenex_left]
>- (rw[Prenex_def] >> metis_tac[prenex_rules])
>- (rw[Prenex_def] >> metis_tac[prenex_rules]));


val specialize_def = Define`
(specialize fFALSE = fFALSE) /\
(specialize (fR a t1 t2) = fR a t1 t2) /\
(specialize (fP a t) = fP a t) /\
(specialize (fIMP f1 f2) = fIMP f1 f2) /\
(specialize (fFORALL n f) = specialize f) /\
(specialize (fEXISTS n ff) = fIMP (fFORALL n (fIMP ff fFALSE)) fFALSE)`;

val bumpterm_def = tDefine "bumpterm" `
bumpterm (V x) = V x /\
bumpterm (Fn k l) = Fn (npair 0 k) (MAP bumpterm l)`
(WF_REL_TAC `measure fterm_size` >> rpt gen_tac >> Induct_on `l` >>
     simp[definition "fterm_size_def"] >> rpt strip_tac >> rw[] >>
     fs[])

val bumpform_def = Define`
bumpform fFALSE = fFALSE /\
bumpform (fR a t1 t2) = fR a (bumpterm t1) (bumpterm t2) /\
bumpform (fP a t) = fP a (bumpterm t) /\
bumpform (fIMP f1 f2) = fIMP (bumpform f1) (bumpform f2) /\
bumpform (fFORALL a ff) = fFORALL a (bumpform ff) /\
bumpform (fFORALL a ff) = fEXISTS a (bumpform ff)`;

val num_of_term_def = tDefine "num_of_term" `
  num_of_term (V n) = 2 * n /\
  num_of_term (Fn f ts) = 2 * (npair f (nlist_of (MAP num_of_term ts))) + 1`
  (WF_REL_TAC `measure fterm_size` >> rpt gen_tac >> Induct_on `ts` 
     >- simp[definition "fterm_size_def"]
     >- (simp[definition "fterm_size_def"] >> rw[]
        >- fs[]
        >> first_x_assum drule >> rw[]))

val num_of_form_def = Define`
  num_of_form fFALSE = 0 /\
  num_of_form (fP a t) = (npair a (num_of_term t)) * 5 + 1 /\
  num_of_form (fR a t1 t2) = (npair a (npair (num_of_term t1) (num_of_term t2))) * 5 + 2 /\
  num_of_form (fIMP ff1 ff2) = npair (num_of_form ff1) (num_of_form ff2) * 5 + 3 /\
  num_of_form (fFORALL n ff) = npair n (num_of_form ff) * 5 + 4 /\
  num_of_form (fEXISTS n ff) = npair n (num_of_form ff) * 5 + 5`;



val term_of_num_def = tDefine "term_of_num" `
term_of_num n = if (n MOD 2 = 0) then (V (n DIV 2)) else
                   Fn (nfst ((n - 1) DIV 2)) (MAP term_of_num (listOfN (nsnd ((n - 1) DIV 2))))`
(WF_REL_TAC `$<` >> rw[] >>
 `a < (nsnd ((n − 1) DIV 2))` by fs[MEM_listOfN_LESS] >>
 `(nsnd ((n − 1) DIV 2)) < n` suffices_by simp[] >>
 `(nsnd ((n − 1) DIV 2)) <= ((n − 1) DIV 2)` by fs[nsnd_le] >>
 `(n − 1) DIV 2 < n` suffices_by simp[] >>
 `0 < 2` by simp[] >>
 `(n - 1) DIV 2 <= n - 1` by simp[DIV_LESS_EQ] >> fs[])
 

Theorem num_of_form_0 :
  num_of_form ff = 0 ==> ff = fFALSE
Proof
  rw[] >> SPOSE_NOT_THEN ASSUME_TAC >> Cases_on `ff` >> fs[num_of_form_def]
QED



val form_of_num_def = tDefine "form_of_num" `
  form_of_num n = case (n MOD 5) of
                  | 0 => if n = 0 then fFALSE else
                    fEXISTS (nfst ((n - 5) DIV 5)) (form_of_num (nsnd ((n - 5) DIV 5)))
                  | 1 => fP (nfst ((n - 1) DIV 5)) (term_of_num (nsnd ((n - 1) DIV 5)))
                  | 2 => fR (nfst ((n - 2) DIV 5)) (term_of_num (nfst (nsnd ((n - 2) DIV 5)))) (term_of_num (nsnd (nsnd ((n - 2) DIV 5))))
                  | 3 => fIMP (form_of_num (nfst ((n - 3) DIV 5)))
                              (form_of_num (nsnd ((n - 3) DIV 5)))
                  | 4 => fFORALL (nfst ((n - 4) DIV 5)) (form_of_num (nsnd ((n - 4) DIV 5)))`
(WF_REL_TAC `$<` >> rw[] (* 4 *)
>- (`nsnd ((n − 4) DIV 5) <= (n − 4) DIV 5` by rw[nsnd_le] >>
   `(n − 4) DIV 5 < n` suffices_by fs[] >>
   Cases_on `n - 4 = 0`
   >- (`n = 4` by fs[] >> simp[])
   >- (`n - 4 > 0` by simp[] >>
      `(n - 4) DIV 5 < n - 4` by simp[DIV_LESS] >> fs[]))
>- (`nfst ((n − 3) DIV 5) <= (n − 3) DIV 5` by rw[nfst_le] >>
   `(n − 3) DIV 5 < n` suffices_by fs[] >>
   Cases_on `n - 3 = 0`
   >- (`n = 3` by fs[] >> simp[])
   >- (`n - 3 > 0` by simp[] >>
      `(n - 3) DIV 5 < n - 3` by simp[DIV_LESS] >> fs[]))
>- (`nsnd ((n − 3) DIV 5) <= (n − 3) DIV 5` by rw[nsnd_le] >>
   `(n − 3) DIV 5 < n` suffices_by fs[] >>
   Cases_on `n - 3 = 0`
   >- (`n = 3` by fs[] >> simp[])
   >- (`n - 3 > 0` by simp[] >>
      `(n - 3) DIV 5 < n - 3` by simp[DIV_LESS] >> fs[]))
>- (`nsnd ((n − 5) DIV 5) <= (n − 5) DIV 5` by rw[nsnd_le] >>
   `(n − 5) DIV 5 < n` suffices_by fs[] >>
   Cases_on `n - 5 = 0`
   >- (Cases_on `n = 0`
      >- fs[]
      >- (`n > 0` by fs[] >> `(n − 5) DIV 5 = 0` by simp[] >> fs[]))
   >- (`n - 5 > 0` by simp[] >>
      `(n - 5) DIV 5 < n - 5` by simp[DIV_LESS] >> fs[])))


Theorem LE_LESS :
!m n. m <= n <=> m < n + 1
Proof
rw[]
QED




Theorem MEM_LESS_num_of_term :
∀l. MEM m l ⇒ num_of_term m < num_of_term (Fn n l)
Proof
Induct_on `l` >> rw[]
>- (rw[num_of_term_def] >> rw[ncons_def] >>
   `num_of_term h = nfst (num_of_term h ⊗ nlist_of (MAP (λa. num_of_term a) l))`
     by simp[GSYM nfst_npair] >>
   `nfst (num_of_term h ⊗ nlist_of (MAP (λa. num_of_term a) l)) <= (num_of_term h ⊗ nlist_of (MAP (λa. num_of_term a) l))`
     by simp[nfst_le] >>
  `num_of_term h <=
   2 * n ⊗ (num_of_term h ⊗ nlist_of (MAP (λa. num_of_term a) l) + 1)` suffices_by simp[] >>
  `num_of_term h <=
   n ⊗ (num_of_term h ⊗ nlist_of (MAP (λa. num_of_term a) l) + 1)` suffices_by simp[] >>
  `(num_of_term h ⊗ nlist_of (MAP (λa. num_of_term a) l) + 1) <=
  n ⊗ (num_of_term h ⊗ nlist_of (MAP (λa. num_of_term a) l) + 1)` by simp[nsnd_le] >>
  `num_of_term h <=
   (num_of_term h ⊗ nlist_of (MAP (λa. num_of_term a) l) + 1)` suffices_by simp[] >>
  `num_of_term h <= num_of_term h ⊗ nlist_of (MAP (λa. num_of_term a) l)`
    suffices_by simp[] >>
  simp[nfst_le])
>- (first_x_assum drule >> rw[] >>
   `num_of_term (Fn n l) <= num_of_term (Fn n (h :: l))` suffices_by fs[] >>
   rw[num_of_term_def] >>
   `n ⊗ nlist_of (MAP (λa. num_of_term a) l) <
   n ⊗ ncons (num_of_term h) (nlist_of (MAP (λa. num_of_term a) l))` suffices_by simp[] >>
   `nlist_of (MAP (λa. num_of_term a) l) <
   ncons (num_of_term h) (nlist_of (MAP (λa. num_of_term a) l))` suffices_by simp[le_npair] >>
   rw[ncons_def] >>
   `num_of_term h ⊗ nlist_of (MAP (λa. num_of_term a) l) <
   (num_of_term h ⊗ nlist_of (MAP (λa. num_of_term a) l)) + 1` by fs[] >>
   rw[GSYM LE_LESS])
QED


Theorem term_num_term :
!n t. num_of_term t = n ==> (term_of_num (num_of_term t)) = t
Proof
completeInduct_on `n` >> rw[] >> Cases_on `t`
>- (rw[num_of_term_def,Once term_of_num_def] >>
   `2 * n = n * 2` by simp[] >>
   `2 * n DIV 2 = n * 2 DIV 2` by metis_tac[] >>
   `0 < 2` by fs[] >> metis_tac[MULT_DIV])
>- (rw[num_of_term_def,Once term_of_num_def]
   >- (`2 * n ⊗ nlist_of (MAP (λa. num_of_term a) l) =
      n ⊗ nlist_of (MAP (λa. num_of_term a) l) * 2` by simp[] >>
      `(2 * n ⊗ nlist_of (MAP (λa. num_of_term a) l) DIV 2) =
      ((n ⊗ nlist_of (MAP (λa. num_of_term a) l) * 2) DIV 2)` by metis_tac[] >>
      `_ = n ⊗ nlist_of (MAP (λa. num_of_term a) l)` by fs[MULT_DIV] >>
      `nfst (n ⊗ nlist_of (MAP (λa. num_of_term a) l)) = n` by fs[nfst_npair] >>
      metis_tac[])
   >- (`2 * n ⊗ nlist_of (MAP (λa. num_of_term a) l) =
      n ⊗ nlist_of (MAP (λa. num_of_term a) l) * 2` by simp[] >>
      `(2 * n ⊗ nlist_of (MAP (λa. num_of_term a) l) DIV 2) =
      ((n ⊗ nlist_of (MAP (λa. num_of_term a) l) * 2) DIV 2)` by metis_tac[] >>
      `_ = n ⊗ nlist_of (MAP (λa. num_of_term a) l)` by fs[MULT_DIV] >>
      `nsnd (n ⊗ nlist_of (MAP (λa. num_of_term a) l)) = nlist_of (MAP (λa. num_of_term a) l)` by fs[nsnd_npair] >>
      fs[] >> simp[listOfN_nlist] >>
      `MAP (λa. term_of_num a) (MAP (λa. num_of_term a) l) =
      MAP ((λa. term_of_num a) o (λa. num_of_term a)) l` by simp[MAP_MAP_o] >>
      `MAP ((λa. term_of_num a) ∘ (λa. num_of_term a)) l = l` suffices_by fs[] >>
      rw[LIST_EQ_REWRITE] >> 
      `EL x (MAP ((λa. term_of_num a) ∘ (λa. num_of_term a)) l) =
      ((λa. term_of_num a) ∘ (λa. num_of_term a)) (EL x l)` by fs[EL_MAP] >>
      `((λa. term_of_num a) ∘ (λa. num_of_term a)) (EL x l) = EL x l` suffices_by fs[] >>
      rw[] >>
      `(num_of_term (EL x l)) < num_of_term (Fn n l)`
        suffices_by rw[] >>
      `!m. MEM m l ==> num_of_term m < num_of_term (Fn n l)`
        suffices_by (rw[] >>
                    `MEM (EL x l) l`
                      by (`∃n. n < LENGTH l ∧ (EL x l) = EL n l`
                            suffices_by metis_tac[MEM_EL] >>
                         qexists_tac `x` >> fs[]) >>
                    metis_tac[]) >>
      metis_tac[MEM_LESS_num_of_term]))
QED

val MULT_DIV' = ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV

Theorem term_num_term'[simp] = SIMP_RULE (srw_ss ()) [] term_num_term
Theorem LENGTH_listOfN_nlen' = GSYM LENGTH_listOfN_nlen

Theorem divmod2_inverts[simp]:
  !n k. n MOD 2 = k ==> 2 * ((n - k) DIV 2) + k = n
Proof
      rw[] >> qabbrev_tac `q = n DIV 2` >> qabbrev_tac `r = n MOD 2` >>
      mp_tac (DIVISION |> Q.SPEC `2`) >> impl_tac >- simp[] >>
      disch_then (qspec_then `n` mp_tac) >> simp[] >>
      markerLib.RM_ALL_ABBREVS_TAC >> rw[MULT_DIV']
QED

Theorem num_term_num[simp]:
  !n. num_of_term (term_of_num n) = n
Proof
  completeInduct_on `n` >> rw[num_of_term_def,Once term_of_num_def,MULT_DIV']
  >- (`2 * ((n - 0) DIV 2) + 0 = n` by metis_tac[divmod2_inverts] >> fs[])
  >- (simp[MAP_MAP_o] >>
     `nlist_of
     (MAP ((λa. num_of_term a) ∘ (λa. term_of_num a))
        (listOfN (nsnd ((n − 1) DIV 2)))) =
     nsnd ((n − 1) DIV 2) /\ 2 * ((n - 1) DIV 2) + 1 = n` suffices_by simp[] >>
     rw[] (* 2 *)
     >- (`(!l. l < n ==>
        nlist_of (MAP ((λa. num_of_term a) ∘ (λa. term_of_num a)) (listOfN l)) = l) /\
        (nsnd ((n − 1) DIV 2)) < n` suffices_by metis_tac[] >> rw[] (* 2 *)
        >- (irule nel_eq_nlist >> rw[] (* 2 *)
           >- (`!m l. m < nlen l ==> nel m l = EL m (listOfN l)` by simp[nel_EL] >>
              `m < LENGTH (MAP ((λa. num_of_term a) ∘ (λa. term_of_num a)) (listOfN l))`
                by metis_tac[listOfN_nlist,LENGTH_listOfN_nlen] >>
              `m < LENGTH (listOfN l)` by metis_tac[LENGTH_MAP] >>
              `nlen l = LENGTH (listOfN l)` by fs[Once LENGTH_listOfN_nlen'] >>
              `nlen
     (nlist_of (MAP ((λa. num_of_term a) ∘ (λa. term_of_num a)) (listOfN l))) =
              LENGTH (listOfN (nlist_of (MAP ((λa. num_of_term a) ∘ (λa. term_of_num a)) (listOfN l))))` by fs[Once LENGTH_listOfN_nlen] >>
              `EL m (listOfN (nlist_of (MAP ((λa. num_of_term a) ∘ (λa. term_of_num a)) (listOfN l)))) = EL m (listOfN l)` suffices_by metis_tac[] >>
              `EL m (MAP ((λa. num_of_term a) ∘ (λa. term_of_num a)) (listOfN l)) =
              EL m (listOfN l)` suffices_by metis_tac[listOfN_nlist] >>
              `MEM (EL m (MAP ((λa. num_of_term a) ∘ (λa. term_of_num a)) (listOfN l)))
              (MAP ((λa. num_of_term a) ∘ (λa. term_of_num a)) (listOfN l))`
                by metis_tac[EL_MEM] >>
              `MEM (EL m (listOfN l)) (listOfN l)`
                by metis_tac[LENGTH_MAP,EL_MEM] >>
              `!e l. MEM e (listOfN l) ==> e < l` by metis_tac[MEM_listOfN_LESS] >>
              `EL m (MAP ((λa. num_of_term a) ∘ (λa. term_of_num a)) (listOfN l)) =
              ((λa. num_of_term a) ∘ (λa. term_of_num a)) (EL m (listOfN l))`
                by metis_tac[EL_MAP] >>
              `((λa. num_of_term a) ∘ (λa. term_of_num a)) (EL m (listOfN l)) =
              EL m (listOfN l)` suffices_by metis_tac[] >> rw[] >>
              first_x_assum irule >>
              `EL m (listOfN l) < l` suffices_by metis_tac[LESS_TRANS] >>
              metis_tac[])
           >- (`nlen l = LENGTH (listOfN l)` by fs[Once LENGTH_listOfN_nlen'] >>
              `nlen
     (nlist_of (MAP ((λa. num_of_term a) ∘ (λa. term_of_num a)) (listOfN l))) =
              LENGTH (listOfN (nlist_of (MAP ((λa. num_of_term a) ∘ (λa. term_of_num a)) (listOfN l))))` by fs[Once LENGTH_listOfN_nlen] >>
              `LENGTH (listOfN l) =
              LENGTH
              (listOfN
                (nlist_of
                 (MAP ((λa. num_of_term a) ∘ (λa. term_of_num a)) (listOfN l))))`
              suffices_by metis_tac[] >>
              `(listOfN (nlist_of
              (MAP ((λa. num_of_term a) ∘ (λa. term_of_num a)) (listOfN l)))) =
              (MAP ((λa. num_of_term a) ∘ (λa. term_of_num a)) (listOfN l))`
                by simp[Once listOfN_nlist] >>
              `LENGTH (listOfN l) = 
              LENGTH (MAP ((λa. num_of_term a) ∘ (λa. term_of_num a)) (listOfN l))`
                suffices_by metis_tac[] >>
              simp[GSYM LENGTH_MAP]))
        >- (irule LESS_EQ_LESS_TRANS >> qexists_tac `(n - 1) DIV 2` >> simp[nsnd_le] >>
           irule LESS_EQ_LESS_TRANS >> qexists_tac `n - 1` >> rw[DIV_LE_X] >>
           SPOSE_NOT_THEN ASSUME_TAC >> `n = 0` by fs[] >> fs[]))
     >- (`n MOD 2 = 1` by (SPOSE_NOT_THEN ASSUME_TAC >> `n MOD 2 >= 2` by fs[] >>
        `0 < 2` by fs[] >> `n MOD 2 < 2` by fs[MOD_LESS] >>
        `2 <= n MOD 2` by fs[] >>
        `¬(n MOD 2 < 2)` by metis_tac[GSYM NOT_LESS]) >> metis_tac[divmod2_inverts]))   
QED



Theorem form_num_form[simp] :
  !f. (form_of_num (num_of_form f)) = f
Proof
Induct_on `f` >> rw[num_of_form_def,Once form_of_num_def,MULT_DIV']
QED

Theorem divmod5_inverts[simp]:
  n MOD 5 = k ==> 5 * ((n - k) DIV 5) + k = n
Proof
  qabbrev_tac `q = n DIV 5` >> qabbrev_tac `r = n MOD 5` >>
      mp_tac (DIVISION |> Q.SPEC `5`) >> impl_tac >- simp[] >>
      disch_then (qspec_then `n` mp_tac) >> simp[] >>
      markerLib.RM_ALL_ABBREVS_TAC >> rw[MULT_DIV']
QED

Theorem num_form_num[simp] :
  !n. num_of_form (form_of_num n) = n
Proof
  completeInduct_on `n` >> simp[Once form_of_num_def] >> rw[num_of_form_def]
  >- (`nsnd ((n - 5) DIV 5) < n ∧ 5 * ((n -5) DIV 5) = n - 5 ∧ 5 <= n` suffices_by simp[] >>
     rw[] (* 3 *)
     >- (irule LESS_EQ_LESS_TRANS >> qexists_tac `(n - 5) DIV 5` >> simp[nsnd_le] >>
        irule LESS_EQ_LESS_TRANS >> qexists_tac `n - 5` >> rw[DIV_LE_X])
     >- (qabbrev_tac `q = n DIV 5` >> qabbrev_tac `r = n MOD 5` >>
         mp_tac (DIVISION |> Q.SPEC `5`) >> impl_tac >- simp[] >>
         disch_then (qspec_then `n` mp_tac) >> simp[] >>
         markerLib.RM_ALL_ABBREVS_TAC >> rw[] >> `5 <= 5 * q` by simp[] >>
         `5 * q - 5 = 5 * (q - 1)` by simp[LEFT_SUB_DISTRIB] >> simp[MULT_DIV'])
     >- (spose_not_then strip_assume_tac >> `n < 5` by simp[] >>
         `n MOD 5 = n` by simp[] >> fs[]))
  >- (`nfst ((n - 3) DIV 5) < n /\ nsnd ((n - 3) DIV 5) < n` suffices_by simp[] >> rw[]
     >- (irule LESS_EQ_LESS_TRANS >> qexists_tac `(n - 3) DIV 5` >> simp[nfst_le] >>
        irule LESS_EQ_LESS_TRANS >> qexists_tac `n - 3` >> rw[DIV_LE_X] >>
        SPOSE_NOT_THEN ASSUME_TAC >> `n = 0` by fs[] >> fs[])
     >- (irule LESS_EQ_LESS_TRANS >> qexists_tac `(n - 3) DIV 5` >> simp[nsnd_le] >>
        irule LESS_EQ_LESS_TRANS >> qexists_tac `n - 3` >> rw[DIV_LE_X] >>
        SPOSE_NOT_THEN ASSUME_TAC >> `n = 0` by fs[] >> fs[]))
  >- (`nfst ((n - 4) DIV 5) < n /\ nsnd ((n - 4) DIV 5) < n` suffices_by simp[] >> rw[]
     >- (irule LESS_EQ_LESS_TRANS >> qexists_tac `(n - 4) DIV 5` >> simp[nfst_le] >>
        irule LESS_EQ_LESS_TRANS >> qexists_tac `n - 4` >> rw[DIV_LE_X] >>
        SPOSE_NOT_THEN ASSUME_TAC >> `n = 0` by fs[] >> fs[])
     >- (irule LESS_EQ_LESS_TRANS >> qexists_tac `(n - 4) DIV 5` >> simp[nsnd_le] >>
        irule LESS_EQ_LESS_TRANS >> qexists_tac `n - 4` >> rw[DIV_LE_X] >>
        SPOSE_NOT_THEN ASSUME_TAC >> `n = 0` by fs[] >> fs[]))
  >- (`n MOD 5 < 5` by simp[] >> qabbrev_tac `r = n MOD 5` >> fs[])
QED


Theorem Godel_num_of_form :
  BIJ num_of_form (univ (:fform)) univ (:num)
Proof
  rw[BIJ_DEF] >> simp[EQ_IMP_THM,INJ_DEF,SURJ_DEF] (* 2 *)
  >- metis_tac[form_num_form]
  >- (rw[] >> qexists_tac `form_of_num x` >> rw[num_form_num])
QED


val SKOLEM_def = tDefine "SKOLEM"`
 (SKOLEM k (fEXISTS m f0) =
   SKOLEM (k + 1)
          (fsubst V⦇m ↦ Fn (npair (npair m (num_of_form f0)) k)
                                (MAP V (SET_TO_LIST (ffvs (fEXISTS m f0))))⦈
                  f0)
 ) /\
 (SKOLEM k (fFORALL m f0) = fFORALL m (SKOLEM k f0)) /\
 SKOLEM k ff = ff`
(WF_REL_TAC `measure (size o SND)` >> simp[GSYM size_fsubst,size_def]);

val SKOLEM_ind = DB.fetch "-" "SKOLEM_ind"

Theorem BIGUNION_set_MAP :
  BIGUNION (set (MAP f l)) = BIGUNION (IMAGE f (set l))
Proof
  Induct_on `l` >> simp[]
QED

Theorem fterm_size_def[simp] = DB.fetch "-" "fterm_size_def"

val tsize_lemma = Q.prove(
  `MEM t tlist ==> fterm_size t < fterm1_size tlist`,
  Induct_on `tlist` >> fs[] >> rw[] >> fs[]);

Theorem tfvs_tsubst :
  !v t. tfvs (tsubst v t) = BIGUNION (IMAGE (tfvs o v) (tfvs t))
Proof
  completeInduct_on `fterm_size t` >> Cases_on `t`
  >> rw[tfvs_def,tsubst_def,MAP_MAP_o,BIGUNION_set_MAP,combinTheory.o_ABS_R] >>
  rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] >> fs[MEM_MAP] >> rw[] >>
  rename [`MEM t tlist`] >>
  first_x_assum (qspec_then `fterm_size t` mp_tac) >> drule_then assume_tac tsize_lemma >>
  simp[] >> strip_tac >> simp[PULL_EXISTS]
  >- (fs[] >> metis_tac[]) >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED


Theorem tfvs_FINITE :
!t. FINITE (tfvs t)
Proof
  completeInduct_on `fterm_size t` >> Cases_on `t` >>
  rw[tfvs_def,MAP_MAP_o,BIGUNION_set_MAP,combinTheory.o_ABS_R] >>
  rw[tfvs_def] >> fs[MEM_MAP] >>
  first_x_assum (qspec_then `fterm_size a'` mp_tac) >> drule_then assume_tac tsize_lemma >>
  simp[]
QED

Theorem ffvs_FINITE :
!f. FINITE (ffvs f)
Proof
  Induct_on `f` >> rw[ffvs_def] >> metis_tac[tfvs_FINITE]
QED


Theorem ffvs_fsubst:
  !v ff. ffvs (fsubst v ff) = BIGUNION (IMAGE (tfvs o v) (ffvs ff))
Proof
  Induct_on `ff` >> rw[ffvs_def,fsubst_def,tfvs_tsubst]
  >- (rw[EQ_IMP_THM, Once EXTENSION, PULL_EXISTS] >>
      rename [`y ∈ ffvs ff`, `a ∈ ffvs ff`, `x ∈ tfvs (v (|n |-> V n|) a)`]
      >- (Cases_on `a = n`
          >- (fs[APPLY_UPDATE_THM, tfvs_def] >> rw[] >> rfs[] >> metis_tac[]) >>
          fs[APPLY_UPDATE_THM, tfvs_def] >> rfs[] >> metis_tac[]) >>
      rfs[APPLY_UPDATE_THM] >> qexists_tac `y` >> simp[] >>
      simp[VARIANT_def] >>
      qmatch_abbrev_tac `x <> MAX_SET myset + 1` >>
      `FINITE myset` by
        (rw[Abbr`myset`]
	>- (irule IMAGE_FINITE >> metis_tac[ffvs_FINITE])
	>- metis_tac[tfvs_FINITE]) >>
      `x IN myset` suffices_by (
        strip_tac >> drule_all in_max_set >> simp[]
      ) >>
      simp[Abbr`myset`,PULL_EXISTS] >> qexists_tac `y` >>
      simp[APPLY_UPDATE_THM])
  >- (rw[EQ_IMP_THM, Once EXTENSION, PULL_EXISTS] 
     >- (rename [`a ∈ ffvs ff`, `x ∈ tfvs (v (|n |-> V n|) a)`] >>
         Cases_on `a = n`
         >- (fs[APPLY_UPDATE_THM, tfvs_def] >> rw[] >> rfs[] >> metis_tac[]) >>
	fs[APPLY_UPDATE_THM, tfvs_def] >> rfs[] >> metis_tac[])
     >- (rename [`a ∈ ffvs ff`, `x ∈ tfvs (v a)`,`a <> n`] >>
        rfs[APPLY_UPDATE_THM] >> qexists_tac `a` >> simp[] >> metis_tac[]))
  >- (rw[EQ_IMP_THM, Once EXTENSION, PULL_EXISTS]
     >- (rename [`a ∈ ffvs ff`, `x ∈ tfvs (v (|n |-> V n|) a)`] >>
        Cases_on `a = n`
	>- (fs[APPLY_UPDATE_THM, tfvs_def] >> rw[] >> rfs[] >> metis_tac[]) >>
	fs[APPLY_UPDATE_THM, tfvs_def] >> rfs[] >> metis_tac[])
     >- (rename [`a ∈ ffvs ff`, `x ∈ tfvs (v a)`,`a <> n`] >>
        rfs[APPLY_UPDATE_THM] >> qexists_tac `a` >> simp[] >> 
        simp[VARIANT_def] >>
        qmatch_abbrev_tac `x <> MAX_SET myset + 1` >>
        `FINITE myset` by
	   (rw[Abbr`myset`]
           >- (irule IMAGE_FINITE >> metis_tac[ffvs_FINITE])
	   >- metis_tac[tfvs_FINITE]) >>
        `x IN myset` suffices_by (
         strip_tac >> drule_all in_max_set >> simp[]
        ) >>
        simp[Abbr`myset`,PULL_EXISTS] >> qexists_tac `a` >>
        simp[APPLY_UPDATE_THM]))
  >- (rw[EQ_IMP_THM, Once EXTENSION, PULL_EXISTS]
     >- (rename [`a ∈ ffvs ff`, `x ∈ tfvs (v (|n |-> V n|) a)`] >>
        Cases_on `a = n`
	>- (fs[APPLY_UPDATE_THM, tfvs_def] >> rw[] >> rfs[] >> metis_tac[]) >>
	fs[APPLY_UPDATE_THM, tfvs_def] >> rfs[] >> metis_tac[])
     >- (rename [`a ∈ ffvs ff`, `x ∈ tfvs (v a)`,`a <> n`] >>
	rfs[APPLY_UPDATE_THM] >> qexists_tac `a` >> simp[] >> metis_tac[]))
QED

Theorem ffvs_SKOLEM[simp]:
  !n ff. ffvs (SKOLEM n ff) = ffvs ff
Proof
  ho_match_mp_tac SKOLEM_ind >> rw[SKOLEM_def,ffvs_def] >> fs[ffvs_fsubst] >>
  rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS]
  >- (Cases_on `x' = m` >> fs[APPLY_UPDATE_THM,tfvs_def,MEM_MAP] >>
     `FINITE (ffvs f0)` by metis_tac[ffvs_FINITE] >>
     `FINITE (ffvs f0 DELETE m)` by simp[] >>
     `y IN (ffvs f0 DELETE m)` by metis_tac[MEM_SET_TO_LIST] >> fs[tfvs_def])
  >- (Cases_on `x' = m` >> fs[APPLY_UPDATE_THM,tfvs_def,MEM_MAP] >>
     `FINITE (ffvs f0)` by metis_tac[ffvs_FINITE] >>
     `FINITE (ffvs f0 DELETE m)` by simp[] >>
     `y IN (ffvs f0 DELETE m)` by metis_tac[MEM_SET_TO_LIST] >> fs[tfvs_def])
  >- (qexists_tac `x` >> simp[] >> fs[APPLY_UPDATE_THM,tfvs_def,MEM_MAP])   
QED




(* semantics stuff *)


val _ = Datatype`
        folmodel = <| dom : 'a set ;
                      fnsyms : num -> 'a list -> 'a;
                      predsyms : num -> 'a -> bool;
                      relsyms : num -> 'a -> 'a -> bool;
                      |>`;

val interpret_def = tDefine "interpret" `
  interpret M σ (V n) = σ n /\
  interpret M σ (Fn f l) = M.fnsyms f (MAP (interpret M σ) l)`
 (WF_REL_TAC `measure (fterm_size o SND o SND)` >> rw[] >> drule tsize_lemma >> rw[])


val feval_def = Define`
  feval M σ (fP p t) = M.predsyms p (interpret M σ t) /\
  feval M σ (fR n t1 t2) = M.relsyms n (interpret M σ t1) (interpret M σ t2) /\
  feval M σ (fIMP f1 f2) = (feval M σ f1 ==> feval M σ f2) /\
  feval M σ (fFALSE) = F /\
  feval M σ (fEXISTS n f) = (?x. x IN M.dom /\ feval M ((n=+x)σ) f) /\
  feval M σ (fFORALL n f) = (!x. x IN M.dom ==> feval M ((n=+x)σ) f)`;



val fsatis_def = Define`
  fsatis M σ fform <=> (IMAGE σ univ(:num)) SUBSET M.dom /\
                       feval M σ fform`;


Theorem interpret_tfvs :
  !M σ1 t σ2. (!n. n IN (tfvs t) ==> σ1 n = σ2 n) ==> interpret M σ1 t = interpret M σ2 t
Proof
  ho_match_mp_tac (theorem "interpret_ind") >> rw[tfvs_def,interpret_def] >> AP_TERM_TAC >> irule MAP_CONG
  >> rw[] >> first_x_assum irule >> rw[] >> fs[PULL_EXISTS,MEM_MAP] >> metis_tac[]
QED


Theorem feval_ffvs :
  !M σ1 σ2 f. (!n. n IN (ffvs f) ==> σ1 n = σ2 n) ==> feval M σ1 f = feval M σ2 f
Proof
  Induct_on `f` >> rw[feval_def,ffvs_def]
  >- metis_tac[interpret_tfvs]
  >- metis_tac[interpret_tfvs]
  >- metis_tac[interpret_tfvs]
  >> (`∀m x. m ∈ ffvs f ==> σ1(|n |-> x|) m = σ2(|n|->x|) m` suffices_by metis_tac[] >>
     rw[APPLY_UPDATE_THM]) 
QED


Theorem interpret_tsubst :
  !v t M σ. (interpret M σ (tsubst v t)) = (interpret M (interpret M σ o v) t)
Proof
  ho_match_mp_tac (theorem "tsubst_ind") >> rw[tsubst_def,interpret_def] 
  >> simp[MAP_MAP_o,combinTheory.o_ABS_R] >> AP_TERM_TAC >> irule MAP_CONG >> rw[]
QED


Theorem 

show_types := false


(theorem "interpret_ind")

Theorem feval_fsubst :
  !f v M σ. feval M σ (fsubst v f) = feval M (interpret M σ o v) f
Proof
  Induct_on `f` >> rw[feval_def,tsubst_def,fsubst_def,interpret_tsubst] (* 4 *)
  >- rw[EQ_IMP_THM] (* 2 *)
     >- fs[ffvs_def,tfvs_def] >> Cases_on `y = n` >> fs[APPLY_UPDATE_THM] >>
        Cases_on `v y` >> fs[APPLY_UPDATE_THM,ffvs_def,tfvs_def]
        >- first_x_assum drule >> rw[] 






     >- first_x_assum drule >> qmatch_abbrev_tac`feval M s1 f ==> feval M s2 f` >>
        `s1 = s2` suffices_by simp[] >> rw[Abbr`s1`,Abbr`s2`] >>
	simp[FUN_EQ_THM] >> rw[] >> Cases_on `x' = n` >> fs[APPLY_UPDATE_THM] (* 2 *)
	>- simp[interpret_def] >> Cases_on `n = y` >> fs[] (* 2 *)
	   >- fs[ffvs_def]
	   >- fs[ffvs_def,tfvs_def] >> Cases_on `v y` >> fs[tfvs_def,ffvs_def]

`(interpret M
                  (σ :num -> α)⦇VARIANT
                       (ffvs
                          (fsubst (v :num -> fterm)⦇(n :num) ↦ V n⦈
                             (f :fform))) ↦ x⦈ ∘ v⦇n ↦ V n⦈) =
			     (interpret M (σ :num -> α) ∘ (v :num -> fterm))⦇(n :num) ↦ (x :α)⦈` suffices_by metis_tac[]










`(interpret M σ ∘ v)⦇n ↦ x⦈ =
         (interpret M σ⦇VARIANT (ffvs (fsubst v⦇n ↦ V n⦈ f)) ↦ x⦈ ∘
                v⦇n ↦ V n⦈)` by cheat >> fs[] >> metis_tac[]
      first_x_assum (qspec_then `x` mp_tac) >> rw[] >> 
         `feval M (interpret M σ ∘ v⦇n ↦ x⦈) f =
         feval M (interpret M σ⦇VARIANT (ffvs (fsubst v⦇n ↦ V n⦈ f)) ↦ x⦈ ∘ v⦇n ↦ V n⦈) f` by simp[]
	 simp[FUN_EQ_THM] >> rw[interpret_def] >> Cases_on `x

  fs[]

QED
  


Theorem tsubst_V :
  !t. tsubst V t = t
Proof
  completeInduct_on `fterm_size t` >> rw[tsubst_def] >>
  Cases_on `t` >> rw[tsubst_def] >> irule LIST_EQ >> rw[EL_MAP] >>
  `fterm_size (EL x l) < fterm_size (Fn n l)` suffices_by metis_tac[] >> simp[fterm_size_def] >>
  `MEM (EL x l) l` by metis_tac[MEM_EL] >> drule tsize_lemma >> rw[]
QED

Theorem size_nonzero :
  !f. 0 < size f
Proof
  Induct_on `f` >> fs[size_def]
QED



Theorem fsubst_V :
  !f. fsubst V f = f
Proof
  completeInduct_on `size f` >> rw[] >> Cases_on `f` >> rw[fsubst_def] >> rw[tsubst_V] (* 8 *)
  >- (first_x_assum irule >> qexists_tac `size f'` >> rw[size_def] >> simp[size_nonzero])
  >- (first_x_assum irule >> qexists_tac `size f0` >> rw[size_def,size_nonzero])
  >- (Cases_on `y = n` >> fs[APPLY_UPDATE_THM] (* 2 *) >> fs[ffvs_def,tfvs_def])
  >- (`V⦇n ↦ V n⦈ = V` by (rw[FUN_EQ_THM] >> Cases_on `x = n` >> fs[APPLY_UPDATE_THM]) >> fs[] >>
     first_x_assum irule >> qexists_tac `size f'` >> rw[size_def,size_nonzero])
  >- (`V⦇n ↦ V n⦈ = V` by (rw[FUN_EQ_THM] >> Cases_on `x = n` >> fs[APPLY_UPDATE_THM]) >> fs[] >>
     first_x_assum irule >> qexists_tac `size f'` >> rw[size_def,size_nonzero])
  >- (Cases_on `y = n` >> fs[APPLY_UPDATE_THM] (* 2 *) >> fs[ffvs_def,tfvs_def])
  >> (`V⦇n ↦ V n⦈ = V` by (rw[FUN_EQ_THM] >> Cases_on `x = n` >> fs[APPLY_UPDATE_THM]) >> fs[] >>
     first_x_assum irule >> qexists_tac `size f'` >> rw[size_def,size_nonzero])
QED


Theorem Prenex_right_fsatis :
  !M σ f1 f2. fsatis M σ (fIMP f1 f2) <=> fsatis M σ (Prenex_right f1 f2)
Proof
  completeInduct_on `size f2` >> rw[fsatis_def,Prenex_right_def,feval_def] >>
  Cases_on `f2` (* 6 *)
  >> fs[feval_def,Prenex_right_def] (* 2 *)
  >- rw[EQ_IMP_THM] (* 2 *)
     >- first_x_assum (qspec_then `size f` mp_tac) >> rw[] >>
     `size f < size (fFORALL n f)` by rw[size_def] >>
     first_x_assum drule >> rw[] >>
     first_x_assum (qspec_then `fsubst V⦇n ↦ V (VARIANT (ffvs (fFORALL n f) ∪ ffvs f1))⦈ f` mp_tac) >> rw[] >>
     `size f =
             size
               (fsubst V⦇n ↦ V (VARIANT (ffvs (fFORALL n f) ∪ ffvs f1))⦈ f)`
       by metis_tac[size_fsubst] >>
     first_x_assum (qspec_then `M` mp_tac) >> rw[] >>
     first_x_assum (qspec_then `σ⦇VARIANT (ffvs (fFORALL n f) ∪ ffvs f1) ↦ x⦈` mp_tac) >> rw[] >>
     first_x_assum (qspec_then `f1` mp_tac) >> rw[] >>
     `fsatis M σ⦇VARIANT (ffvs (fFORALL n f) ∪ ffvs f1) ↦ x⦈
           (fIMP f1
              (fsubst V⦇n ↦ V (VARIANT (ffvs (fFORALL n f) ∪ ffvs f1))⦈ f))` suffices_by metis_tac[fsatis_def] >>
     `feval M σ⦇VARIANT (ffvs (fFORALL n f) ∪ ffvs f1) ↦ x⦈
     (fIMP f1 (fsubst V⦇n ↦ V (VARIANT (ffvs (fFORALL n f) ∪ ffvs f1))⦈ f))` suffices_by cheat >>
     rw[feval_def] >>
     qabbrev_tac `a = VARIANT (ffvs (fFORALL n f) ∪ ffvs f1)` >>
     `feval M σ f1 ⇒ feval M σ⦇n ↦ x⦈ f` by metis_tac[] >>
     `feval M σ f1 = feval M σ⦇a ↦ x⦈ f1` by
       (irule feval_ffvs >> rw[] >> Cases_on `n' = a` >> fs[APPLY_UPDATE_THM,Abbr`a`,VARIANT_def] >>
       `FINITE (ffvs f1)` by metis_tac[ffvs_FINITE] >>
       `MAX_SET (ffvs (fFORALL n f) ∪ ffvs f1) + 1 <= MAX_SET (ffvs (fFORALL n f) ∪ ffvs f1)` suffices_by fs[] >>
       irule in_max_set >> rw[] >> metis_tac[ffvs_FINITE]) >>
     `feval M σ⦇n ↦ x⦈ f` by metis_tac[] >> Cases_on `a = n` >> rw[] (* 2 *)
       >- (`V⦇a ↦ V a⦈ = V` by (rw[FUN_EQ_THM] >> Cases_on `x' = a` >> rw[APPLY_UPDATE_THM]) >>
          simp[fsubst_V])
       >- 
        
          
     
     
     
  

QED


Theorem Prenex_left_fsatis :
  !f1 f2 M σ. feval M σ (Prenex_left (Prenex f1) (Prenex f2)) <=> (feval M σ f1 ⇒ feval M σ f2) 
Proof
  Induct_on `f1` >> fs[Prenex_left_def] >> rw[EQ_IMP_THM] (* 12 *)
  >- fs[feval_def]
  >- fs[Prenex_def,Prenex_left_def]
QED


Theorem Prenex_fsatis:
  !M σ f. fsatis M σ f <=> fsatis M σ (Prenex f)
Proof
  Induct_on `f` >> rw[fsatis_def,feval_def,Prenex_def] (* 3 *)xs
  >- rw[EQ_IMP_THM] (* 2 *)
     >- Cases_on `f` >> rw[Prenex_left_def]
        >- rw[EQ_IMP_THM]
	   >- rw[Prenex_left_def,Prenex_def,feval_def,]
QED





val _ = export_theory();

