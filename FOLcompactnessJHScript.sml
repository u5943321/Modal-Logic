open HolKernel Parse boolLib bossLib;
open HolKernel Parse boolLib bossLib;
open combinTheory;
open pred_setTheory;
open relationTheory;
open arithmeticTheory;
open set_relationTheory;


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

val (prenex_rules, prenex_ind, prenex_cases) = Hol_reln`
  (!ff. qfree ff ==> prenex ff) /\
  (!ff n. prenex ff ==> prenex (fEXISTS n ff)) /\
  (!ff n. prenex ff ==> prenex (fFORALL n ff))`

val (universal_rules, universal_ind, universal_cases) = Hol_reln`
  (!ff. qfree ff ==> universal ff) /\
  (!ff n. prenex ff ==> universal (fFORALL n ff))`

val Prenex_right_def = tDefine "Prenex_right" `
  Prenex_right p fFALSE = fIMP p fFALSE /\
  Prenex_right p (fR a t1 t2) = fIMP p (fR a t1 t2) /\
  Prenex_right p (fP a t) = fIMP p (fP a t) /\
  Prenex_right p (fIMP ff1 ff2) = fIMP p (fIMP ff1 ff2) /\
  Prenex_right p (fFORALL n q) = fFORALL (VARIANT ((ffvs (fFORALL n q) ∪ (ffvs p))))
                                         (Prenex_right p (fsubst ((n =+ fVar (VARIANT ((ffvs (fEXISTS n q) ∪ (ffvs p))))) fVar) q)) /\
  
  ` (WF_REL_TAC `measure (size o SND)` >> rw[] (* 2 *)
     >- (`size (fsubst ((n =+ fVar (VARIANT (ffvs (fEXISTS n (fNOT ff0)) ∪ ffvs p))) fVar) ff0) = size ff0`
          by metis_tac[size_fsubst] >>
	`size ff0 < size (fNOT (fEXISTS n (fNOT ff0)))` suffices_by metis_tac[] >> rw[size_def])
     >- (`size (fsubst ((n =+ fVar (VARIANT (ffvs (fEXISTS n q) ∪ ffvs p))) fVar) q) = size q`
          by metis_tac[size_fsubst] >>
`size q < size (fEXISTS n q)` suffices_by metis_tac[] >> rw[size_def]))




val size_def = Define`
  size fFALSE = 1 /\
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

val Prenex_right_prenex = store_thm(
	"Prenex_right_prenex",
	``


val Prenex_left_def = tDefine "Prenex_left" `
Prenex_left fFALSE p = Prenex_right fFALSE p /\
Prenex_left (fR a t1 t2) p = Prenex_right (fR a t1 t2) p /\
Prenex_left (fP a t) p = Prenex_right (fP a t) p /\
Prenex_left (fIMP ff1 ff2) p = fIMP (fIMP ff1 ff2) p /\
(Prenex_left (fFORALL n q) p = let y = VARIANT ((ffvs (fFORALL n q) ∪ (ffvs p))) in
				  fEXISTS y (Prenex_left (fsubst ((n =+ V y) V) q) p)) /\
Prenex_left (fEXISTS n q) p = let y = VARIANT ((ffvs (fEXISTS n q) ∪ (ffvs p))) in
				  fFORALL y (Prenex_left (fsubst ((n =+ V y) V) q) p)`
(WF_REL_TAC `measure (size o FST)` >> rw[] (* 2 *)
     >- (`size (fsubst V⦇n ↦ V (VARIANT (ffvs (fEXISTS n q) ∪ ffvs p))⦈ q) = size q`
          by metis_tac[size_fsubst] >> rw[size_def] >> fs[])
     >- (`size (fsubst V⦇n ↦ V (VARIANT (ffvs (fFORALL n q) ∪ ffvs p))⦈ q) = size q`
          by metis_tac[size_fsubst] >> rw[size_def] >> fs[]))




val qfree_Prenex_left = store_thm(
  "qfree_Prenex_left",
``!f1. qfree f1 ==> !f2. qfree f2 ==> Prenex_left f1 f2 = fIMP f1 f2``,
Induct_on `f1` >> rw[]



val Prenex_left_subst = store_thm(
  "Prenex_left_subst",
``!f. prenex f ==> !f1 f2. f = (Prenex_left f1 f2) ==> !v. prenex (Prenex_left (fsubst v f1) f2)``,	








val COUNT_Q_def = Define`
COUNT_Q fFALSE = 0 /\
COUNT_Q (fR a t1 t2) = 0 /\
COUNT_Q (fP a t) = 0 /\
COUNT_Q 

val prenex_Prenex_left = store_thm(
  "prenex_Prenex_left",							       
  ``!f1. prenex f1 ==> !f2. prenex f2 ==> prenex (Prenex_left f1 f2)``,
  Induct_on `prenex f1` >> strip_tac (* 2 *)
	    >- strip_tac >> strip_tac >> Induct_on `prenex f2` >> strip_tac (* 2 *)
	      >- rw[] >> (* qfree_Prenex_left *) cheat
              >- strip_tac (* 2 *)
                 >- Induct_on `prenex f2`



val prenex_Prenex_left = store_thm(
  "prenex_Prenex_left",							       
  ``!f1. prenex f1 ==> !f2. prenex f2 ==> prenex (Prenex_left f1 f2)``,
  Induct_on `prenex f1` >> rw[] (* 3 *)
	    >- `!f2. prenex f2 ==> prenex (Prenex_left f1 f2)` suffices_by metis_tac[] >> Induct_on `prenex f2` >> rw[] (* 3 *)
	      >- (*  prenex_Prenex_left *) cheat
	      >- `prenex (Prenex_right f1 (fEXISTS n f2'))` suffices_by cheat (* if LHS is pform then pl does not do anything *) >>
	         rw[Prenex_right_def] >> 
                 `prenex (Prenex_right f1 f2')` by cheat (* (Prenex_left f1 f2') = (Prenex_right f1 f2') when qfree f1 *) >>
                 (* fsubst does not change prenex *) cheat
	      >- (* similar as existence case *) cheat	 
            >- `prenex (Prenex_left f1 f2)` by metis_tac[] >> rw[Prenex_left_def]
               



	
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
>- rw[Prenex_def] >> 

>- (rw[Prenex_def] >> metis_tac[prenex_rules])
>- (rw[Prenex_def] >> metis_tac[prenex_rules])
Cases_on `ff` 
>- Cases_on `ff'`
  >- cheat (* 3 *) rw[Prenex_def,Prenex_left_def,Prenex_right_def]






EVAL ``Prenex (fIMP (fFORALL n (fIMP (fFORALL n (fP a (V n))) (fR b (V n) (V n)))) (fEXISTS n (fR c (V  n) (V n))))``
			       
val _ = export_theory();

