
open HolKernel Parse boolLib bossLib;

val _ = new_theory "FOL";

val _ = Datatype`
        fterm = ftv num
	       | ffn num (fterm list);
	fform = fRrel fterm fterm
	       | fVrel 'a fterm
	       | fDISJ fform fform
	       | fNOT fform
	       | fEXISTS num fform
	       | fEQ fterm fterm`;


val _ = Datatype`
        fterm = ftv num
	       | ffn num (fterm list);
	fform = fRrel fterm fterm
	       | fVrel 'a fterm
	       | fDISJ fform fform
	       | fNOT fform
	       | fFORALL num fform
	       | fEQ fterm fterm`;

val fAND_def = Define`
  fAND ff1 ff2 = fDISJ (fNOT ff1) (fNOT ff2)`;

val fEXISTS_def = Define`
  fEXISTS n:num fform = 

val ST_def = Define`
  ST x (VAR p) = fVrel p (ftv x) /\
  ST x (FALSE) = fNOT (fEQ (ftv x) (ftv x)) /\
  ST x (NOT phi) = fNOT (ST x phi) /\
  ST x (DISJ phi psi) = fDISJ (ST x phi) (ST x psi) /\
  ST x (DIAM phi) = fEXISTS (x + 1) (fAND (fRrel (ftv x) (ftv (x + 1))) (ST (x + 1) phi))`;

val ST_BOX = store_thm(
  "ST_BOX",
  ``ST x (BOX phi) = 

val _ = export_theory();

