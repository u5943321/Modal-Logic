open HolKernel Parse boolLib bossLib;

open chap1Theory chap2_1Theory chap2_2Theory chap2_3revisedTheory chap2_4revisedTheory chap2_5Theory chap2_6Theory chap2_7Theory lemma2_73Theory pred_setTheory pairTheory folLangTheory folModelsTheory ultraproductTheory

val _ = new_theory "prettyPrinting";

(* val _ = remove_termtok { tok = " *)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Infixr 200,
                  term_name = "==>",
                  pp_elements = [HardSpace 1, TOK "⇒", BreakSpace(1,2)]}


val Fun_component_def = Define`
  Fun_component FMS n fs i = (FMS i).Fun n (MAP (λfc. CHOICE fc i) fs)`;


val Pred_component_def = Define`
  Pred_component FMS p zs i = (FMS i).Pred p (MAP (λfc. CHOICE fc i) zs)`;


Theorem ppultraproduct_folmodel_def:
 ∀U I FMS.
            ultraproduct_folmodel U I FMS =
            <|Dom := ultraproduct U I (\i. (FMS i).Dom);
              Fun :=
                (λn fs.
                     {y |
                      (∀i. i ∈ I ⇒ y i ∈ (FMS i).Dom) ∧
                      {i |
                       i ∈ I ∧
                       y i = Fun_component FMS n fs i} ∈ U});
              Pred :=
                (λp zs.
                     {i | i ∈ I ∧ Pred_component FMS p zs i} ∈
                     U)|>
Proof
rw[ultraproduct_folmodel_def,Fun_component_def,Pred_component_def,folmodels2Doms_def]
QED

Theorem ppultraproduct_model_def:
∀U I MS.
            ultraproduct_model U I MS =
            <|frame :=
                <|world := ultraproduct U I (\i. (MS i).frame.world);
                  rel :=
                    (λfu gu.
                         ∃f g.
                             f ∈ fu ∧ g ∈ gu ∧
                             {i | i ∈ I ∧ (MS i).frame.rel (f i) (g i)} ∈ U)|>;
              valt :=
                (λp fu. ∃f. f ∈ fu ∧ {i | i ∈ I ∧ f i ∈ (MS i).valt p} ∈ U)|>
Proof
rw[ultraproduct_model_def,models2worlds_def]
QED




Theorem ppcompactness_thm_L1tau:
!A. (INFINITE 𝕌(:α) /\
     (∀f. f ∈ A ⇒ L1tau f) ∧
         (∀ss.
              FINITE ss ∧ ss ⊆ A ⇒
              ∃M σ:num -> α. valuation M σ ∧ ∀ff. ff ∈ ss ⇒ feval M σ ff)) ⇒
         ∃M σ:num -> α. valuation M σ ∧ ∀f. f ∈ A ⇒ feval M σ f
Proof
rw[] >> drule compactness_thm_L1tau >> rw[]
QED

Theorem ppcompactness_corollary_L1tau:
!A a. (INFINITE 𝕌(:α) /\ L1tau a /\
         (∀f. f ∈ A ⇒ L1tau f) ∧
         (∀M σ:num -> α. valuation M σ ⇒ (∀f. f ∈ A ⇒ feval M σ f) ⇒ feval M σ a)) ⇒
         ∃ss.
             FINITE ss ∧ ss ⊆ A ∧
             ∀M σ:num -> α. valuation M σ ⇒ (∀f. f ∈ ss ⇒ feval M σ f) ⇒ feval M σ a
Proof
rw[] >> drule compactness_corollary_L1tau >> rw[]
QED

Theorem ppexpansion_shift_feval:
  !M A M' f σ phi. (BIJ f (count (CARD A)) A /\ valuation (mm2folm M) σ /\
                    (form_functions phi ⊆ {(c1,0) | c1 < (CARD A)})) ==>
                    (feval (expand (mm2folm M) A f) σ phi <=>
                    feval (mm2folm M) (shift_valuation (CARD A) σ f) (shift_form (CARD A) phi))
Proof
rw[] >> irule expansion_shift_feval >> rw[]
>- (fs[FC_def] >>
   qspec_then `phi` assume_tac FC_form_functions >>
   fs[SUBSET_DEF] >> first_x_assum drule >> rw[] >> Cases_on `c'` >> rw[] >>
   first_x_assum drule >> rw[]) >>
fs[mm2folm_def,valuation_def,IMAGE_DEF,SUBSET_DEF] >> metis_tac[]
QED




Theorem ppthm_A_19_ii:
!U I phi σ FMS. (ultrafilter U I /\
                 (valuation (ultraproduct_folmodel U I FMS) σ) /\
                 (!i. i IN I ==> wffm (FMS i))) ==>
                  (feval (ultraproduct_folmodel U I FMS) σ phi <=>
                  {i | i IN I /\ feval (FMS i) (\x. (CHOICE (σ x)) i) phi} IN U)
Proof
rw[] >> drule thm_A_19_ii >> rw[] >> first_x_assum irule >>
 fs[IMAGE_DEF,valuation_def,wffm_def,SUBSET_DEF,ultraproduct_folmodel_def] >>
metis_tac[]
QED

Theorem ppultraproduct_comm_feval:
  !phi U I MS σ.
 (ultrafilter U I /\
         form_functions phi = ∅ /\
         valuation (mm2folm (ultraproduct_model U I MS)) σ) ⇒
             (feval (mm2folm (ultraproduct_model U I MS)) σ phi ⇔
              feval (ultraproduct_folmodel U I (λi. mm2folm (MS i))) σ phi)
Proof
rw[] >> drule ultraproduct_comm_feval >>
strip_tac >>
rw[] >>
`IMAGE σ 𝕌(:num) ⊆ ultraproduct U I' (models2worlds MS)` suffices_by metis_tac[] >>
rw[IMAGE_DEF,SUBSET_DEF] >> fs[valuation_def,ultraproduct_model_def,mm2folm_def]
QED



Theorem ppmodal_compactness_thm:
(INFINITE 𝕌(:α) /\ (∀ss:chap1$form -> bool.
                 FINITE ss ∧ ss ⊆ s ⇒
                 ∃M w:α. w ∈ M.frame.world ∧ ∀f. f ∈ ss ⇒ satis M w f)) ⇒
            ∃M w:α. w ∈ M.frame.world ∧ ∀f. f ∈ s ⇒ satis M w f
Proof
metis_tac[modal_compactness_thm]
QED



Theorem ppmodal_compactness_corollary:
INFINITE 𝕌(:α) /\
        (∀M w:α.
                 w ∈ M.frame.world ⇒ (∀f. f ∈ s ⇒ satis M w f) ⇒ satis M w a) ⇒
            ∃ss:chap1$form -> bool.
                FINITE ss ∧ ss ⊆ s ∧
                ∀M w:α.
                    w ∈ M.frame.world ⇒
                    (∀f. f ∈ ss ⇒ satis M w f) ⇒
                    satis M w a
Proof
metis_tac[modal_compactness_corollary]
QED


val UE'_def = Define`
  UE' M = <| frame := <| world := {u | ultrafilter u M.frame.world};
                        rel :=  \u v.
            (ultrafilter u M.frame.world ∧ ultrafilter v M.frame.world ∧
            ∀X. X ∈ v ⇒ can_see M X ∈ u) |>;
            valt := \p v. (ultrafilter v M.frame.world /\
            {w | w IN M.frame.world /\  M.valt p w } IN v)|>`;

val _ = overload_on("Mw", “λM. M.frame.world”);

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Mw)"],
                  term_name = "Mw", paren_style = OnlyIfNecessary}

val _ = overload_on("Mr", “\M. M.frame.rel”);

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Mr)"],
                  term_name = "Mr", paren_style = OnlyIfNecessary}


val _ = overload_on("Mv", “λM. M.valt”);

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Mv)"],
                  term_name = "Mv", paren_style = OnlyIfNecessary}

val _ = overload_on("equiv", “equiv0”);


val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                          fixity = Infix(NONASSOC, 450),
                          pp_elements = [TOK "(forces1)", TM,
                                         TOK "(forces2)", BreakSpace (1,2)],
                          term_name = "satis", paren_style = OnlyIfNecessary}
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix(NONASSOC, 450),
                  pp_elements = [TOK "(nforces1)", TM,
                                 TOK "(nforces2)", BreakSpace (1,2)],
                  term_name = "nsatis", paren_style = OnlyIfNecessary}

val _ = overload_on("nsatis", “λM w f. ~satis M w f”);

val _ = app clear_overloads_on ["◇", "□"]

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Prefix 900, pp_elements = [TOK "◇"],
                  term_name = "DIAM", paren_style = OnlyIfNecessary}
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Prefix 900, pp_elements = [TOK "□"],
                  term_name = "BOX", paren_style = OnlyIfNecessary}


Overload UPM = ``\U MS. ultraproduct_folmodel U (J:α -> bool) MS``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(UPM1)", TM, TOK "(UPM2)"],
                  term_name = "UPM", paren_style = OnlyIfNecessary}


Overload UPMN = ``\U MS. ultraproduct_folmodel U (J:num -> bool) MS``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(UPMN1)", TM, TOK "(UPMN2)"],
                  term_name = "UPMN", paren_style = OnlyIfNecessary}


Overload myequiv = ``\f1 ty f2. equiv0 ty f1 f2``


val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(meq1)", TM, TOK "(meq2)"],
                  term_name = "myequiv", paren_style = OnlyIfNecessary}


Overload myfeq = ``\f1 ty f2. feq ty f1 f2``


val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [HardSpace 2, TOK "(mfeq1)", TM, TOK "(mfeq2)", BreakSpace (2,0)],
                  term_name = "myfeq", paren_style = OnlyIfNecessary}




Overload upr = ``\f U A g. Uequiv U (J: α -> bool) A f g``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(upr1)", TM, TOK "(upr2)",TM, TOK "(upr3)"],
                  term_name = "upr", paren_style = OnlyIfNecessary}

Overload uprr = ``\U A. Uequiv U (J: α -> bool) A``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix,
                  pp_elements = [TOK "(uprr1)", TM, TOK "(uprr2)",TM, TOK "(uprr3)"],
                  term_name = "uprr", paren_style = OnlyIfNecessary}

Overload uprn = ``\f U A g. Uequiv U (J: num -> bool) A f g``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(uprn1)", TM, TOK "(uprn2)",TM, TOK "(uprn3)"],
                  term_name = "uprn", paren_style = OnlyIfNecessary}

Overload uprrn = ``\U A. Uequiv U (J: num -> bool) A``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix,
                  pp_elements = [TOK "(uprrn1)", TM, TOK "(uprrn2)",TM, TOK "(uprrn3)"],
                  term_name = "uprrn", paren_style = OnlyIfNecessary}


Overload pt = ``\s r.partition r s``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (LEFT, 500),
                  pp_elements = [TOK "(ptt)"],
                  term_name = "pt", paren_style = OnlyIfNecessary}
(*
Overload cp = ``\J A. Cart_prod (J:α -> bool)  A``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(cp1)", TM, TOK "(cp2)", TM, TOK "(cp3)"],
                  term_name = "cp", paren_style = OnlyIfNecessary}
*)

Overload disj = ``\f1 f2. DISJ f1 f2``
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(disj)"],
                  term_name = "disj", paren_style = OnlyIfNecessary}

Overload fdisj = ``\f1 f2. fDISJ f1 f2``
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(fdisj)"],
                  term_name = "fdisj", paren_style = OnlyIfNecessary}

Overload fimp = ``\f1 f2. IMP (f1: folLang$form) f2``
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(fimp)"],
                  term_name = "fimp", paren_style = OnlyIfNecessary}


Overload ad = ``\f1 f2. AND f1 f2``
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(ad)"],
                  term_name = "ad", paren_style = OnlyIfNecessary}


Overload fad = ``\f1 f2. fAND f1 f2``
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(fad)"],
                  term_name = "fad", paren_style = OnlyIfNecessary}


Overload rst = ``\r s. RESTRICT r s``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(rst1)", TM, TOK "(rst2)", TM, TOK "(rst3)"],
                  term_name = "rst", paren_style = OnlyIfNecessary}

Overload mdeq = ``\M1 w1 M2 w2. modal_eq M1 M2 w1 w2``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(mdeq1)", TM, TOK "(mdeq2)", TM, TOK "(mdeq3)"],
                  term_name = "mdeq", paren_style = OnlyIfNecessary}


Overload gsm = ``\M1 M2. GENSUBMODEL M1 M2``
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(gsm)"],
                  term_name = "gsm", paren_style = OnlyIfNecessary}


Overload hom = ``\M1 f M2. hom f M1 M2``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(hom1)", TM, TOK "(hom2)"],
                  term_name = "hom", paren_style = OnlyIfNecessary}


Overload bisim' = ``\M1 Z M2. bisim Z M1 M2``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(bisim1)", TM, TOK "(bisim2)"],
                  term_name = "bisim'", paren_style = OnlyIfNecessary}


Overload bw = ``\M1 w1 M2 w2. bisim_world M1 M2 w1 w2``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(bw1)", TM, EndInitialBlock(PP.CONSISTENT,0), TOK "(bw2)",
                                 BeginFinalBlock(PP.CONSISTENT,0), TM, TOK "(bw3)"],
                  term_name = "bw", paren_style = OnlyIfNecessary}

Overload nbw = ``\M1 w1 f n M2 w2. nbisim M1 M2 f n w1 w2``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(nbw1)", TM, TOK "(nbw2)", TM, TOK "(nbw3)",TM, TOK "(nbw4)",TM, TOK "(nbw5)"],
                  term_name = "nbw", paren_style = OnlyIfNecessary}

Overload cs = ``\M X. can_see M (X: α -> bool)``
Overload cs = ``\M X. can_see M (X: β -> bool)``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(cs1)", TM, TOK "(cs2)",TM, TOK"(cs3)"],
                  term_name = "cs", paren_style = OnlyIfNecessary}



Overload os = ``\M X. only_see M (X:α -> bool) ``
Overload os = ``\M X. only_see M (X:β -> bool) ``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(os1)", TM, TOK "(os2)",TM, TOK "(os3)"],
                  term_name = "os", paren_style = OnlyIfNecessary}

Overload uer = ``\M. UE_rel M``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(uer1)", TM, TOK "(uer2)"],
                  term_name = "uer", paren_style = OnlyIfNecessary}

Overload ue = ``\M. UE M``
Overload ue = ``\M. UE' M``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(ue1)", TM, TOK "(ue2)"],
                  term_name = "ue", paren_style = OnlyIfNecessary}

Overload pf = ``\w s. principle_UF w s``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(pf1)", TM, TOK "(pf2)", TM, TOK "(pf3)"],
                  term_name = "pf", paren_style = OnlyIfNecessary}

Overload sim = ``\M1 Z M2. sim Z M1 M2``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(sim1)", TM, TOK "(sim2)"],
                  term_name = "sim", paren_style = OnlyIfNecessary}

Overload fev = ``\M σ f. feval M σ f``



val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                          fixity = Infix(NONASSOC, 450),
                          pp_elements = [TOK "(fev1)", TM,
                                         TOK "(fev2)", BreakSpace (1,2)],
                          term_name = "fev", paren_style = OnlyIfNecessary}

Overload bmi = ``\M1 f M2. bounded_mor_image f M1 M2``


val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC, 450),
                  pp_elements = [TOK "(bmi1)", TM, TOK "(bmi2)"],
                  term_name = "bmi", paren_style = OnlyIfNecessary}

Overload fPred = “\a l. Pred a l”


val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix,
                  pp_elements = [TOK "(M3)"],
                  term_name = "M3", paren_style = OnlyIfNecessary}

Overload st = ``\x. ST x``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix,
                  pp_elements = [TOK "(st1)", TM, TOK "(st2)"],
                  term_name = "st", paren_style = OnlyIfNecessary}
(*added*)
Overload mnot = ``\phi:form. NOT phi``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix,
                  pp_elements = [TOK "(mnot1)", TM, TOK "(mnot2)"],
                  term_name = "mnot", paren_style = OnlyIfNecessary}

		 

Overload fst = ``\M σ f. fsatis M σ f``



val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                          fixity = Infix(NONASSOC, 450),
                          pp_elements = [TOK "(fst1)", TM,
                                         TOK "(fst2)", BreakSpace (1,2)],
                          term_name = "fst", paren_style = OnlyIfNecessary}


Overload UPMM = ``\U MS. ultraproduct_model U (J:α -> bool) MS``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(UPMM1)", TM, TOK "(UPMM2)"],
                  term_name = "UPMM", paren_style = OnlyIfNecessary}

Overload UPMMN = ``\U MS. ultraproduct_model U (J:num -> bool) MS``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(UPMMN1)", TM, TOK "(UPMMN2)"],
                  term_name = "UPMMN", paren_style = OnlyIfNecessary}

Overload Emu = ``\s. s //E (:β)``

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, pp_elements = [TOK "(Emu1)", TM, TOK "(Emu2)"],
                  term_name = "Emu", paren_style = OnlyIfNecessary}

Overload univn = ``univ(:num)``

Overload FM = ``(M:'a folModels$model)``
Overload FM = ``(M:'b folModels$model)``

Overload MM = ``M:'a chap1$model``
Overload MM = ``M:'b chap1$model``


val _ = export_theory();
