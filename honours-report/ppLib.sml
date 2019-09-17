structure ppLib =
struct

local open HolKernel Parse boolLib set_relationTheory chap2_1Theory chap2_2Theory chap2_3Theory chap2_4revisedTheory chap2_5Theory chap2_6Theory chap2_7Theory folLangTheory folModelsTheory
           IBCDNFrevisedTheory ultrafilterTheory ultraproductTheory lemma2_73Theory prettyPrintingTheory
in

val _ = temp_remove_termtok { tok = "=", term_name ="="}
val _ = temp_add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                       paren_style = OnlyIfNecessary,
		       fixity = Infix(NONASSOC, 450),
		       term_name = "=",
		       pp_elements = [HardSpace 1, TOK "=", BreakSpace(1,2),
		                      BeginFinalBlock(PP.CONSISTENT, 2)]}

val _ = temp_remove_termtok { tok = "⇔", term_name ="<=>"}
val _ = temp_add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                       paren_style = OnlyIfNecessary,
		       fixity = Infix(NONASSOC, 100),
		       term_name = "<=>",
		       pp_elements = [HardSpace 1, TOK "⇔", BreakSpace(1,2),
		                      BeginFinalBlock(PP.CONSISTENT, 2)]}



end (* local *)
val _ = Parse.type_abbrev_pp ("form", ``:'a chap1$form``);
val _ = Parse.type_abbrev_pp ("model", ``:('a,'b) chap1$model``);
val _ = Parse.overload_on ("pvalue", ``peval``);
end (* struct *)
