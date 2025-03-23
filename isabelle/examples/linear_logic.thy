theory linear_logic
imports "../operators" "../entailment" "HOL-Eisbach.Eisbach"
begin

(*A custom prover for this theory ("theory-method")*)
(*Current implementation is very brute! It consists of mindless definition-unfolding followed by
 invocation of ground HOL-provers (extensionality is applied in between, if no success at first).
 A decent implementation shall unfold definitions gradually and call custom methods at each layer*)
method skip = (tactic \<open>all_tac\<close>)
method them = (unfold endorel_defs rel_defs func_defs comb_defs) ;
              (auto | metis | smt) ; ((rule ext)+ | skip) ; (auto | metis | smt)


section \<open>Recap from the theory of relations\<close>

(*Literature on relational algebra informally classifies relational connectives into two groups:
 a so-called "Boolean" (aka. additive) and a "Peircean" (aka. multiplicative) structure.
 When seen as set-valued functions, we can see that the former is in fact 'inherited' from sets, while
 the latter comes from their generalized (i.e. partial and non-deterministic) functional structure.*)

(*Remember that these relational binary operations (composition and its dual) are associative*)
lemma "A ;\<^sup>r (B ;\<^sup>r C) = (A ;\<^sup>r B) ;\<^sup>r C" by them
lemma "A \<dagger>\<^sup>r (B \<dagger>\<^sup>r C) = (A \<dagger>\<^sup>r B) \<dagger>\<^sup>r C" by them

(*Also note that the operation of cotransposition can act as a negation wrt. some relational operations*)
lemma "R\<^sup>\<sim>\<^sup>\<sim> = R" by them (*involutivity: double-negation *)
lemma "\<UU>\<^sup>r\<^sup>\<sim> = \<emptyset>\<^sup>r" by them (*swapping top and bottom*)
lemma "\<Q>\<^sup>\<sim> = \<D>" by them  (*swapping identity and anti-identity (difference)*)

(*Cotransposition validates De Morgan laws wrt union and intersection*)
lemma "(R \<inter>\<^sup>r S)\<^sup>\<sim> = (R\<^sup>\<sim>) \<union>\<^sup>r (S\<^sup>\<sim>)" by them
lemma "(R \<union>\<^sup>r S)\<^sup>\<sim> = (R\<^sup>\<sim>) \<inter>\<^sup>r (S\<^sup>\<sim>)" by them

(*Cotransposition validates 'flipped' De Morgan-like laws wrt composition and its dual*)
lemma "(R ;\<^sup>r S)\<^sup>\<sim> = (S\<^sup>\<sim>) \<dagger>\<^sup>r (R\<^sup>\<sim>)" by them
lemma "(R \<dagger>\<^sup>r S)\<^sup>\<sim> = (S\<^sup>\<sim>) ;\<^sup>r (R\<^sup>\<sim>)" by them

(*Cotransposition also acts as a negation wrt residuals*)
lemma "(A \<Zrres>\<^sup>r B)\<^sup>\<sim> = (A \<circ>\<^sup>r (B\<^sup>\<sim>))" by them
lemma "(A \<Znrres>\<^sup>r B)\<^sup>\<sim> = (A ;\<^sup>r (B\<^sup>\<sim>))" by them

(*The strong-identity-interior and weak-difference-closure operators are dual wrt. cotransposition*)
lemma "R\<^sup>!\<^sup>\<sim> = R\<^sup>\<sim>\<^sup>?" by them
lemma "R\<^sup>?\<^sup>\<sim> = R\<^sup>\<sim>\<^sup>!" by them

(*Cotransposition validates "excluded middle" and "ex contradictio" with \<Q> resp. \<D> as top resp. bottom*)
lemma "\<Q> \<subseteq>\<^sup>r (R \<dagger>\<^sup>r (R\<^sup>\<sim>))" by them
lemma "(R ;\<^sup>r (R\<^sup>\<sim>)) \<subseteq>\<^sup>r \<D>" by them


section \<open>Cyclic Linear Logic\<close>

(*We show how (extended) relation algebra can interpret a non-commutative, cyclic variant of linear logic.*)
(*If modal logic can be said to adopt the "propositions as sets (of states)" paradigm. The present
 encoding can be paraphrased as "propositions as relations (between states)". Understanding propositions
 as sets of transitions between states offers an enriching dynamic perspective.*)

(*Nullary connectives are interpreted as relational constants*)
abbreviation(input) ll_one::"ERel('a)"  ("\<^bold>1") where  "\<^bold>1 \<equiv> \<Q>"
abbreviation(input) ll_bot::"ERel('a)"  ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<D>"
abbreviation(input) ll_zero::"ERel('a)" ("\<^bold>0") where  "\<^bold>0 \<equiv> \<emptyset>\<^sup>r"
abbreviation(input) ll_top::"ERel('a)"  ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<UU>\<^sup>r"

(*Negation is interpreted as relational cotransposition (the transposition/converse of the complement)*)
abbreviation(input) ll_neg::"EOp(ERel('a))"  ("(_)\<^sup>\<bottom>") where "r\<^sup>\<bottom> \<equiv> r\<^sup>\<sim>"

(*The "additive" binary connectives are interpreted with "Boolean" binary operations*)
abbreviation(input) ll_plus::"EOp\<^sub>2(ERel('a))" (infix "\<^bold>\<oplus>" 99) where "(\<^bold>\<oplus>) \<equiv> (\<union>\<^sup>r)"
abbreviation(input) ll_with::"EOp\<^sub>2(ERel('a))" (infix "\<^bold>&" 99) where "(\<^bold>&) \<equiv> (\<inter>\<^sup>r)"
abbreviation(input) ll_lpmi::"EOp\<^sub>2(ERel('a))" (infix "\<^bold>\<circ>-" 99) where "(\<^bold>\<circ>-) \<equiv> (\<Zndres>\<^sup>r)"

(*The "multiplicative" binary connectives are interpreted with "Peircean" binary operations*)
abbreviation(input) ll_tensor::"EOp\<^sub>2(ERel('a))" (infixr "\<^bold>\<otimes>" 99) where "(\<^bold>\<otimes>) \<equiv> (;\<^sup>r)"
abbreviation(input) ll_par::"EOp\<^sub>2(ERel('a))" (infixl "\<^bold>\<section>" 99) where "(\<^bold>\<section>) \<equiv> (\<dagger>\<^sup>r)" (* \<section> as in par-agraph ;*)
abbreviation(input) ll_impl::"EOp\<^sub>2(ERel('a))" (infix "-\<^bold>\<circ>" 99) where "(-\<^bold>\<circ>) \<equiv> (\<Zrres>\<^sup>r)"

(*Exponentials are interpreted with special unary operations that give strong-identities and weak-differences*)
abbreviation(input) ll_ofcourse::"EOp(ERel('a))"  ("\<^bold>!_") where "\<^bold>!r \<equiv> r\<^sup>!"
abbreviation(input) ll_whynot::"EOp(ERel('a))"  ("\<^bold>?_") where "\<^bold>?r \<equiv> r\<^sup>?"

(*As with any logic, (cyclic) linear logic features three fundamental "speech acts":
(1) Asserting validity (or tautologicity)
(2) Asserting invalidity (or unsatisfiablility)
(3) Asserting entailment (or consequence)*)

(*Usual (structural) logics make those assertions in terms of sets of propositions. In contrast, so-called
 substructural logics aggregate propositions as sequences instead. Linear logics are substructural.

(1) Asserting validity of a sequence of propositions:  "\<turnstile> P\<^sub>1,...,P\<^sub>n" (prefix-turnstile notation)
(2) Asserting invalidity of a sequence of propositions: "P\<^sub>1,...,P\<^sub>n \<turnstile>" (suffix-turnstile notation)
(3) Asserting that a sequence of propositions A\<^sub>1,...,A\<^sub>n (assumptions or antecedent) entails another
    sequence C\<^sub>1,...,C\<^sub>n (conclusions or consequent): A\<^sub>1,...,A\<^sub>n \<turnstile> C\<^sub>1,...,C\<^sub>n (sequent-turnstile notation)

In fact, (1) and (2) can be encoded as special cases of (3), so we start with the latter. This is due
to the fact that the notion of entailment employed in linear logic is "degree-preserving" (aka. "local")*)

(* (3) Degree-preserving (local) entailment is encoded by using the subrelation ordering.*)
abbreviation(input) ll_entail  ("[_\<turnstile>_]") where "[A \<turnstile> B] \<equiv> A \<subseteq>\<^sup>r B"
(*We use connectives \<^bold>\<otimes> resp. \<^bold>\<section> as assumption resp. conclusion aggregators and add syntactic sugar*)
abbreviation(input) ll_entail12  ("[_\<turnstile>_,_]") where "[A \<turnstile> B,C] \<equiv> [A \<turnstile> B \<^bold>\<section> C]"
abbreviation(input) ll_entail21  ("[_,_\<turnstile>_]") where "[A,B \<turnstile> C] \<equiv> [A \<^bold>\<otimes> B \<turnstile> C]"
abbreviation(input) ll_entail22  ("[_,_\<turnstile>_,_]") where "[A,B \<turnstile> C,D] \<equiv> [A \<^bold>\<otimes> B \<turnstile> C \<^bold>\<section> D]"
abbreviation(input) ll_entail31  ("[_,_,_\<turnstile>_]") where "[A,B,C \<turnstile> D] \<equiv> [A \<^bold>\<otimes> B \<^bold>\<otimes> C \<turnstile> D]"
abbreviation(input) ll_entail13  ("[_\<turnstile>_,_,_]") where "[A \<turnstile> B,C,D] \<equiv> [A \<turnstile> B \<^bold>\<section> C \<^bold>\<section> D]"
(*...and so on*)

(* (1) Validity: a proposition is valid iff it is entailed by \<^bold>1 *)
abbreviation(input) ll_valid  ("[\<turnstile>_]") where "[\<turnstile> A] \<equiv> [\<^bold>1 \<turnstile> A]"
(*Semantically, this means that tautologies are interpreted by reflexive relations*)
lemma "[\<turnstile> A] = \<Q> \<subseteq>\<^sup>r A" by them
lemma "[\<turnstile> A] = reflexive A" by them

(* (2) Invalidity: a proposition is invalid iff it entails \<^bold>\<bottom> *)
abbreviation(input) ll_invalid  ("[_\<turnstile>]") where "[A \<turnstile>] \<equiv> [A \<turnstile> \<^bold>\<bottom>]"
(*Semantically, this means that inconsistencies are interpreted by irreflexive relations*)
lemma "[A \<turnstile>] = A \<subseteq>\<^sup>r \<D>" by them
lemma "[A \<turnstile>] = irreflexive A" by them

(* We add convenient syntactic sugar...*)
abbreviation(input) ll_valid2  ("[\<turnstile>_,_]") where "[\<turnstile> A,B] \<equiv> [\<turnstile> A \<^bold>\<section> B]"
abbreviation(input) ll_valid3  ("[\<turnstile>_,_,_]") where "[\<turnstile> A,B,C] \<equiv> [\<turnstile> A \<^bold>\<section> B \<^bold>\<section> C]"
abbreviation(input) ll_valid4  ("[\<turnstile>_,_,_,_]") where "[\<turnstile> A,B,C,D] \<equiv> [\<turnstile> A \<^bold>\<section> B \<^bold>\<section> C \<^bold>\<section> D]"
(*...and so on*)
abbreviation(input) ll_invalid2  ("[_,_\<turnstile>]") where "[A,B \<turnstile>] \<equiv> [A \<^bold>\<otimes> B \<turnstile>]"
abbreviation(input) ll_invalid3  ("[_,_,_\<turnstile>]") where "[A,B,C \<turnstile>] \<equiv> [A \<^bold>\<otimes> B \<^bold>\<otimes> C \<turnstile>]"
abbreviation(input) ll_invalid4  ("[_,_,_,_\<turnstile>]") where "[A,B,C,D \<turnstile>] \<equiv> [A \<^bold>\<otimes> B \<^bold>\<otimes> C \<^bold>\<otimes> D \<turnstile>]"
(*...and so on*)

(*Cyclic linear logic is strictly weaker than linear logic: exchange does not hold unrestrictedly*)
lemma "[\<turnstile> R, S] \<longrightarrow> [\<turnstile> S, R]" by them (*works because it is a cyclic rotation*)
lemma "[\<turnstile> R, S, T] \<longrightarrow> [\<turnstile> S, R, T]" nitpick[card 'a=2] oops (*counterexample*)
lemma "[\<turnstile> R, S, T] \<longrightarrow> [\<turnstile> R, T, S]" nitpick[card 'a=2] oops (*counterexample*)
lemma "[\<turnstile> R, S, T] \<longrightarrow> [\<turnstile> T, R, S]" by them (*only cyclic rotations allowed*)
lemma "[\<turnstile> R, S, T] \<longrightarrow> [\<turnstile> S, T, R]" by them (*only cyclic rotations allowed*)

(*Negation allows formulas to change sides in a sequent (but a in a particular order!)*)
lemma "[\<turnstile> A, B] \<longleftrightarrow> [A\<^sup>\<bottom> \<turnstile> B]" by them
lemma "[C \<turnstile> A, B] \<longleftrightarrow> [A\<^sup>\<bottom>, C \<turnstile> B]" by them
lemma "[C \<turnstile> A, B] \<longleftrightarrow> [C, B\<^sup>\<bottom> \<turnstile> A]" by them
lemma "[C \<turnstile> A, B] \<longleftrightarrow> [C, A\<^sup>\<bottom> \<turnstile> B]" nitpick oops (*countermodel: wrong order*)
lemma "[C \<turnstile> A, B] \<longleftrightarrow> [B\<^sup>\<bottom>, C \<turnstile> A]" nitpick oops (*countermodel: wrong order*)

(*The deduction metatheorem holds wrt -\<circ> (by taking into account the correct rotation) *)
lemma "[\<turnstile> R -\<^bold>\<circ> T] \<longleftrightarrow> [R \<turnstile> T]" by them
lemma "[A \<turnstile> R -\<^bold>\<circ> T] \<longleftrightarrow> [R, A \<turnstile> T]" by them
lemma "[A \<turnstile> R -\<^bold>\<circ> T] \<longleftrightarrow> [A, R \<turnstile> T]" nitpick oops (*counterexample: cyclicity must be respected*)

(*Excluded middle & ex contradictio*)
lemma "[\<turnstile> R, R\<^sup>\<bottom>]" by them
lemma "[R, R\<^sup>\<bottom> \<turnstile>]" by them

(*Resolution resp. cut*)
lemma "[\<turnstile> Q, R] \<longrightarrow> [\<turnstile> R\<^sup>\<bottom>, T] \<longrightarrow> [\<turnstile> Q, T]" by them
lemma "[\<turnstile> Q, R] \<longrightarrow> [\<turnstile> R -\<^bold>\<circ> T] \<longrightarrow> [\<turnstile> Q, T]" by them

(*Moreover, note that*)
lemma "([A \<turnstile> B] \<and> [B \<turnstile> A]) \<longleftrightarrow> (A = B)" by them
lemma "([\<turnstile> A -\<^bold>\<circ> B] \<and> [\<turnstile> B -\<^bold>\<circ> A]) \<longleftrightarrow> (A = B)" by them

(*The following well-known properties of exponentials hold, as expected *)
lemma "\<^bold>!A = \<^bold>!\<^bold>!A" by them
lemma "\<^bold>?A = \<^bold>?\<^bold>?A" by them
lemma "\<^bold>!\<^bold>\<top> = \<^bold>1" by them
lemma "\<^bold>?\<^bold>0 = \<^bold>\<bottom>" by them
lemma "\<^bold>!(A \<^bold>& B) = (\<^bold>!A) \<^bold>\<otimes> (\<^bold>!B)" by them
lemma "\<^bold>?(A \<^bold>\<oplus> B) = (\<^bold>?A) \<^bold>\<section> (\<^bold>?B)" by them

(*And we get counterexamples for these non-theorems, as expected*)
lemma "\<^bold>!(A \<^bold>\<otimes> B) = (\<^bold>!A) \<^bold>& (\<^bold>!B)" nitpick oops (*countermodel*)
lemma "\<^bold>?(A \<^bold>\<otimes> B) = (\<^bold>?A) \<^bold>& (\<^bold>?B)" nitpick oops (*countermodel*)
lemma "\<^bold>?(A \<^bold>\<section> B) = (\<^bold>?A) \<^bold>\<oplus> (\<^bold>?B)" nitpick oops (*countermodel*)
lemma "\<^bold>!(A \<^bold>\<section> B) = (\<^bold>!A) \<^bold>\<oplus> (\<^bold>!B)" nitpick oops (*countermodel*)

(*Weakening fails in the general case, as expected*)
lemma "[A \<turnstile> C] \<longrightarrow> [A, H \<turnstile> C]" nitpick oops (*countermodel*)
lemma "[A \<turnstile> C] \<longrightarrow> [H, A \<turnstile> C]" nitpick oops (*countermodel*)
(*Indeed it is recoverable via exponentials (in any order)*)
lemma "[A \<turnstile> C] \<longrightarrow> [A, \<^bold>!H \<turnstile> C]" by them
lemma "[A,B \<turnstile> C] \<longrightarrow> [A, B, \<^bold>!H \<turnstile> C]" by them
lemma "[A,B \<turnstile> C] \<longrightarrow> [A, \<^bold>!H, B \<turnstile> C]" by them

(*Contraction also fails in the general case but is recoverable via exponentials*)
lemma "[A, A \<turnstile> C] \<longrightarrow> [A \<turnstile> C]" nitpick oops (*countermodel*)
lemma "[\<^bold>!A, \<^bold>!A \<turnstile> C] \<longrightarrow> [\<^bold>!A \<turnstile> C]" by them
lemma "[A, A \<turnstile> C] \<longrightarrow> [\<^bold>!A \<turnstile> C]" by them (*TODO: check this*)

end
