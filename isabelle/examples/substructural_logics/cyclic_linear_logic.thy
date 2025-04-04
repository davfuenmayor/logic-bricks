section \<open>Cyclic Linear Logic\<close>
text \<open>This is an example shallow encoding of an object-logical system using the library.\<close>

theory linear_logic
imports "../../operators" "../../entailment" "HOL-Eisbach.Eisbach"
begin

text \<open>We start by implementing a custom prover for this theory (called "them" for "theory-method").
Current implementation is very brute! It consists of mindless definition-unfolding followed by
 invocation of ground HOL-provers (extensionality is applied in between, if no success at first).
 A decent implementation shall unfold definitions gradually and call custom methods at each layer.\<close>
method skip = (tactic \<open>all_tac\<close>)
method them = (unfold endorel_defs rel_defs func_defs comb_defs) ;
              (auto | metis | smt) ; ((rule ext)+ | skip) ; (auto | metis | smt)


subsection \<open>Recap from the Theory of Relations\<close>

text \<open>Literature on relational algebra informally classifies relational connectives into two groups:
 a so-called "Boolean" (aka. additive) and a "Peircean" (aka. multiplicative) structure.
 When seen as set-valued functions, we can see that the former is in fact inherited from sets, while
 the latter comes from their generalized (i.e. partial and non-deterministic) functional structure.\<close>

text \<open>Remember that these relational binary operations (composition and its dual) are associative.\<close>
lemma "A ;\<^sup>r (B ;\<^sup>r C) = (A ;\<^sup>r B) ;\<^sup>r C" by them
lemma "A \<dagger>\<^sup>r (B \<dagger>\<^sup>r C) = (A \<dagger>\<^sup>r B) \<dagger>\<^sup>r C" by them

text \<open>Also note that the operation of cotransposition can act as a negation wrt. some relational operations.\<close>
lemma "R\<^sup>\<sim>\<^sup>\<sim> = R" by them     \<comment> \<open>involutivity: double-negation\<close>
lemma "\<UU>\<^sup>r\<^sup>\<sim> = \<emptyset>\<^sup>r" by them    \<comment> \<open>swapping top and bottom\<close>
lemma "\<Q>\<^sup>\<sim> = \<D>" by them     \<comment> \<open>swapping identity and anti-identity (difference)\<close>

text \<open>Cotransposition validates De Morgan laws wrt union and intersection.\<close>
lemma "(R \<inter>\<^sup>r S)\<^sup>\<sim> = (R\<^sup>\<sim>) \<union>\<^sup>r (S\<^sup>\<sim>)" by them
lemma "(R \<union>\<^sup>r S)\<^sup>\<sim> = (R\<^sup>\<sim>) \<inter>\<^sup>r (S\<^sup>\<sim>)" by them

text \<open>Cotransposition validates "flipped" De Morgan-like laws wrt composition and its dual.\<close>
lemma "(R ;\<^sup>r S)\<^sup>\<sim> = (S\<^sup>\<sim>) \<dagger>\<^sup>r (R\<^sup>\<sim>)" by them
lemma "(R \<dagger>\<^sup>r S)\<^sup>\<sim> = (S\<^sup>\<sim>) ;\<^sup>r (R\<^sup>\<sim>)" by them

text \<open>Cotransposition also acts as a negation wrt residuals.\<close>
lemma "(A \<Zrres>\<^sup>r B)\<^sup>\<sim> = (A \<circ>\<^sup>r (B\<^sup>\<sim>))" by them
lemma "(A \<Znrres>\<^sup>r B)\<^sup>\<sim> = (A ;\<^sup>r (B\<^sup>\<sim>))" by them

text \<open>The strong-identity-interior and weak-difference-closure operators are dual wrt. cotransposition.\<close>
lemma "R\<^sup>!\<^sup>\<sim> = R\<^sup>\<sim>\<^sup>?" by them
lemma "R\<^sup>?\<^sup>\<sim> = R\<^sup>\<sim>\<^sup>!" by them

text \<open>Cotransposition validates "excluded middle" and "ex contradictio" with \<open>\<Q>\<close> resp. \<open>\<D>\<close> as top resp. bottom.\<close>
lemma "\<Q> \<subseteq>\<^sup>r (R \<dagger>\<^sup>r (R\<^sup>\<sim>))" by them
lemma "(R ;\<^sup>r (R\<^sup>\<sim>)) \<subseteq>\<^sup>r \<D>" by them


subsection \<open>Cyclic Linear Logic\<close>

text \<open>We show how relations can interpret a non-commutative, cyclic variant of linear logic \<^cite>\<open>Desharnais1997\<close>.
 If modal logic can be said to adopt the "propositions as sets (of states)" paradigm. The present
 encoding can be paraphrased as "propositions as relations (on states)". Understanding propositions
 as sets of transitions between states offers an enriching dynamic perspective.\<close>

text \<open>Nullary connectives are interpreted as relational constants.\<close>
abbreviation(input) ll_one::"ERel('a)"  ("\<^bold>1") where  "\<^bold>1 \<equiv> \<Q>"
abbreviation(input) ll_bot::"ERel('a)"  ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<D>"
abbreviation(input) ll_zero::"ERel('a)" ("\<^bold>0") where  "\<^bold>0 \<equiv> \<emptyset>\<^sup>r"
abbreviation(input) ll_top::"ERel('a)"  ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<UU>\<^sup>r"

text \<open>Negation is interpreted as relational cotransposition (the transposition/converse of the complement).\<close>
abbreviation(input) ll_neg::"EOp(ERel('a))"  ("(_)\<^sup>\<bottom>") where "r\<^sup>\<bottom> \<equiv> r\<^sup>\<sim>"

text \<open>The "additive" binary connectives are interpreted with "Boolean" binary operations.\<close>
abbreviation(input) ll_plus::"EOp\<^sub>2(ERel('a))" (infix "\<^bold>\<oplus>" 99) where "(\<^bold>\<oplus>) \<equiv> (\<union>\<^sup>r)"
abbreviation(input) ll_with::"EOp\<^sub>2(ERel('a))" (infix "\<^bold>&" 99) where "(\<^bold>&) \<equiv> (\<inter>\<^sup>r)"
abbreviation(input) ll_lpmi::"EOp\<^sub>2(ERel('a))" (infix "\<^bold>\<circ>-" 99) where "(\<^bold>\<circ>-) \<equiv> (\<Zndres>\<^sup>r)"

text \<open>The "multiplicative" binary connectives are interpreted with "Peircean" binary operations.\<close>
abbreviation(input) ll_tensor::"EOp\<^sub>2(ERel('a))" (infixr "\<^bold>\<otimes>" 99) where "(\<^bold>\<otimes>) \<equiv> (;\<^sup>r)"
abbreviation(input) ll_par::"EOp\<^sub>2(ERel('a))" (infixl "\<^bold>\<section>" 99) where "(\<^bold>\<section>) \<equiv> (\<dagger>\<^sup>r)" (* \<section> as in par-agraph ;*)
abbreviation(input) ll_impl::"EOp\<^sub>2(ERel('a))" (infix "-\<^bold>\<circ>" 99) where "(-\<^bold>\<circ>) \<equiv> (\<Zrres>\<^sup>r)"

text \<open>Exponentials are interpreted with special unary operations that give strong-identities and weak-differences.\<close>
abbreviation(input) ll_ofcourse::"EOp(ERel('a))"  ("\<^bold>!_") where "\<^bold>!r \<equiv> r\<^sup>!"
abbreviation(input) ll_whynot::"EOp(ERel('a))"  ("\<^bold>?_") where "\<^bold>?r \<equiv> r\<^sup>?"

text \<open>As with any logic, (cyclic) linear logic features three fundamental "speech acts":
  \<^enum> Asserting validity (or tautologicity)
  \<^enum> Asserting invalidity (or unsatisfiablility)
  \<^enum> Asserting entailment (or consequence)\<close>

text \<open>Usual (structural) logics make those assertions in terms of sets of propositions. In contrast, so-called
 substructural logics aggregate propositions as sequences instead. Linear logics are substructural.

  \<^enum> Asserting validity of a sequence of propositions:  \<open>\<turnstile> P\<^sub>1,...,P\<^sub>n\<close> (prefix-turnstile notation)
  \<^enum> Asserting invalidity of a sequence of propositions: \<open>P\<^sub>1,...,P\<^sub>n \<turnstile>\<close> (suffix-turnstile notation)
  \<^enum> Asserting that a sequence of propositions \<open>A\<^sub>1,...,A\<^sub>n\<close> (assumptions or antecedent) entails another
    sequence \<open>C\<^sub>1,...,C\<^sub>n\<close> (conclusions or consequent): \<open>A\<^sub>1,...,A\<^sub>n \<turnstile> C\<^sub>1,...,C\<^sub>n\<close> (sequent-turnstile notation)

In fact, the first two can be encoded as special cases of the third, so we start with the latter. This is due
to the fact that the notion of entailment employed in linear logic is "degree-preserving" (aka. "local")\<close>

text \<open>Degree-preserving (local) entailment is encoded by using the subrelation ordering.\<close>
abbreviation(input) ll_entail  ("[_\<turnstile>_]") where "[A \<turnstile> B] \<equiv> A \<subseteq>\<^sup>r B"

text \<open>We use connectives \<open>\<^bold>\<otimes>\<close> resp. \<open>\<^bold>\<section>\<close> as assumption resp. conclusion aggregators and add syntactic sugar.\<close>
abbreviation(input) ll_entail12  ("[_\<turnstile>_,_]") where "[A \<turnstile> B,C] \<equiv> [A \<turnstile> B \<^bold>\<section> C]"
abbreviation(input) ll_entail21  ("[_,_\<turnstile>_]") where "[A,B \<turnstile> C] \<equiv> [A \<^bold>\<otimes> B \<turnstile> C]"
abbreviation(input) ll_entail22  ("[_,_\<turnstile>_,_]") where "[A,B \<turnstile> C,D] \<equiv> [A \<^bold>\<otimes> B \<turnstile> C \<^bold>\<section> D]"
abbreviation(input) ll_entail31  ("[_,_,_\<turnstile>_]") where "[A,B,C \<turnstile> D] \<equiv> [A \<^bold>\<otimes> B \<^bold>\<otimes> C \<turnstile> D]"
abbreviation(input) ll_entail13  ("[_\<turnstile>_,_,_]") where "[A \<turnstile> B,C,D] \<equiv> [A \<turnstile> B \<^bold>\<section> C \<^bold>\<section> D]"
\<comment> \<open>...and so on\<close>

text \<open>Validity: a proposition is valid iff it is entailed by \<open>\<^bold>1\<close>\<close>
abbreviation(input) ll_valid  ("[\<turnstile>_]") where "[\<turnstile> A] \<equiv> [\<^bold>1 \<turnstile> A]"

text \<open>Semantically, this means that tautologies are interpreted by reflexive relations.\<close>
lemma "[\<turnstile> A] = \<Q> \<subseteq>\<^sup>r A" by them
lemma "[\<turnstile> A] = reflexive A" by them

text \<open>Invalidity: a proposition is invalid iff it entails \<open>\<^bold>\<bottom>\<close>\<close>
abbreviation(input) ll_invalid  ("[_\<turnstile>]") where "[A \<turnstile>] \<equiv> [A \<turnstile> \<^bold>\<bottom>]"

text \<open>Semantically, this means that inconsistencies are interpreted by irreflexive relations.\<close>
lemma "[A \<turnstile>] = A \<subseteq>\<^sup>r \<D>" by them
lemma "[A \<turnstile>] = irreflexive A" by them

text \<open>We add convenient syntactic sugar:\<close>
abbreviation(input) ll_valid2  ("[\<turnstile>_,_]") where "[\<turnstile> A,B] \<equiv> [\<turnstile> A \<^bold>\<section> B]"
abbreviation(input) ll_valid3  ("[\<turnstile>_,_,_]") where "[\<turnstile> A,B,C] \<equiv> [\<turnstile> A \<^bold>\<section> B \<^bold>\<section> C]"
abbreviation(input) ll_valid4  ("[\<turnstile>_,_,_,_]") where "[\<turnstile> A,B,C,D] \<equiv> [\<turnstile> A \<^bold>\<section> B \<^bold>\<section> C \<^bold>\<section> D]"
\<comment> \<open>...and so on\<close>
abbreviation(input) ll_invalid2  ("[_,_\<turnstile>]") where "[A,B \<turnstile>] \<equiv> [A \<^bold>\<otimes> B \<turnstile>]"
abbreviation(input) ll_invalid3  ("[_,_,_\<turnstile>]") where "[A,B,C \<turnstile>] \<equiv> [A \<^bold>\<otimes> B \<^bold>\<otimes> C \<turnstile>]"
abbreviation(input) ll_invalid4  ("[_,_,_,_\<turnstile>]") where "[A,B,C,D \<turnstile>] \<equiv> [A \<^bold>\<otimes> B \<^bold>\<otimes> C \<^bold>\<otimes> D \<turnstile>]"
\<comment> \<open>...and so on\<close>

text \<open>Cyclic linear logic is strictly weaker than linear logic: exchange does not hold unrestrictedly.\<close>
lemma "[\<turnstile> R, S] \<longrightarrow> [\<turnstile> S, R]" by them \<comment> \<open>works because it is a cyclic rotation\<close>
proposition "[\<turnstile> R, S, T] \<longrightarrow> [\<turnstile> S, R, T]" nitpick[card 'a=2]  \<comment> \<open>countermodel found\<close> oops
proposition "[\<turnstile> R, S, T] \<longrightarrow> [\<turnstile> R, T, S]" nitpick[card 'a=2]  \<comment> \<open>countermodel found\<close> oops
lemma "[\<turnstile> R, S, T] \<longrightarrow> [\<turnstile> T, R, S]" by them  \<comment> \<open>only cyclic rotations allowed\<close>
lemma "[\<turnstile> R, S, T] \<longrightarrow> [\<turnstile> S, T, R]" by them  \<comment> \<open>only cyclic rotations allowed\<close>

text \<open>Negation allows formulas to change sides in a sequent (but a in a particular order!).\<close>
lemma "[\<turnstile> A, B] \<longleftrightarrow> [A\<^sup>\<bottom> \<turnstile> B]" by them
lemma "[C \<turnstile> A, B] \<longleftrightarrow> [A\<^sup>\<bottom>, C \<turnstile> B]" by them
lemma "[C \<turnstile> A, B] \<longleftrightarrow> [C, B\<^sup>\<bottom> \<turnstile> A]" by them
proposition "[C \<turnstile> A, B] \<longleftrightarrow> [C, A\<^sup>\<bottom> \<turnstile> B]" nitpick \<comment> \<open>countermodel found: wrong order\<close> oops
proposition "[C \<turnstile> A, B] \<longleftrightarrow> [B\<^sup>\<bottom>, C \<turnstile> A]" nitpick \<comment> \<open>countermodel found: wrong order\<close> oops

text \<open>The deduction metatheorem holds wrt \<open>-\<circ>\<close> (by taking into account the correct rotation).\<close>
lemma "[\<turnstile> R -\<^bold>\<circ> T] \<longleftrightarrow> [R \<turnstile> T]" by them
lemma "[A \<turnstile> R -\<^bold>\<circ> T] \<longleftrightarrow> [R, A \<turnstile> T]" by them
proposition "[A \<turnstile> R -\<^bold>\<circ> T] \<longleftrightarrow> [A, R \<turnstile> T]" nitpick \<comment> \<open>counterexample: cyclicity must be respected\<close> oops

text \<open>Excluded middle and ex contradictio.\<close>
lemma "[\<turnstile> R, R\<^sup>\<bottom>]" by them
lemma "[R, R\<^sup>\<bottom> \<turnstile>]" by them

text \<open>Resolution resp. cut.\<close>
lemma "[\<turnstile> Q, R] \<longrightarrow> [\<turnstile> R\<^sup>\<bottom>, T] \<longrightarrow> [\<turnstile> Q, T]" by them
lemma "[\<turnstile> Q, R] \<longrightarrow> [\<turnstile> R -\<^bold>\<circ> T] \<longrightarrow> [\<turnstile> Q, T]" by them

text \<open>Moreover, note that.\<close>
lemma "([A \<turnstile> B] \<and> [B \<turnstile> A]) \<longleftrightarrow> (A = B)" by them
lemma "([\<turnstile> A -\<^bold>\<circ> B] \<and> [\<turnstile> B -\<^bold>\<circ> A]) \<longleftrightarrow> (A = B)" by them

text \<open>The following well-known properties of exponentials hold, as expected.\<close>
lemma "\<^bold>!A = \<^bold>!\<^bold>!A" by them
lemma "\<^bold>?A = \<^bold>?\<^bold>?A" by them
lemma "\<^bold>!\<^bold>\<top> = \<^bold>1" by them
lemma "\<^bold>?\<^bold>0 = \<^bold>\<bottom>" by them
lemma "\<^bold>!(A \<^bold>& B) = (\<^bold>!A) \<^bold>\<otimes> (\<^bold>!B)" by them
lemma "\<^bold>?(A \<^bold>\<oplus> B) = (\<^bold>?A) \<^bold>\<section> (\<^bold>?B)" by them

text \<open>And we get counterexamples for these non-theorems, as expected:\<close>
proposition "\<^bold>!(A \<^bold>\<otimes> B) = (\<^bold>!A) \<^bold>& (\<^bold>!B)" nitpick \<comment> \<open>countermodel found\<close> oops
proposition "\<^bold>?(A \<^bold>\<otimes> B) = (\<^bold>?A) \<^bold>& (\<^bold>?B)" nitpick \<comment> \<open>countermodel found\<close> oops
proposition "\<^bold>?(A \<^bold>\<section> B) = (\<^bold>?A) \<^bold>\<oplus> (\<^bold>?B)" nitpick \<comment> \<open>countermodel found\<close> oops
proposition "\<^bold>!(A \<^bold>\<section> B) = (\<^bold>!A) \<^bold>\<oplus> (\<^bold>!B)" nitpick \<comment> \<open>countermodel found\<close> oops

text \<open>Weakening fails in the general case, as expected:\<close>
proposition "[A \<turnstile> C] \<longrightarrow> [A, H \<turnstile> C]" nitpick \<comment> \<open>countermodel found\<close> oops
proposition "[A \<turnstile> C] \<longrightarrow> [H, A \<turnstile> C]" nitpick \<comment> \<open>countermodel found\<close> oops

text \<open>Indeed weakening is recoverable via exponentials (in any order)\<close>
lemma "[A \<turnstile> C] \<longrightarrow> [A, \<^bold>!H \<turnstile> C]" by them
lemma "[A,B \<turnstile> C] \<longrightarrow> [A, B, \<^bold>!H \<turnstile> C]" by them
lemma "[A,B \<turnstile> C] \<longrightarrow> [A, \<^bold>!H, B \<turnstile> C]" by them

text \<open>Contraction also fails in the general case but is recoverable via exponentials.\<close>
proposition "[A, A \<turnstile> C] \<longrightarrow> [A \<turnstile> C]" nitpick \<comment> \<open>countermodel found\<close> oops
lemma "[\<^bold>!A, \<^bold>!A \<turnstile> C] \<longrightarrow> [\<^bold>!A \<turnstile> C]" by them
lemma "[A, A \<turnstile> C] \<longrightarrow> [\<^bold>!A \<turnstile> C]" by them (*TODO: check this*)

end
