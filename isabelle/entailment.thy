theory entailment
  imports adj
begin

section \<open>Semantic Entailment and Validity\<close>

subsection \<open>Special case (for modal logicians and co.)\<close>

text \<open>Modal logics model propositions as sets (of "worlds") and are primarily concerned with "validity" 
 of propositions. We encode below the set of valid (resp. unsatisfiable, satisfiable) propositions.\<close>
definition valid::"Set(Set('a))" ("\<Turnstile> _") 
  where "valid \<equiv> \<forall>"
definition satisfiable::"Set(Set('a))" ("\<Turnstile>\<^sup>s\<^sup>a\<^sup>t _")
  where "satisfiable \<equiv> \<exists>"
definition unsatisfiable::"Set(Set('a))" ("\<Turnstile>\<^sup>u\<^sup>n\<^sup>s\<^sup>a\<^sup>t _")
  where "unsatisfiable \<equiv> \<nexists>"

lemma "\<Turnstile> P = (\<forall>w. P w)" unfolding valid_def .. \<comment> \<open>"true in all worlds"\<close>
lemma "\<Turnstile>\<^sup>s\<^sup>a\<^sup>t P = (\<exists>w. P w)" unfolding satisfiable_def .. \<comment> \<open>"true in some world"\<close>
lemma "\<Turnstile>\<^sup>u\<^sup>n\<^sup>s\<^sup>a\<^sup>t P = (\<not>(\<exists>w. P w))" unfolding unsatisfiable_def empty_def .. \<comment> \<open>"true in no world"\<close>

text \<open>In modal logic, logical consequence/entailment usually comes in two flavours: "local" and "global".
 The local variant is the default one (i.e. the one employed in most sources). Semantically, it 
 corresponds to the subset relation (assumptions are aggregated using conjunction/intersection).\<close>
abbreviation(input) localEntailment::"ERel(Set('a))" (infixr "\<Turnstile>\<^sub>l" 99)                   
  where "a \<Turnstile>\<^sub>l c \<equiv> a \<subseteq> c"
abbreviation(input) localEntailment2::"Set('a) \<Rightarrow> ERel(Set('a))" ("_,_ \<Turnstile>\<^sub>l _") 
  where "a\<^sub>1, a\<^sub>2 \<Turnstile>\<^sub>l c \<equiv> (a\<^sub>1 \<inter> a\<^sub>2) \<Turnstile>\<^sub>l c"       \<comment> \<open>syntax sugar for two (or more) premises\<close>
\<comment> \<open>...and so on\<close>

text \<open>Clearly, validity is a special case of local entailment.\<close>
lemma "\<Turnstile> c \<leftrightarrow> \<UU> \<Turnstile>\<^sub>l c" unfolding valid_def func_defs comb_defs by simp

text \<open>In fact, local entailment can also be stated in terms of validity via the so-called "deduction
 (meta-)theorem", which follows as a particular case of the following fact (aka. "residuation law").\<close>
lemma local_residuation: "(\<Turnstile>\<^sub>l),(\<Turnstile>\<^sub>l)-ADJ\<^sub>2 (\<inter>) (\<Rightarrow>)" by (simp add: adjunction_lift2 and_impl_adj impl_def inter_def subset_def)
\<comment> \<open>or, in other words\<close>
lemma "a, b \<Turnstile>\<^sub>l c \<leftrightarrow> b \<Turnstile>\<^sub>l (a \<Rightarrow> c)" using local_residuation unfolding galois2_def relLiftAll_def comb_defs by (metis adjunction_def2)
text \<open>Which produces the "deduction meta-theorem" as a particular case (with b = \<open>\<UU>\<close>).\<close>
lemma DMT: "\<Turnstile> a \<Rightarrow> c \<leftrightarrow> a \<Turnstile>\<^sub>l c " by (simp add: B2_comb_def subset_setdef valid_def)

text \<open>Global entailment is sometimes discussed, mostly for theoretical purposes (e.g. in algebraic logic).\<close>
abbreviation(input) globalEntailment::"Rel(Set(Set('a)),Set('a))" (infixr "\<Turnstile>\<^sub>g" 99)
  where "A \<Turnstile>\<^sub>g c \<equiv> (\<forall>a. A a \<rightarrow> \<Turnstile> a) \<rightarrow> \<Turnstile> c"

text \<open>Again, validity is clearly a special case of global entailment.\<close>
lemma "\<Turnstile> c \<leftrightarrow> {\<UU>} \<Turnstile>\<^sub>g c" by (simp add: K21_comb_def universe_def valid_def)

text \<open>Local entailment is stronger than global entailment.\<close>
lemma "a \<Turnstile>\<^sub>l c \<Longrightarrow> {a} \<Turnstile>\<^sub>g c" unfolding valid_def func_defs comb_defs by auto
lemma "a,b \<Turnstile>\<^sub>l c \<Longrightarrow> {a,b} \<Turnstile>\<^sub>g c" unfolding valid_def func_defs comb_defs by auto
lemma "{a} \<Turnstile>\<^sub>g c \<Longrightarrow> a \<Turnstile>\<^sub>l c" nitpick oops \<comment> \<open>countermodel\<close>

text \<open>The "deduction meta-theorem" does not hold for global entailment.\<close>
lemma "{a} \<Turnstile>\<^sub>g c \<Longrightarrow> (\<Turnstile> a \<Rightarrow> c)" nitpick oops \<comment> \<open>countermodel\<close>
lemma "{a,b} \<Turnstile>\<^sub>g c \<Longrightarrow> {b} \<Turnstile>\<^sub>g (a \<Rightarrow> c)" nitpick oops \<comment> \<open>countermodel\<close>

\<comment> \<open>Only this kind of "detachment rule" holds.\<close>
lemma "\<Turnstile> (a \<Rightarrow> c) \<Longrightarrow> {a} \<Turnstile>\<^sub>g c" unfolding valid_def func_defs comb_defs by auto
lemma "{b} \<Turnstile>\<^sub>g (a \<Rightarrow> c) \<Longrightarrow> {a,b} \<Turnstile>\<^sub>g c" unfolding valid_def func_defs comb_defs by auto


subsection \<open>General case (for algebraic and many-valued/fuzzy logicians)\<close>

text \<open>We introduce an "entailment" operation (for denotations) that corresponds to the semantic counterpart
 of the notion of consequence (for formulas). We refer to the literature on algebraic logic for detailed
 explanations, in particular \<^cite>\<open>font2007\<close> for an overview, and references therein.\<close>

text \<open>We encode below a general notion of logical entailment as discussed in the algebraic logic literature;
 cf. "ramified matrices" (e.g. \<^cite>\<open>wojcicki1970\<close>) and "generalized matrices" (e.g. \<^cite>\<open>font2007\<close>).
 Entailment becomes parameterized with a class \<open>TT\<close> of "truth-sets". We say that a set of assumptions
 \<open>A\<close> entails the conclusion \<open>c\<close> iff when all \<open>A\<close>s are in \<open>T\<close> then \<open>c\<close> is in \<open>T\<close> too, for all truth-sets \<open>T\<close> in \<open>TT\<close>.\<close>
definition entailment::"Set(Set('a)) \<Rightarrow> SetEOp('a)" ("\<E>")
  where "\<E> TT \<equiv> \<lambda>A. \<lambda>c. \<forall>T. TT T \<longrightarrow> A \<subseteq> T \<longrightarrow> T c"

notation(input) entailment ("[_|_ \<Turnstile> _]")
lemma "[TT| A \<Turnstile> c] = \<E> TT A c" .. 

text \<open>Alternative definition: \<open>c\<close> is in the intersection of all truth-sets containing \<open>A\<close>\<close>
lemma entailment_def2: "[TT| A \<Turnstile> c] =  \<Inter>(TT \<inter> (\<subseteq>) A) c"
  unfolding entailment_def func_defs comb_defs by (smt (z3))

text \<open>It is worth noting that when the class of truth-sets \<comment> \<open>TT\<close> is closed under arbitrary intersections 
(aka. "closure system") then entailment becomes a closure (aka. hull) operator.\<close>
lemma entailment_closure: "\<forall>X. X \<subseteq> TT \<longrightarrow> TT (\<Inter>X) \<Longrightarrow> (\<subseteq>)-CLOSURE (\<E> TT)" 
  unfolding entailment_def rel_defs func_defs comb_defs by blast

text \<open>One special case of the definition above occurs when \<open>TT\<close> is a singleton \<open>{T}\<close>. This corresponds to
 the traditional notion of logical consequence associated to "logical matrices" in algebraic logic, and 
 which is characterized by the principle of truth(-value) preservation ("truth-preserving consequence"
 in \<^cite>\<open>font2007\<close>). We thus refer to its encoding below as "(truth-)value-preserving entailment".\<close>
definition valueEntailment::"Set('a) \<Rightarrow> SetEOp('a)" ("\<E>\<^sub>v")
  where "\<E>\<^sub>v T \<equiv> \<E> {T}"

notation(input) valueEntailment ("[_|_ \<Turnstile>\<^sub>v _]")
lemma "[T| A \<Turnstile>\<^sub>v c] = \<E>\<^sub>v T A c" ..

text \<open>Alternative definition: if all As are in T (true) then c is also in T (true).\<close>
lemma valueEntailment_def2: "[T| A \<Turnstile>\<^sub>v c] = (A \<subseteq> T \<longrightarrow> T c)"
  unfolding entailment_def valueEntailment_def by simp

text \<open>Value-preserving entailment is a closure operator too.\<close>
lemma ValueConsequence_closure: "(\<subseteq>)-CLOSURE (\<E>\<^sub>v T)" 
  unfolding valueEntailment_def entailment_def rel_defs func_defs comb_defs by blast

text \<open>Back to the general notion of entailment, now observe that it satisfies the following properties:\<close>
lemma entailment_prop1: "transitive R \<Longrightarrow> R-glb A m \<Longrightarrow> [range R | A \<Turnstile> c] = R m c" 
  unfolding entailment_def endorel_defs rel_defs func_defs comb_defs by blast
lemma entailment_prop2: "preorder R \<Longrightarrow> [range R | {a} \<Turnstile> c] = R a c"
  unfolding entailment_def endorel_defs rel_defs func_defs comb_defs by metis

text \<open>The properties above justify the following special case, in which the class of truth-sets is 
 given as the (functional) range of a relation (qua set-valued function). 
 Following \<^cite>\<open>font2007\<close> we speak of "(truth-)degree-preserving" entailment.\<close>
definition degreeEntailment::"ERel('a) \<Rightarrow> SetEOp('a)" ("\<E>\<^sub>d")
  where "\<E>\<^sub>d R \<equiv> \<E> (range R)"

notation(input) degreeEntailment ("[_|_ \<Turnstile>\<^sub>d _]")
lemma "[R| A \<Turnstile>\<^sub>d c] = \<E>\<^sub>d R A c" ..

text \<open>Alternative definitions for transitive relations resp. preorders.\<close>
lemma degreeEntailment_def2: "transitive R \<Longrightarrow> R-glb A h \<Longrightarrow> [R| A \<Turnstile>\<^sub>d c] = R h c" 
  unfolding degreeEntailment_def entailment_prop1 by (smt (z3))
lemma degreeEntailment_def3: "preorder R \<Longrightarrow> [R| {a} \<Turnstile>\<^sub>d c] = R a c"
  by (simp add: degreeEntailment_def entailment_prop2)

text \<open>Degree-preserving entailment is a closure operator.\<close>
lemma degreeEntailment_closure: "(\<subseteq>)-CLOSURE (\<E>\<^sub>d R)" 
  unfolding entailment_def degreeEntailment_def unfolding rel_defs func_defs comb_defs by blast

text \<open>It is worth mentioning that for semantics based on algebras of sets (e.g. modal algebras/Kripke models)
 the usual notion of logical consequence ("local consequence") corresponds to the "degree-preserving"
 entailment presented here, when instantiated with the subset relation.\<close>
lemma degreeEntailment_local: "[(\<subseteq>)| A \<Turnstile>\<^sub>d c] = \<Inter>A \<Turnstile>\<^sub>l c" 
  by (metis biginter_glb degreeEntailment_def2 partial_order_def2 subset_partial_order)

text \<open>Similarly, the notion of "global consequence" (e.g. in modal logic) corresponds to "value-preserving"
 consequence instantiated with \<open>T = {\<UU>}\<close> where \<open>\<UU>\<close> is the universe of all points (or "worlds").\<close>
lemma valueEntailment_global: "[{\<UU>}| A \<Turnstile>\<^sub>v c] = A \<Turnstile>\<^sub>g c" 
  unfolding valueEntailment_def2 valid_def func_defs comb_defs by blast

end