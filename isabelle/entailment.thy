theory entailment
  imports adj
begin

section \<open>Semantic Entailment and Validity\<close>

subsection \<open>Special case (for modal logicians & co.)\<close>

(*Modal logics model propositions as sets (of 'worlds') and are primarily concerned with 'validity' 
 of propositions. We encode below the set of valid (resp. unsatisfiable, satisfiable) propositions. *)
definition valid::"Set(Set('a))" ("\<Turnstile> _") 
  where "valid \<equiv> \<forall>"
definition satisfiable::"Set(Set('a))" ("\<Turnstile>\<^sup>s\<^sup>a\<^sup>t _")
  where "satisfiable \<equiv> \<exists>"
definition unsatisfiable::"Set(Set('a))" ("\<Turnstile>\<^sup>u\<^sup>n\<^sup>s\<^sup>a\<^sup>t _")
  where "unsatisfiable \<equiv> \<nexists>"

lemma "\<Turnstile> P = (\<forall>w. P w)" unfolding valid_def .. (* "true in all worlds" *)
lemma "\<Turnstile>\<^sup>s\<^sup>a\<^sup>t P = (\<exists>w. P w)" unfolding satisfiable_def .. (* "true in some world" *)
lemma "\<Turnstile>\<^sup>u\<^sup>n\<^sup>s\<^sup>a\<^sup>t P = (\<not>(\<exists>w. P w))" unfolding unsatisfiable_def empty_def .. (* "true in no world" *)

(*In modal logic, logical consequence/entailment usually comes in two flavours: "local" and "global".
 The local variant is the default one (i.e. the one employed in most sources). Semantically, it 
 corresponds to the subset relation (assumptions are aggregated using conjunction/intersection).*)
abbreviation(input) localEntailment::"ERel(Set('a))" (infixr "\<Turnstile>\<^sub>l" 99)                   
  where "a \<Turnstile>\<^sub>l c \<equiv> a \<subseteq> c"
abbreviation(input) localEntailment2::"Set('a) \<Rightarrow> ERel(Set('a))" ("_,_ \<Turnstile>\<^sub>l _") 
  where "a\<^sub>1, a\<^sub>2 \<Turnstile>\<^sub>l c \<equiv> (a\<^sub>1 \<inter> a\<^sub>2) \<Turnstile>\<^sub>l c"              (*syntax sugar for two (or more) premises*)
(*...and so on*)

(*Clearly, validity is a special case of local entailment *)
lemma "\<Turnstile> c \<leftrightarrow> \<UU> \<Turnstile>\<^sub>l c" unfolding valid_def func_defs comb_defs by simp

(*In fact, local entailment can also be stated in terms of validity via the so-called "deduction
 (meta-)theorem", which follows as a particular case of the following fact (aka. "residuation law") *)
lemma local_residuation: "(\<Turnstile>\<^sub>l),(\<Turnstile>\<^sub>l)-ADJ\<^sub>2 (\<inter>) (\<Rightarrow>)" by (simp add: adjunction_lift2 and_impl_adj impl_def inter_def subset_def)
(*or, in other words*)
lemma "a, b \<Turnstile>\<^sub>l c \<leftrightarrow> b \<Turnstile>\<^sub>l (a \<Rightarrow> c)" using local_residuation unfolding galois2_def relLiftAll_def comb_defs by (metis adjunction_def2)
(*which produces the "deduction meta-theorem" as a particular case (with b = \<UU>)*)
lemma DMT: "\<Turnstile> a \<Rightarrow> c \<leftrightarrow> a \<Turnstile>\<^sub>l c " by (simp add: B2_comb_def subset_setdef valid_def)

(*Global entailment is sometimes discussed, mostly for theoretical purposes (e.g. in algebraic logic).*)
abbreviation(input) globalEntailment::"Rel(Set(Set('a)),Set('a))" (infixr "\<Turnstile>\<^sub>g" 99)
  where "A \<Turnstile>\<^sub>g c \<equiv> (\<forall>a. A a \<rightarrow> \<Turnstile> a) \<rightarrow> \<Turnstile> c"

(*Again, validity is clearly a special case of global entailment *)
lemma "\<Turnstile> c \<leftrightarrow> {\<UU>} \<Turnstile>\<^sub>g c" by (simp add: K21_comb_def universe_def valid_def)

(*Local entailment is stronger than global entailment*)
lemma "a \<Turnstile>\<^sub>l c \<Longrightarrow> {a} \<Turnstile>\<^sub>g c" unfolding valid_def func_defs comb_defs by auto
lemma "a,b \<Turnstile>\<^sub>l c \<Longrightarrow> {a,b} \<Turnstile>\<^sub>g c" unfolding valid_def func_defs comb_defs by auto
lemma "{a} \<Turnstile>\<^sub>g c \<Longrightarrow> a \<Turnstile>\<^sub>l c" nitpick oops (*countermodel*)

(*The "deduction meta-theorem" does not hold for global entailment*)
lemma "{a} \<Turnstile>\<^sub>g c \<Longrightarrow> (\<Turnstile> a \<Rightarrow> c)" nitpick oops (*countermodel*)
lemma "{a,b} \<Turnstile>\<^sub>g c \<Longrightarrow> {b} \<Turnstile>\<^sub>g (a \<Rightarrow> c)" nitpick oops (*countermodel*)

(*Only this kind of 'detachment rule' holds*)
lemma "\<Turnstile> (a \<Rightarrow> c) \<Longrightarrow> {a} \<Turnstile>\<^sub>g c" unfolding valid_def func_defs comb_defs by auto
lemma "{b} \<Turnstile>\<^sub>g (a \<Rightarrow> c) \<Longrightarrow> {a,b} \<Turnstile>\<^sub>g c" unfolding valid_def func_defs comb_defs by auto


subsection \<open>General case (for algebraic & many-valued/fuzzy logicians)\<close>

(*We introduce an 'entailment' operation (for denotations) that corresponds to the semantic counterpart
 of the notion of consequence (for formulas). We refer to the literature on algebraic logic for detailed
 explanations, in particular to J.M. Font (2007) "On substructural logics preserving degrees of truth" 
 (https://www.researchgate.net/publication/265570835_On_substructural_logics_preserving_degrees_of_truth)
 for an overview, and references therein.*)

(*We encode below a general notion of logical entailment as discussed in the algebraic logic literature;
 cf. "ramified matrices" (e.g. Wojcicki 1970) and "generalized matrices" (e.g. Font 2007).
 Entailment becomes parameterized with a class TT of "truth-sets". We say that a set of assumptions
 A entails the conclusion c iff when all As are in T then c is in T too, for all truth-sets T in TT.*)
definition entailment::"Set(Set('a)) \<Rightarrow> SetEOp('a)" ("\<E>")
  where "\<E> TT \<equiv> \<lambda>A. \<lambda>c. \<forall>T. TT T \<longrightarrow> A \<subseteq> T \<longrightarrow> T c"

notation(input) entailment ("[_|_ \<Turnstile> _]")
lemma "[TT| A \<Turnstile> c] = \<E> TT A c" .. 

(*Alternative definition: c is in the intersection of all truth-sets containing A*)
lemma entailment_def2: "[TT| A \<Turnstile> c] =  \<Inter>(TT \<inter> (\<subseteq>) A) c"
  unfolding entailment_def func_defs comb_defs by (smt (z3))

(*It is worth noting that when the class of truth-sets TT is closed under arbitrary intersections 
(aka. "closure system") then entailment becomes a closure (aka. hull) operator. *)
lemma entailment_closure: "\<forall>X. X \<subseteq> TT \<longrightarrow> TT (\<Inter>X) \<Longrightarrow> (\<subseteq>)-CLOSURE (\<E> TT)" 
  unfolding entailment_def rel_defs func_defs comb_defs by blast

(*One special case of the definition above occurs when TT is a singleton {T}. This corresponds to the
 traditional notion of logical consequence associated to "logical matrices" in algebraic logic, and 
 which is characterized by the principle of truth(-value) preservation ("truth-preserving consequence"
 in Font 2007). We thus refer to its encoding below as "(truth-)value-preserving entailment".*)
definition valueEntailment::"Set('a) \<Rightarrow> SetEOp('a)" ("\<E>\<^sub>v")
  where "\<E>\<^sub>v T \<equiv> \<E> {T}"

notation(input) valueEntailment ("[_|_ \<Turnstile>\<^sub>v _]")
lemma "[T| A \<Turnstile>\<^sub>v c] = \<E>\<^sub>v T A c" ..

(*Alternative definition: if all As are in T (true) then c is also in T (true)*)
lemma valueEntailment_def2: "[T| A \<Turnstile>\<^sub>v c] = (A \<subseteq> T \<longrightarrow> T c)"
  unfolding entailment_def valueEntailment_def by simp

(*Value-preserving entailment is a closure operator too*)
lemma ValueConsequence_closure: "(\<subseteq>)-CLOSURE (\<E>\<^sub>v T)" 
  unfolding valueEntailment_def entailment_def rel_defs func_defs comb_defs by blast

(*Back to the general notion of entailment, now observe that it satisfies the following properties:*)
lemma entailment_prop1: "transitive R \<Longrightarrow> R-glb A m \<Longrightarrow> [range R | A \<Turnstile> c] = R m c" 
  unfolding entailment_def endorel_defs rel_defs func_defs comb_defs by blast
lemma entailment_prop2: "preorder R \<Longrightarrow> [range R | {a} \<Turnstile> c] = R a c"
  unfolding entailment_def endorel_defs rel_defs func_defs comb_defs by metis

(*The properties above justify the following special case, in which the class of truth-sets is 
 given as the (functional) range of a relation (qua set-valued function). 
 Following Font (2007) we speak of "(truth-)degree-preserving" entailment. *)
definition degreeEntailment::"ERel('a) \<Rightarrow> SetEOp('a)" ("\<E>\<^sub>d")
  where "\<E>\<^sub>d R \<equiv> \<E> (range R)"

notation(input) degreeEntailment ("[_|_ \<Turnstile>\<^sub>d _]")
lemma "[R| A \<Turnstile>\<^sub>d c] = \<E>\<^sub>d R A c" ..

(*Alternative definitions for transitive relations resp. preorders*)
lemma degreeEntailment_def2: "transitive R \<Longrightarrow> R-glb A h \<Longrightarrow> [R| A \<Turnstile>\<^sub>d c] = R h c" 
  unfolding degreeEntailment_def entailment_prop1 by (smt (z3))
lemma degreeEntailment_def3: "preorder R \<Longrightarrow> [R| {a} \<Turnstile>\<^sub>d c] = R a c"
  by (simp add: degreeEntailment_def entailment_prop2)

(*Degree-preserving entailment is a closure operator*)
lemma degreeEntailment_closure: "(\<subseteq>)-CLOSURE (\<E>\<^sub>d R)" 
  unfolding entailment_def degreeEntailment_def unfolding rel_defs func_defs comb_defs by blast

(*It is worth mentioning that for semantics based on algebras of sets (e.g. modal algebras/Kripke models)
 the usual notion of logical consequence ("local consequence") corresponds to the "degree-preserving"
 entailment presented here, when instantiated with the subset relation.*)
lemma degreeEntailment_local: "[(\<subseteq>)| A \<Turnstile>\<^sub>d c] = \<Inter>A \<Turnstile>\<^sub>l c" 
  by (metis biginter_glb degreeEntailment_def2 partial_order_def2 subset_partial_order)

(*Similarly, the notion of "global consequence" (e.g. in modal logic) corresponds to "value-preserving"
 consequence instantiated with T = {\<UU>} where \<UU> is the universe of all points (or 'worlds').*)
lemma valueEntailment_global: "[{\<UU>}| A \<Turnstile>\<^sub>v c] = A \<Turnstile>\<^sub>g c" 
  unfolding valueEntailment_def2 valid_def func_defs comb_defs by blast

end