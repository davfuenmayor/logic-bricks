theory entailment
  imports endorels spaces
begin

section \<open>Semantic Entailment and Validity\<close>

subsection \<open>Special case (for modal logicians & co.)\<close>

(*Modal logics model propositions as sets (of 'worlds') and are primarily concerned with 'validity' 
 of propositions. We encode below the set of valid (resp. unsatisfiable, satisfiable) propositions. *)
definition valid::"Set(Set('a))" ("\<Turnstile>_") 
  where "valid \<equiv> \<forall>"
definition satisfiable::"Set(Set('a))" ("\<Turnstile>\<^sup>s\<^sup>a\<^sup>t_")
  where "satisfiable \<equiv> \<exists>"
definition unsatisfiable::"Set(Set('a))" ("\<Turnstile>\<^sup>u\<^sup>n\<^sup>s\<^sup>a\<^sup>t_")
  where "unsatisfiable \<equiv> \<nexists>"

lemma "\<Turnstile> P = (\<forall>w. P w)" unfolding valid_def .. (* "true in all worlds" *)
lemma "\<Turnstile>\<^sup>s\<^sup>a\<^sup>t P = (\<exists>w. P w)" unfolding satisfiable_def .. (* "true in some world" *)
lemma "\<Turnstile>\<^sup>u\<^sup>n\<^sup>s\<^sup>a\<^sup>t P = (\<not>(\<exists>w. P w))" unfolding unsatisfiable_def empty_def .. (* "true in no world" *)

(*In modal logic, logical consequence/entailment usually comes in two flavours: "local" and "global".
 The local variant is the default one (i.e. the one employed in most sources). Semantically, it 
 corresponds to the subset relation (assumptions are aggregated using conjunction/intersection).*)
abbreviation(input) localEntailment::"ERel(Set('a))" ("[_ \<Turnstile> _]")
  where "[a \<Turnstile> c] \<equiv> a \<subseteq> c"

(*The global variant is sometimes discussed, mostly for theoretical purposes (e.g. in algebraic logic).*)
abbreviation(input) globalEntailment1::"Set('a) \<Rightarrow> Set('a) \<Rightarrow> o" ("[_ \<Turnstile>\<^sub>g _]") (*one premise*)
  where "[a \<Turnstile>\<^sub>g c] \<equiv> \<Turnstile> a \<rightarrow> \<Turnstile> c"
abbreviation(input) globalEntailment2::"Set('a) \<Rightarrow> Set('a) \<Rightarrow> Set('a) \<Rightarrow> o" ("[_,_ \<Turnstile>\<^sub>g _]") (*two premises*)
  where "[a\<^sub>1, a\<^sub>2 \<Turnstile>\<^sub>g c] \<equiv> \<Turnstile> a\<^sub>1 \<rightarrow> \<Turnstile> a\<^sub>2 \<rightarrow> \<Turnstile> c"
(*...and so on*)

(*Local entailment is stronger than global entailment*)
lemma "[a \<Turnstile> c] \<Longrightarrow> [a \<Turnstile>\<^sub>g c]" unfolding valid_def set_defs comb_defs by auto
lemma "[a \<Turnstile>\<^sub>g c] \<Longrightarrow> [a \<Turnstile> c]" nitpick oops (*countermodel*)

(*The "deduction meta-theorem" holds for local entailment only*)
lemma DMT: "(\<Turnstile> a \<Rightarrow> c) = [a \<Turnstile> c]" unfolding valid_def set_defs comb_defs ..
lemma "(\<Turnstile> a \<Rightarrow> c) = [a \<Turnstile>\<^sub>g c]" nitpick oops (*countermodel*)


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
  unfolding entailment_def set_defs comb_defs by (smt (z3))

(*It is worth noting that when the class of truth-sets TT is closed under arbitrary intersections 
(aka. "closure system") then entailment becomes a closure (aka. hull) operator. *)
lemma entailment_closure: "\<forall>X. X \<subseteq> TT \<longrightarrow> TT (\<Inter>X) \<Longrightarrow> CLOSURE (\<E> TT)" 
  unfolding entailment_def monotonic_def expansive_def idempotent_def 
  unfolding comb_defs apply auto 
  apply (smt (z3) B2_comb_def \<Phi>21_comb_def \<Phi>22_comb_def implR_def impl_def subrel_def2 subset_def)
  apply (simp add: B2_comb_def \<Phi>21_comb_def impl_def subset_def)
  unfolding set_defs comb_defs by fastforce

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
lemma ValueConsequence_closure: "CLOSURE (\<E>\<^sub>v T)" 
  unfolding valueEntailment_def monotonic_def expansive_def idempotent_def
  unfolding comb_defs apply auto 
  apply (simp add: B2_comb_def \<Phi>21_comb_def \<Phi>22_comb_def entailment_def implR_def impl_def subrel_def2 subset_def)
  apply (simp add: B2_comb_def \<Phi>21_comb_def entailment_def impl_def subset_def)
  unfolding entailment_def set_defs comb_defs by auto
  

(*Back to the general notion of entailment, now observe that it satisfies the following properties:*)
lemma entailment_prop1: "transitive R \<Longrightarrow> R-glb A m \<Longrightarrow> [range R | A \<Turnstile> c] = R m c" 
  unfolding entailment_def endorel_defs rel_defs func_defs set_defs comb_defs by metis
lemma entailment_prop2: "preorder R \<Longrightarrow> [range R | {a} \<Turnstile> c] = R a c"
  unfolding entailment_def endorel_defs rel_defs func_defs set_defs comb_defs by metis

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
lemma degreeEntailment_closure: "CLOSURE (\<E>\<^sub>d R)" 
  unfolding entailment_def degreeEntailment_def monotonic_def expansive_def idempotent_def
  unfolding rel_defs func_defs set_defs comb_defs apply simp by blast

(*It is worth mentioning that for semantics based on algebras of sets (e.g. modal algebras/Kripke models)
 the usual notion of logical consequence ("local consequence") corresponds to the "degree-preserving"
 entailment presented here, when instantiated with the subset relation.*)
lemma degreeEntailment_local: "[(\<subseteq>)| A \<Turnstile>\<^sub>d c] = \<Inter>A \<subseteq> c" 
  by (metis biginter_glb degreeEntailment_def2 partial_order_def2 subset_partial_order)

lemma "[(\<subseteq>)| A \<Turnstile>\<^sub>d c] = [\<Inter>A \<Turnstile> c]" unfolding degreeEntailment_local ..
lemma "[(\<subseteq>)| {a\<^sub>1, a\<^sub>2} \<Turnstile>\<^sub>d c] = [a\<^sub>1 \<inter> a\<^sub>2 \<Turnstile> c]" unfolding degreeEntailment_local unfolding set_defs comb_defs by blast

(*Similarly, the notion of "global consequence" (e.g. in modal logic) corresponds to "value-preserving"
 consequence instantiated with T = {\<UU>} where \<UU> is the universe of all points (or 'worlds').*)
lemma valueEntailment_global: "[{\<UU>}| A \<Turnstile>\<^sub>v c] = ((\<forall>a. A a \<longrightarrow> a = \<UU>) \<longrightarrow> c = \<UU>)" 
  unfolding valueEntailment_def2 valid_def set_defs comb_defs by blast

lemma "[{\<UU>}| {a\<^sub>1, a\<^sub>2} \<Turnstile>\<^sub>v c] = [a\<^sub>1, a\<^sub>2 \<Turnstile>\<^sub>g c]" 
  unfolding valueEntailment_global by (smt (z3) \<Phi>21_comb_def all_defQ union_def universe_def valid_def)

end