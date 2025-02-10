theory connectives_disequality
  imports base
begin

section \<open>Basic logical connectives (using primitive disequality)\<close>

(*Via negativa: disequality (notation: \<D>, infix \<noteq>) is all you can tell.*)

subsection \<open>Basic connectives\<close>

subsubsection \<open>Falsum\<close>
(* Since no function is non-self-identical, the following serves as definition of falsum/false *)
lemma false_defQ: "\<F> = \<D> \<D> \<D>" by simp 
lemma "\<F> = (\<D> \<noteq> \<D>)" by simp

subsubsection \<open>Identity (for booleans)\<close>
(* In fact, the identity function (for booleans) is also definable from disequality alone*)
lemma id_defQ: "\<^bold>I = \<D> \<F>" unfolding comb_defs by simp
lemma "\<^bold>I = \<D> (\<D> \<D> \<D>)" unfolding comb_defs by simp (*expanded*)

subsubsection \<open>Verum\<close>
(*Asserting that two different functions are different is a good way to encode verum*)
lemma true_defQ: "\<T> = \<D> \<^bold>I (\<^bold>K \<F>)" unfolding comb_defs by metis
lemma "\<T> = (\<^bold>I \<noteq> \<^bold>K \<F>)" unfolding comb_defs by metis
lemma "\<T> = \<D>(\<D>(\<D> \<D> \<D>))(\<^bold>K(\<D> \<D> \<D>))" unfolding comb_defs by metis (*expanded*)

subsubsection \<open>Negation\<close>
(*We can negate a proposition P by asserting that 'P is not true' (i.e. P is not equal to verum)*)
lemma not_defQ: "(\<not>) = \<D> \<T>" unfolding comb_defs by simp
lemma "(\<not>) = (\<lambda>P. P \<noteq> \<T>)" by simp
lemma "(\<not>) = \<D>(\<D>(\<D>(\<D> \<D> \<D>))(\<^bold>K(\<D> \<D> \<D>)))" unfolding comb_defs by metis (*expanded*)

subsubsection \<open>Equality\<close>
(*Using negation we can define equality for any type (not only boolean)*)
lemma eq_defQ: "\<Q> = (\<not>) \<circ>\<^sub>2 \<D>" unfolding comb_defs by simp
lemma "\<Q> = (\<lambda>A B. \<not>(A \<noteq> B))"  by simp

named_theorems eq_defs
declare false_defQ [eq_defs] id_defQ [eq_defs] 
        true_defQ [eq_defs] not_defQ [eq_defs] eq_defQ [eq_defs]

end