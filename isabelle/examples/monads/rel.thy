theory rel
imports env set
begin

section \<open>Relation Monad\<close>

text \<open>In fact, the \<open>Rel('a,'b)\<close> type constructor also comes with a monad structure, which merges, 
 in a sense, the environment monad with the set monad.\<close>

named_theorems all_defs
declare comb_defs[all_defs] func_defs[all_defs] rel_defs[all_defs]


subsection \<open>Functor\<close>

abbreviation(input) fmap0::"'a \<Rightarrow>  Rel('b,'a)"
  where "fmap0 \<equiv> env.fmap0 \<circ> set.fmap0"
abbreviation(input) fmap1::"('a \<Rightarrow> 'b) \<Rightarrow> Rel('c,'a) \<Rightarrow> Rel('c,'b)"
  where "fmap1 \<equiv> env.fmap1 \<circ> set.fmap1"
abbreviation(input) fmap2::"('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> (Rel('d,'a) \<Rightarrow> Rel('d,'b) \<Rightarrow> Rel('d,'c))"
  where "fmap2 \<equiv> env.fmap2 \<circ> set.fmap2"
abbreviation(input) fmap3::"('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> (Rel('e,'a) \<Rightarrow> Rel('e,'b) \<Rightarrow> Rel('e,'c) \<Rightarrow> Rel('e,'d))"
  where "fmap3 \<equiv> env.fmap3 \<circ> set.fmap3"
\<comment> \<open>...and so on\<close>

text \<open>Functor's "unit" (monad's "return" resp. applicative's "pure") corresponds to the nullary case.\<close>
abbreviation unit where "unit \<equiv> fmap0"
text \<open>Functor's classic "fmap" corresponds to the unary case.\<close>
abbreviation fmap where "fmap \<equiv> fmap1"


subsection \<open>Applicative\<close>

abbreviation(input) ap0::"Rel('b,'a) \<Rightarrow> Rel('b,'a)"
  where "ap0 \<equiv> fmap1 \<^bold>I" \<comment> \<open>ie. \<open>\<^bold>A\<close>\<close>
abbreviation(input) ap1::"Rel('c,'a \<Rightarrow> 'b) \<Rightarrow> Rel('c,'a) \<Rightarrow> Rel('c,'b)"
  where "ap1 \<equiv> fmap2 \<^bold>I"
abbreviation(input) ap2::"Rel('d,'a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> (Rel('d,'a) \<Rightarrow> Rel('d,'b) \<Rightarrow> Rel('d,'c))"
  where "ap2 \<equiv> fmap3 \<^bold>I"
\<comment> \<open>...and so on\<close>

text \<open>Applicative's classic "ap" corresponds to the unary case.\<close>
notation ap1 ("ap")
abbreviation(input) apr :: "Rel('c,'a) \<Rightarrow> Rel('c,'a \<Rightarrow> 'b) \<Rightarrow> Rel('c,'b)"(infixl "\<ggreater>" 54)
  where "a \<ggreater> f \<equiv> ap f a"  \<comment> \<open>convenient "pipeline notation"\<close>

text \<open>Indeed, we have:\<close>
lemma "ap0 = \<^bold>A" unfolding all_defs by simp
lemma "ap1 =  \<^bold>\<Phi>\<^sub>2\<^sub>1 set.ap" unfolding all_defs ..
lemma "ap2 =  \<^bold>\<Phi>\<^sub>3\<^sub>1 set.ap2" unfolding all_defs ..
\<comment> \<open>...and so on\<close>

text \<open>Check that applicative operations satisfy the corresponding laws.\<close>
lemma applicative_unit1: "x = x \<ggreater> (unit \<^bold>I)" unfolding all_defs by simp
lemma applicative_unit2: "(unit x) \<ggreater> (unit f) = unit (f x)" unfolding all_defs by simp
lemma applicative_unit3: "apr (unit x) f = apr f (unit (\<^bold>T x))" unfolding all_defs by simp
lemma applicative_assoc: "apr (apr w v) u = apr w (apr v (apr u (unit \<^bold>B)))" unfolding all_defs by fast


subsection \<open>Monad\<close>

abbreviation(input) bindr1::"('a \<Rightarrow> Rel('c,'b)) \<Rightarrow> Rel('c,'a) \<Rightarrow> Rel('c,'b)" (*TODO: extend for higher arities*)
  where "bindr1 \<equiv> (\<^bold>\<Phi>\<^sub>2\<^sub>1 set.bindr1) \<circ> \<^bold>C" \<comment> \<open>bind-reversed\<close>
\<comment> \<open>...and so on\<close>

text \<open>We have\<close>
lemma "bindr1 = \<^bold>B (\<^bold>C\<^bold>B\<^bold>C) \<^bold>\<Phi>\<^sub>2\<^sub>1 set.bindr" unfolding all_defs by metis

text \<open>Monad's usual "bind" corresponds to the (reversed) unary case, and gets its customary notation.\<close>
abbreviation bindr where "bindr \<equiv> bindr1"
abbreviation(input) bind::"Rel('c,'a) \<Rightarrow> ('a \<Rightarrow> Rel('c,'b)) \<Rightarrow> Rel('c,'b)" (infixl "\<bind>" 54)
  where "a \<bind> f \<equiv> bindr f a"

text \<open>fmap can be stated in terms of (reversed) bind and unit...\<close>
lemma "fmap = (bindr \<circ>\<^sub>2 \<^bold>B) unit" unfolding all_defs ..
text \<open>... and ap in terms of bind and fmap\<close>
lemma "ap = \<^bold>B\<^sub>1\<^sub>1 bind \<^bold>I (\<^bold>C fmap)" unfolding all_defs by blast

text \<open>The so-called "monad laws". They guarantee that term operations compose reliably.\<close>
lemma monad_unit1: "(unit x \<bind> f) = f x" unfolding all_defs by simp  \<comment> \<open>left identity\<close>
lemma monad_unit2: "(x \<bind> unit) = x" unfolding all_defs by simp      \<comment> \<open>right identity\<close>
lemma monad_assoc: "(bind (bind x f) g) = (bind x (\<lambda>z. bind (f z) g))" unfolding all_defs by auto \<comment> \<open>associativity\<close>


abbreviation(input) join::"Rel('c,Rel('c,'a)) \<Rightarrow> Rel('c,'a)"
  where "join \<equiv> \<^bold>W \<circ> (\<^bold>B \<Union>\<^sup>r)"

text \<open>Recalling that\<close>
lemma "join = bindr \<^bold>I" unfolding all_defs by metis

text \<open>We extrapolate to obtain some interesting interrelations, for different arities\<close>
lemma "join \<circ> ap0 = bindr1 \<^bold>I"  unfolding all_defs by metis
(* lemma "join \<circ>\<^sub>2 ap1 = bindr2 \<^bold>I" unfolding all_defs by metis *)
(* lemma "join \<circ>\<^sub>3 ap2 = bindr3 \<^bold>I" unfolding all_defs by metis *)

text \<open>Similarly, we can define bindr in terms of join and fmap, for different arities\<close>
lemma "bindr  = join \<circ>\<^sub>2 fmap"  unfolding all_defs by metis
lemma "bindr1 = join \<circ>\<^sub>2 fmap1" unfolding all_defs by metis
(* lemma "bindr2 = join \<circ>\<^sub>3 fmap2" unfolding all_defs by metis *)
(* lemma "bindr3 = join \<circ>\<^sub>4 fmap3" unfolding all_defs by metis *)

text \<open>Moreover, recalling that\<close>
lemma "ap F A = join (fmap (\<lambda>f. fmap f A) F)" unfolding all_defs by blast 

text \<open>We can extrapolate to define ap in terms of join and fmap\<close> (*TODO: for different arities*)
lemma "ap1 = join \<circ>\<^sub>2 ((\<^bold>C \<circ>\<^sub>2 (;) \<circ> \<^bold>C) fmap fmap)" unfolding all_defs by blast

(* TODO *)
subsection \<open>Pipelines\<close>

end