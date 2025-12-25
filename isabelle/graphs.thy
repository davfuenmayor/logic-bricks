section \<open>Graphs\<close>

text \<open>Graphs are sets of endopairs and end up being isomorphic to endorelations (via currying).
 We replicate some of the theory of endorelations for illustration (exploiting currying).\<close>

theory graphs (* A basic theory of graphs (as sets of pairs and isomorphic to endorelations) *)
imports pairs endorelations
begin

subsection \<open>Intervals and Powers\<close>

subsubsection \<open>Intervals\<close>

text \<open>An interval (wrt. given graph G) is the set of points that lie between given pair (of "boundaries").\<close>
abbreviation interval::"Graph('a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> Set('a)" ("_-interval")
  where "G-interval a b \<equiv> \<lfloor>G\<rfloor>-interval a b "

lemma "G-interval a b = (\<lambda>c. G <a,c> \<and> G <c,b>)" 
  unfolding endorel_defs rel_defs func_defs comb_defs curry_def by auto


subsection \<open>Properties and Operations\<close>
text \<open>Properties of endorelations can be seamlessly transported to the world of graphs via currying.\<close>

subsubsection \<open>Reflexivity and Irreflexivity\<close>

abbreviation reflexive::"Set(Graph('a))"
  where \<open>reflexive G  \<equiv> endorelations.reflexive \<lfloor>G\<rfloor>\<close>
abbreviation irreflexive::"Set(Graph('a))"
  where \<open>irreflexive G \<equiv> endorelations.irreflexive \<lfloor>G\<rfloor>\<close>

lemma "reflexive G = (\<forall>x. G <x,x>)"
  by (simp add: B1_comb_def B2_comb_def C21_comb_def W21_comb_def curry_def reflexive_def2)

text \<open>...and so on\<close>


subsubsection \<open>Symmetry, Connectedness, and co.\<close>

abbreviation symmetric::"Set(Graph('a))"
  where \<open>symmetric G  \<equiv> endorelations.symmetric \<lfloor>G\<rfloor>\<close>
abbreviation connected::"Set(Graph('a))"
  where \<open>connected G \<equiv> endorelations.connected \<lfloor>G\<rfloor>\<close>

lemma "symmetric G = (\<forall>a b. G <a,b> \<rightarrow> G <b,a>)" 
  unfolding endorel_defs rel_defs func_defs comb_defs unfolding pair_defs comb_defs by metis
lemma "connected G = (\<forall>a b. G <a,b> \<or> G <b,a>)" 
 unfolding endorel_defs rel_defs func_defs comb_defs unfolding pair_defs comb_defs by metis

text \<open>...and so on\<close>


subsubsection \<open>Transitivity, Denseness, Quasitransitivity, and co.\<close>

abbreviation transitive::"Set(Graph('a))"
  where \<open>transitive G  \<equiv> endorelations.transitive \<lfloor>G\<rfloor>\<close>
abbreviation antitransitive::"Set(Graph('a))"
  where \<open>antitransitive G \<equiv> endorelations.antitransitive \<lfloor>G\<rfloor>\<close>
abbreviation dense::"Set(Graph('a))"
  where \<open>dense G \<equiv> endorelations.dense \<lfloor>G\<rfloor>\<close>

lemma \<open>transitive G = (\<forall>a b c. G <a,c> \<and> G <c,b> \<rightarrow> G <a,b>)\<close>
  by (simp add: B2_comb_def C21_comb_def curry_def transitive_def2)
lemma \<open>antitransitive G = (\<forall>a b c. G <a,c> \<and> G <c,b> \<rightarrow> \<not>G <a,b>)\<close>
  by (simp add: B2_comb_def C21_comb_def antitransitive_def2 curry_def)
lemma \<open>dense G = (\<forall>a b. G <a,b> \<rightarrow> (\<exists>c. G <a,c> \<and> G <c,b>))\<close> 
  unfolding endorel_defs rel_defs func_defs comb_defs unfolding pair_defs comb_defs by auto

text \<open>...and so on\<close>


subsubsection \<open>Euclideanness and co.\<close>

abbreviation rightEuclidean::"Set(Graph('a))"
  where \<open>rightEuclidean G  \<equiv> endorelations.rightEuclidean \<lfloor>G\<rfloor>\<close>
abbreviation leftEuclidean::"Set(Graph('a))"
  where \<open>leftEuclidean G \<equiv> endorelations.leftEuclidean \<lfloor>G\<rfloor>\<close>

lemma \<open>rightEuclidean G = (\<forall>a b c. G <a,b> \<and> G <a,c> \<rightarrow> G <b,c>)\<close>
  unfolding endorel_defs rel_defs func_defs comb_defs unfolding pair_defs comb_defs by auto
lemma \<open>leftEuclidean G = (\<forall>a b c. G <a,b> \<and> G <c,b> \<rightarrow> G <a,c>)\<close>
  unfolding endorel_defs rel_defs func_defs comb_defs unfolding pair_defs comb_defs by auto

text \<open>...and so on\<close>

end