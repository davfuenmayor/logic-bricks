theory endorels_mini (* A basic theory of endorelations *)
imports rels_setops
begin

section \<open>Endorelations\<close>
 
named_theorems endorel_defs (*container for related definitions*)
named_theorems endorel_simps (*container for related simplification rules*)


subsection \<open>Operations\<close>

(*The 'strict' (or 'sharp') version of a relation R*)
definition strict::"ERel('a) \<Rightarrow> ERel('a)" ("(_)\<^sup>#")
  where "strict \<equiv> \<^bold>S (\<inter>\<^sup>r) \<sim>\<^sup>r"

lemma "R\<^sup># = R \<inter>\<^sup>r (R\<^sup>\<sim>)" unfolding strict_def rel_defs set_defs comb_defs ..
lemma "R\<^sup># = (\<lambda>a b. R a b \<and> \<not>R b a)" unfolding strict_def rel_defs set_defs comb_defs ..

declare strict_def[endorel_defs]

(*The 'lax' (or 'broad') version of a relation R*)
definition lax::"ERel('a) \<Rightarrow> ERel('a)" ("(_)\<^sup>\<flat>")
  where "lax \<equiv> \<^bold>S (\<union>\<^sup>r) \<sim>\<^sup>r"

lemma "R\<^sup>\<flat> = R \<union>\<^sup>r (R\<^sup>\<sim>)" unfolding lax_def rel_defs set_defs comb_defs ..
lemma "R\<^sup>\<flat> = (\<lambda>a b. R a b \<or> \<not>R b a)" unfolding lax_def rel_defs set_defs comb_defs ..

declare strict_def[endorel_defs] lax_def[endorel_defs]

(*The notions of strict and lax are duals*)
lemma "R\<^sup>\<flat>\<^sup>\<midarrow> = R\<^sup>\<midarrow>\<^sup>#" unfolding endorel_defs rel_defs set_defs comb_defs by simp
lemma "R\<^sup>#\<^sup>\<midarrow> = R\<^sup>\<midarrow>\<^sup>\<flat>" unfolding endorel_defs rel_defs set_defs comb_defs by simp

(*...*)


subsection \<open>Properties\<close>

subsubsection \<open>Serial\<close>

definition \<open>serial \<equiv> \<forall> \<circ> leftRange\<close>

lemma \<open>serial R = (\<forall>x. \<exists>y. R x y)\<close> unfolding serial_def rel_defs comb_defs ..

declare serial_def[endorel_defs]


subsubsection \<open>Reflexive, irreflexive and their duals\<close>

definition \<open>reflexive \<equiv> (\<subseteq>\<^sup>r) \<Q>\<close>
definition "coreflexive \<equiv> (\<supseteq>\<^sup>r) \<Q>"
definition "irreflexive \<equiv> (\<supseteq>\<^sup>r) \<D>"
definition "coirreflexive \<equiv> (\<subseteq>\<^sup>r) \<D>"

lemma \<open>reflexive R = \<Q> \<subseteq>\<^sup>r R\<close> unfolding reflexive_def ..
lemma \<open>coreflexive R = R \<subseteq>\<^sup>r \<Q>\<close> unfolding coreflexive_def ..
lemma \<open>irreflexive R = R \<subseteq>\<^sup>r \<D>\<close> unfolding irreflexive_def ..
lemma \<open>coirreflexive R = \<D> \<subseteq>\<^sup>r R\<close> unfolding coirreflexive_def ..

declare reflexive_def[endorel_defs] coreflexive_def[endorel_defs]
        irreflexive_def[endorel_defs] coirreflexive_def[endorel_defs]

lemma irreflexive_def2: "irreflexive = \<^bold>B \<nexists> \<^bold>W" unfolding irreflexive_def rel_defs set_defs comb_defs by auto
lemma reflexive_def2: "reflexive = \<^bold>B \<forall> \<^bold>W" unfolding reflexive_def rel_defs set_defs comb_defs by simp

lemma "irreflexive R = (\<forall>a. \<not>R a a)" unfolding irreflexive_def2 comb_defs by simp
lemma \<open>reflexive R = (\<forall>a. R a a)\<close> unfolding reflexive_def2 comb_defs ..


subsubsection \<open>Transitivity, denseness, quasitransitivity, etc.\<close>

definition \<open>transitive \<equiv> \<^bold>S (\<supseteq>\<^sup>r) (\<^bold>W (\<circ>\<^sup>r))\<close>
definition \<open>dense \<equiv> \<^bold>S (\<subseteq>\<^sup>r) (\<^bold>W (\<circ>\<^sup>r))\<close>

lemma transitive_reldef: \<open>transitive R = (R \<circ>\<^sup>r R) \<subseteq>\<^sup>r R\<close> unfolding transitive_def comb_defs ..
lemma dense_reldef: \<open>dense R = R \<subseteq>\<^sup>r (R \<circ>\<^sup>r R)\<close> unfolding dense_def comb_defs ..

declare transitive_def[endorel_defs] dense_def[endorel_defs]

lemma \<open>transitive R = (\<forall>a b. (\<exists>c. R a c \<and> R c b) \<longrightarrow> R a b)\<close> unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma \<open>dense R = (\<forall>a b. R a b \<longrightarrow> (\<exists>c. R a c \<and> R c b))\<close> unfolding endorel_defs rel_defs set_defs comb_defs by auto

lemma transitive_def2: \<open>transitive R = (\<forall>a b c. R a c \<and> R c b \<longrightarrow> R a b)\<close> 
  unfolding transitive_def rel_defs set_defs comb_defs by auto


abbreviation \<open>quasitransitive \<equiv> transitive \<circ> strict\<close>

lemma "quasitransitive R = (\<forall>a b c. R\<^sup># a c \<and> R\<^sup># c b \<longrightarrow> R\<^sup># a b)" 
  unfolding endorel_defs comb_defs rel_defs set_defs by auto


subsubsection \<open>Symmetry, asymmetry, antisymmetry, etc.\<close>

definition \<open>symmetric \<equiv> \<^bold>S (\<subseteq>\<^sup>r) \<^bold>C\<close>
definition "asymmetric \<equiv> \<^bold>S (\<subseteq>\<^sup>r) \<sim>\<^sup>r" 
definition "antisymmetric \<equiv> \<^bold>D (\<supseteq>\<^sup>r) \<Q> (\<^bold>S (\<inter>\<^sup>r) \<^bold>C)"

lemma symmetric_reldef: \<open>symmetric R = R \<subseteq>\<^sup>r R\<Zcat>\<close> unfolding symmetric_def comb_defs ..
lemma asymmetric_reldef: \<open>asymmetric R = R \<subseteq>\<^sup>r R\<^sup>\<sim>\<close> unfolding asymmetric_def comb_defs ..
lemma antisymmetric_reldef: \<open>antisymmetric R = R \<inter>\<^sup>r (R\<Zcat>) \<subseteq>\<^sup>r \<Q>\<close> unfolding antisymmetric_def comb_defs ..

declare symmetric_def[endorel_defs] asymmetric_def[endorel_defs] antisymmetric_def[endorel_defs]

lemma \<open>symmetric R = (\<forall>a b. R a b \<longrightarrow> R b a)\<close> unfolding endorel_defs rel_defs set_defs comb_defs ..
lemma "asymmetric R = (\<forall>a b. R a b \<longrightarrow> \<not>R b a)" unfolding endorel_defs rel_defs set_defs comb_defs ..
lemma "antisymmetric R = (\<forall>a b. R a b \<and> R b a \<longrightarrow> a = b)" unfolding endorel_defs rel_defs set_defs comb_defs ..


lemma symmetric_def2: \<open>symmetric = \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<squnion>\<^sup>r) \<midarrow>\<^sup>r \<^bold>C\<close> 
  unfolding endorel_defs rel_defs set_defs comb_defs by simp
lemma asymmetric_def2: \<open>asymmetric = \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<squnion>\<^sup>r) \<midarrow>\<^sup>r \<sim>\<^sup>r\<close> 
  unfolding endorel_defs rel_defs set_defs comb_defs by simp

lemma symmetric_reldef2: \<open>symmetric R = R\<^sup>\<midarrow> \<squnion>\<^sup>r R\<Zcat>\<close> unfolding symmetric_def2 comb_defs ..
lemma asymmetric_reldef2: \<open>asymmetric R = R\<^sup>\<midarrow> \<squnion>\<^sup>r R\<^sup>\<sim>\<close> unfolding asymmetric_def2 comb_defs ..


subsubsection \<open>Connectedness & co.\<close>

definition \<open>connected \<equiv> \<^bold>S (\<supseteq>\<^sup>r) \<sim>\<^sup>r\<close>  (*aka. 'linear' if an ordering *)

lemma connected_reldef: \<open>connected R = (R\<^sup>\<sim> \<subseteq>\<^sup>r R)\<close> unfolding connected_def comb_defs ..

declare connected_def[endorel_defs]

lemma \<open>connected R = (\<forall>a b. \<not>R b a \<longrightarrow> R a b)\<close> unfolding endorel_defs rel_defs set_defs comb_defs ..

lemma connected_def2: \<open>connected = \<^bold>S (\<squnion>\<^sup>r) \<^bold>C\<close> 
  unfolding endorel_defs rel_defs set_defs comb_defs by auto

lemma connected_reldef2: \<open>connected R = R \<squnion>\<^sup>r R\<Zcat>\<close> unfolding connected_def2 comb_defs ..


subsubsection \<open>Euclideanness & co.\<close>

definition \<open>euclidean \<equiv> \<^bold>S (\<supseteq>\<^sup>r) (\<^bold>S (\<circ>\<^sup>r) \<^bold>C)\<close>

lemma euclidean_reldef: "euclidean R = R \<circ>\<^sup>r (R\<Zcat>) \<subseteq>\<^sup>r R" unfolding euclidean_def comb_defs ..

declare euclidean_def[endorel_defs]

lemma "euclidean R = (\<forall>a b. (\<exists>c. R c a \<and> R c b) \<rightarrow> R a b)" 
  unfolding endorel_defs rel_defs set_defs comb_defs ..

lemma euclidean_def2: \<open>euclidean R = (\<forall>a b c. R c a \<and> R c b \<longrightarrow> R a b)\<close>
  unfolding endorel_defs rel_defs set_defs comb_defs by blast


subsubsection \<open>Equivalence, equality & co.\<close>

(*Equivalence relations are their own kernels (when seen as set-valued functions)*)
definition "equivalence \<equiv> fp kernel" 

lemma equivalence_reldef: "equivalence R = (R = R\<^sup>=)" 
  unfolding equivalence_def func_defs comb_defs ..

declare equivalence_def[endorel_defs]

lemma "equivalence R = (\<forall>a b. R a b = (R a = R b))"
  unfolding endorel_defs func_defs comb_defs by metis

(*In fact, equality (\<Q>) is an equivalence relation (which means that \<Q> is identical to its own kernel)*)
lemma "equivalence \<Q>" 
  unfolding endorel_defs func_defs comb_defs by fastforce

(*This gives a kind of recursive definition of equality (of which we make a simplification rule)*)
lemma eq_kernel_simp: "\<Q>\<^sup>= = \<Q>" 
  unfolding endorel_defs func_defs comb_defs by fastforce

declare eq_kernel_simp[endorel_simps]

(*Equality has other alternative definitions. We also make simplification rules out of them: *)

(*The intersection of all reflexive relations*)
lemma eq_refl_simp: "\<Inter>\<^sup>r reflexive = \<Q>\<^sup>=" 
  unfolding biginterR_def2 reflexive_def2 func_defs comb_defs by (metis (mono_tags, opaque_lifting))

(*Leibniz principle of identity of indiscernibles*)
lemma eq_leibniz_simp1: "(\<lambda>a b. \<forall>P. P a \<leftrightarrow> P b) = \<Q>\<^sup>=" (*symmetric version*)
  unfolding func_defs comb_defs by (metis (full_types))
lemma eq_leibniz_simp2: "(\<lambda>a b. \<forall>P. P a \<rightarrow> P b) = \<Q>\<^sup>=" (*simplified version*)
  unfolding func_defs comb_defs by (metis (full_types))

(*By extensionality, the above equation can be written as follows *)
lemma eq_cont_simp1: "(\<lambda>a b. (\<lambda>k. k a) \<subseteq> (\<lambda>c. c b)) = \<Q>\<^sup>=" 
  unfolding func_defs set_defs comb_defs by (metis (full_types))

(*Equality also corresponds to identity of generated principal filters *)
lemma eq_cont_simp2: "(\<lambda>a b. (\<lambda>k::Set(Set('a)). k a) = (\<lambda>c. c b)) = \<Q>\<^sup>="
  unfolding func_defs comb_defs by (metis (full_types))
(*or, in terms of combinators*)
lemma eq_cont_simp3: "(\<^bold>T::'a \<Rightarrow> Set(Set('a)))\<^sup>= = \<Q>\<^sup>="
  unfolding func_defs comb_defs by (metis (full_types))

declare eq_refl_simp[endorel_simps] eq_leibniz_simp1[endorel_simps] eq_leibniz_simp2[endorel_simps]
        eq_cont_simp1[endorel_simps] eq_cont_simp2[endorel_simps] eq_cont_simp3[endorel_simps]

(*Finally, note that*)
lemma "(\<forall>y::'a \<Rightarrow> o. y a = y b) \<Longrightarrow> (\<forall>y::'a \<Rightarrow> 'b. y a = y b)" oops (*Zipperpin finds a proof*)
lemma "(\<forall>y::'a \<Rightarrow> 'b. y a = y b) \<Longrightarrow> (\<forall>y::'a \<Rightarrow> o. y a = y b)" nitpick oops (*counterexample*)


subsection \<open>Interdefinitions\<close>

(*We have in fact the following alternative interdefinitions between properties:*)
lemma connected_char: "connected R = asymmetric R\<^sup>\<midarrow>"
  unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma asymmetric_char: "asymmetric R = (irreflexive R \<and> antisymmetric R)"
  unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma equivalence_char: "equivalence R = (reflexive R \<and> transitive R \<and> symmetric R)"
  unfolding endorel_defs rel_defs set_defs func_defs comb_defs sorry (*zipperpin found a proof*)
(*... more *)

end