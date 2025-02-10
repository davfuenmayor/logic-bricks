theory endorels (* A basic theory of endorelations *)
imports rels
begin

section \<open>Endorelations\<close>
 
named_theorems endorel_defs


subsection \<open>Reflexive, irreflexive & co.\<close>

definition reflexive::"Set(ERel('a))"
  where \<open>reflexive     \<equiv> (\<subseteq>\<^sup>r) \<Q>\<close>
definition coreflexive::"Set(ERel('a))" 
  where "coreflexive   \<equiv> (\<supseteq>\<^sup>r) \<Q>"
definition irreflexive::"Set(ERel('a))"
  where "irreflexive   \<equiv> (\<supseteq>\<^sup>r) \<D>"
definition coirreflexive::"Set(ERel('a))"
  where "coirreflexive \<equiv> (\<subseteq>\<^sup>r) \<D>"

lemma \<open>reflexive R = \<Q> \<subseteq>\<^sup>r R\<close> unfolding reflexive_def ..
lemma \<open>coreflexive R = R \<subseteq>\<^sup>r \<Q>\<close> unfolding coreflexive_def ..
lemma \<open>irreflexive R = R \<subseteq>\<^sup>r \<D>\<close> unfolding irreflexive_def ..
lemma \<open>coirreflexive R = \<D> \<subseteq>\<^sup>r R\<close> unfolding coirreflexive_def ..

declare reflexive_def[endorel_defs] coreflexive_def[endorel_defs] 
        irreflexive_def[endorel_defs] coirreflexive_def[endorel_defs]

lemma irreflexive_def2: "irreflexive = \<^bold>B \<nexists> \<^bold>W" unfolding irreflexive_def rel_defs set_defs comb_defs by auto
lemma reflexive_def2: "reflexive = \<^bold>B \<forall> \<^bold>W" unfolding reflexive_def rel_defs set_defs comb_defs by simp

lemma "irreflexive R = (\<forall>a. \<not>R a a)" unfolding irreflexive_def2 set_defs comb_defs by simp
lemma \<open>reflexive R = (\<forall>a. R a a)\<close> unfolding reflexive_def2 comb_defs ..


(*The smallest reflexive super-relation resp. largest irreflexive subrelation *)
definition reflexiveClosure::"ERel('a) \<Rightarrow> ERel('a)" (*TODO: superscript notation*)
  where "reflexiveClosure    \<equiv> (\<union>\<^sup>r) \<Q>"
definition irreflexiveInterior::"ERel('a) \<Rightarrow> ERel('a)"
  where "irreflexiveInterior \<equiv> (\<inter>\<^sup>r) \<D>"

declare reflexiveClosure_def[endorel_defs] irreflexiveInterior_def[endorel_defs]

lemma "reflexiveClosure    R = (R \<union>\<^sup>r \<Q>)" unfolding endorel_defs rel_defs comb_defs by auto
lemma "irreflexiveInterior R = (R \<inter>\<^sup>r \<D>)" unfolding endorel_defs rel_defs comb_defs by auto

lemma "reflexive (reflexiveClosure R)" unfolding endorel_defs rel_defs set_defs comb_defs by simp
lemma "irreflexive (irreflexiveInterior R)" unfolding endorel_defs rel_defs set_defs comb_defs by simp


subsection \<open>Symmetry, connectedness & co.\<close>

definition symmetric::"Set(ERel('a))"
  where \<open>symmetric \<equiv> \<^bold>S (\<subseteq>\<^sup>r) \<smile>\<close>
lemma symmetric_def2: 
        "symmetric  = \<^bold>S (\<supseteq>\<^sup>r) \<smile>"       unfolding symmetric_def rel_defs set_defs comb_defs by auto
definition asymmetric::"Set(ERel('a))"
  where "asymmetric \<equiv> \<^bold>S (\<subseteq>\<^sup>r) \<frown>"
definition connected::"Set(ERel('a))"
  where \<open>connected \<equiv>  \<^bold>S (\<supseteq>\<^sup>r) \<frown>\<close>  (*aka. 'linear' or 'total' in order theory *)

declare symmetric_def[endorel_defs] asymmetric_def[endorel_defs] connected_def[endorel_defs]

lemma symmetric_reldef:   \<open>symmetric R = R  \<subseteq>\<^sup>r R\<^sup>\<smile>\<close> unfolding endorel_defs comb_defs ..
lemma symmetric_reldef2:  \<open>symmetric R = R\<^sup>\<smile> \<subseteq>\<^sup>r R\<close> unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma asymmetric_reldef: \<open>asymmetric R = R  \<subseteq>\<^sup>r R\<^sup>\<frown>\<close> unfolding endorel_defs comb_defs ..
lemma connected_reldef:   \<open>connected R = R\<^sup>\<frown> \<subseteq>\<^sup>r R\<close> unfolding endorel_defs comb_defs ..

lemma \<open>symmetric R = (\<forall>a b. R a b \<rightarrow> R b a)\<close> unfolding endorel_defs rel_defs set_defs comb_defs ..
lemma "asymmetric R = (\<forall>a b. R a b \<rightarrow> \<not>R b a)" unfolding endorel_defs rel_defs set_defs comb_defs ..
lemma \<open>connected R = (\<forall>a b. \<not>R b a \<rightarrow> R a b)\<close> unfolding endorel_defs rel_defs set_defs comb_defs ..

lemma "symmetric R\<^sup>\<midarrow> = symmetric R" unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma "connected R\<^sup>\<midarrow> = asymmetric R" unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma "asymmetric R\<^sup>\<midarrow> = connected R" unfolding endorel_defs rel_defs set_defs comb_defs by auto

(*Connectedness resp. asymmetry entail reflexivity resp. irreflexivity*)
lemma "connected R \<Longrightarrow> reflexive R" unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma "asymmetric R \<Longrightarrow> irreflexive R" unfolding endorel_defs rel_defs set_defs comb_defs by auto

(*An alternative (more intuitive?) definition of connectedness *)
lemma connected_def2: \<open>connected = \<^bold>S (\<squnion>\<^sup>r) \<smile>\<close> unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma connected_reldef2: \<open>connected R = R \<squnion>\<^sup>r R\<^sup>\<smile>\<close> unfolding connected_def2 comb_defs ..
lemma \<open>connected R = (\<forall>a b. R b a \<or> R a b)\<close> unfolding connected_reldef2 rel_defs comb_defs by auto


(*The following are operations on relations associated to the previous properties. We start by considering
 two ways of 'symmetrizing' a given relation R: The symmetric closure/interior operation merges/intersects
 R with its converse, thus generating its smallest/largest symmetric super/sub-relation. 
 Note that, if R is symmetric, then its closure and interior coincide.*)
definition symmetricClosure::"ERel('a) \<Rightarrow> ERel('a)" ("(_)\<^sup>s\<^sup>c")
  where "symmetricClosure  \<equiv> \<^bold>S (\<union>\<^sup>r) \<smile>"
definition symmetricInterior::"ERel('a) \<Rightarrow> ERel('a)" ("(_)\<^sup>s\<^sup>i")
  where "symmetricInterior \<equiv> \<^bold>S (\<inter>\<^sup>r) \<smile>" (*aka. symmetric part of R*)

declare symmetricClosure_def[endorel_defs] symmetricInterior_def[endorel_defs]

lemma "R\<^sup>s\<^sup>c = R \<union>\<^sup>r (R\<^sup>\<smile>)" unfolding endorel_defs rel_defs comb_defs ..
lemma "R\<^sup>s\<^sup>i = R \<inter>\<^sup>r (R\<^sup>\<smile>)" unfolding endorel_defs rel_defs comb_defs ..

lemma "R\<^sup>s\<^sup>c = \<Inter>\<^sup>r(\<lambda>T. R \<subseteq>\<^sup>r T \<and> symmetric T)" oops (*TODO: reconstruct proof*)
lemma "R\<^sup>s\<^sup>i = \<Union>\<^sup>r(\<lambda>T. T \<subseteq>\<^sup>r R \<and> symmetric T)" oops (*TODO: reconstruct proof*)

(*Symmetric closure/interior are of course symmetric*)
lemma "symmetric (R\<^sup>s\<^sup>c)" unfolding endorel_defs rel_defs set_defs comb_defs by simp
lemma "symmetric (R\<^sup>s\<^sup>i)" unfolding endorel_defs rel_defs set_defs comb_defs by simp

(*Symmetric relations are fixed-points of the symmetric closure/interior*)
lemma "symmetric = FP symmetricClosure" unfolding endorel_defs rel_defs func_defs set_defs comb_defs by metis
lemma "symmetric = FP symmetricInterior" unfolding endorel_defs rel_defs func_defs set_defs comb_defs by metis

lemma "connected R = \<forall>\<^sup>2(R\<^sup>s\<^sup>c)" unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma "asymmetric R = \<nexists>\<^sup>2(R\<^sup>s\<^sup>i)" unfolding endorel_defs rel_defs set_defs comb_defs by auto

(*The notions of symmetric closure and symmetric interior are duals wrt. relation-complement*)
lemma "(R\<^sup>\<midarrow>)\<^sup>s\<^sup>i = (R\<^sup>s\<^sup>c)\<^sup>\<midarrow>" unfolding endorel_defs rel_defs set_defs comb_defs by simp
lemma "(R\<^sup>\<midarrow>)\<^sup>s\<^sup>c = (R\<^sup>s\<^sup>i)\<^sup>\<midarrow>" unfolding endorel_defs rel_defs set_defs comb_defs by simp

(*The properties of (ir)reflexivity and co(ir)reflexivity are preserved by symmetric interior and closure*)
lemma reflexive_si: \<open>reflexive R = reflexive R\<^sup>s\<^sup>i\<close> unfolding endorel_defs rel_defs set_defs comb_defs by simp
lemma coirreflexive_si: \<open>coirreflexive R = coirreflexive R\<^sup>s\<^sup>i\<close> unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma coreflexive_sc: \<open>coreflexive R = coreflexive R\<^sup>s\<^sup>c\<close> unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma irreflexive_sc: \<open>irreflexive R = irreflexive R\<^sup>s\<^sup>c\<close> unfolding endorel_defs rel_defs set_defs comb_defs by auto

(*TODO: check that symmetricInterior and symmetricClosure form a Galois connection *)


(*The following operation takes a relation R and returns its 'strict' or 'sharp' part, which is always
 an asymmetric sub-relation (though not a maximal one in general).*)
definition strict::"ERel('a) \<Rightarrow> ERel('a)" ("(_)\<^sup>#")
  where "strict \<equiv> \<^bold>S (\<inter>\<^sup>r) \<frown>"

lemma "R\<^sup># = R \<inter>\<^sup>r (R\<^sup>\<frown>)" unfolding strict_def rel_defs set_defs comb_defs ..
lemma "R\<^sup># = (\<lambda>a b. R a b \<and> \<not>R b a)" unfolding strict_def rel_defs set_defs comb_defs ..

(*Analogously, the following operation takes relation a R and returns its 'lax' or 'broad' extension,
 which is always a connected super-relation (though not a minimal one in general)*)
definition lax::"ERel('a) \<Rightarrow> ERel('a)" ("(_)\<^sup>\<flat>")
  where "lax \<equiv> \<^bold>S (\<union>\<^sup>r) \<frown>"

lemma "R\<^sup>\<flat> = R \<union>\<^sup>r (R\<^sup>\<frown>)" unfolding lax_def rel_defs set_defs comb_defs ..
lemma "R\<^sup>\<flat> = (\<lambda>a b. R a b \<or> \<not>R b a)" unfolding lax_def rel_defs set_defs comb_defs ..

declare strict_def[endorel_defs] lax_def[endorel_defs]

(*Strict resp. lax variants are always asymmetric resp. connected relations*)
lemma "asymmetric R\<^sup>#" unfolding endorel_defs rel_defs set_defs comb_defs by simp
lemma "connected R\<^sup>\<flat>" unfolding endorel_defs rel_defs set_defs comb_defs by simp

(*The notions of strict and lax are duals wrt. relation-complement*)
lemma "R\<^sup>\<flat>\<^sup>\<midarrow> = R\<^sup>\<midarrow>\<^sup>#" unfolding endorel_defs rel_defs set_defs comb_defs by simp
lemma "R\<^sup>#\<^sup>\<midarrow> = R\<^sup>\<midarrow>\<^sup>\<flat>" unfolding endorel_defs rel_defs set_defs comb_defs by simp

(* TODO: check whether the pair strict/lax forms a (dual)Galois connection *)


subsection \<open>Antisymmetry, semiconnectedness, etc.\<close>

definition antisymmetric::"Set(ERel('a))"
  where "antisymmetric \<equiv> coreflexive \<circ> symmetricInterior"
definition semiconnected::"Set(ERel('a))"
  where "semiconnected \<equiv> coirreflexive \<circ> symmetricClosure"

declare antisymmetric_def[endorel_defs] semiconnected_def[endorel_defs]

lemma \<open>antisymmetric R = coreflexive R\<^sup>s\<^sup>i\<close> unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma \<open>antisymmetric R = R\<^sup>s\<^sup>i \<subseteq>\<^sup>r \<Q>\<close> unfolding endorel_defs comb_defs ..
lemma antisymmetric_reldef: \<open>antisymmetric R = R \<inter>\<^sup>r (R\<^sup>\<smile>) \<subseteq>\<^sup>r \<Q>\<close> unfolding endorel_defs comb_defs ..

lemma \<open>semiconnected R = \<D> \<subseteq>\<^sup>r R\<^sup>s\<^sup>c\<close> unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma \<open>semiconnected R = coirreflexive R\<^sup>s\<^sup>c\<close> unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma semiconnected_reldef: "semiconnected R = (\<forall>a b. a \<noteq> b \<rightarrow> R a b \<or> R b a)" unfolding endorel_defs rel_defs set_defs comb_defs ..

(*A relation is antisymmetric/semiconnected iff its complement is semiconnected/antisymmetric*)
lemma antisymmetric_defN:  "antisymmetric R = semiconnected R\<^sup>\<midarrow>" unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma semiconnected_defN:  "semiconnected R = antisymmetric R\<^sup>\<midarrow>" unfolding endorel_defs rel_defs set_defs comb_defs by auto

lemma "asymmetric R = (irreflexive R \<and> antisymmetric R)" unfolding endorel_defs rel_defs set_defs comb_defs by auto

(*A relation is called (co)skeletal when its symmetric interior (closure) is the (dis)equality relation,
 inspired by category theory where categories are skeletal when isomorphic objects are identical*)
definition skeletal::"Set(ERel('a))"
  where \<open>skeletal   \<equiv> \<^bold>B\<^sub>0\<^sub>1 \<Q> \<Q> symmetricInterior\<close> 
definition coskeletal::"Set(ERel('a))"
  where \<open>coskeletal \<equiv> \<^bold>B\<^sub>0\<^sub>1 \<Q> \<D> symmetricClosure\<close> 

declare skeletal_def[endorel_defs] coskeletal_def[endorel_defs]

lemma "skeletal   R = (\<Q> = R\<^sup>s\<^sup>i)" unfolding endorel_defs comb_defs ..
lemma "coskeletal R = (\<D> = R\<^sup>s\<^sup>c)" unfolding endorel_defs comb_defs ..

lemma "skeletal R = coskeletal R\<^sup>\<midarrow>" unfolding endorel_defs rel_defs comb_defs by (rule iffI, metis (mono_tags, lifting), (rule ext)+, metis)
lemma "coskeletal R = skeletal R\<^sup>\<midarrow>" unfolding endorel_defs rel_defs comb_defs by (rule iffI, (rule ext)+, metis, metis (mono_tags, lifting))

lemma skeletal_def2:  "skeletal R = (reflexive R \<and> antisymmetric R)"
  using reflexive_si unfolding antisymmetric_reldef endorel_defs comb_defs by (smt (verit, ccfv_threshold) B2_comb_def \<Phi>22_comb_def implR_def subrel_antisymm subrel_def2)
lemma coskeletal_def2:  "coskeletal R = (irreflexive R \<and> semiconnected R)" 
  using irreflexive_sc unfolding semiconnected_reldef endorel_defs comb_defs by (smt (verit, best) B2_comb_def \<Phi>22_comb_def implR_def subrel_antisymm subrel_def2)


subsection \<open>Transitivity, denseness, quasitransitivity, etc.\<close>

(*Every pair of elements x and y that can be connected by an element z in between are (un)related*)
definition transitive::"Set(ERel('a))"
  where \<open>transitive \<equiv> \<^bold>S (\<supseteq>\<^sup>r) (\<^bold>W (\<circ>\<^sup>r))\<close>
definition antitransitive::"Set(ERel('a))"
  where \<open>antitransitive \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<supseteq>\<^sup>r) \<midarrow>\<^sup>r (\<^bold>W (\<circ>\<^sup>r))\<close>

declare transitive_def[endorel_defs] antitransitive_def[endorel_defs]

lemma transitive_reldef: \<open>transitive R = (R \<circ>\<^sup>r R) \<subseteq>\<^sup>r R\<close> unfolding endorel_defs comb_defs ..
lemma antitransitive_reldef: \<open>antitransitive R = (R \<circ>\<^sup>r R) \<subseteq>\<^sup>r R\<^sup>\<midarrow>\<close> unfolding endorel_defs comb_defs ..

(*Alternative convenient definitions*)
lemma transitive_def2: \<open>transitive R = (\<forall>a b c. R a c \<and> R c b \<rightarrow> R a b)\<close>
  unfolding transitive_def rel_defs set_defs comb_defs by auto
lemma antitransitive_def2: \<open>antitransitive R = (\<forall>a b c. R a c \<and> R c b \<rightarrow> \<not>R a b)\<close>
  unfolding antitransitive_def rel_defs set_defs comb_defs by auto

(*Relationship between antitransitivity and irreflexivity*)
lemma "antitransitive R \<Longrightarrow> irreflexive R" 
  unfolding endorel_defs rel_defs set_defs comb_defs by metis
lemma "leftUnique R \<or> rightUnique R \<Longrightarrow> antitransitive R = irreflexive R"
  unfolding endorel_defs rel_defs set_defs comb_defs by metis

(*Every pair of (un)related elements x and y can be connected by an element z in between*)
definition dense::"Set(ERel('a))"
  where \<open>dense \<equiv> \<^bold>S (\<subseteq>\<^sup>r) (\<^bold>W (\<circ>\<^sup>r))\<close>
definition pseudoClique::"Set(ERel('a))" (*i.e. a graph with diameter 2 (where cliques have diameter 1)*)
  where \<open>pseudoClique \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<subseteq>\<^sup>r) \<midarrow>\<^sup>r (\<^bold>W (\<circ>\<^sup>r))\<close>

declare dense_def[endorel_defs] pseudoClique_def[endorel_defs]

lemma dense_reldef: \<open>dense R = R \<subseteq>\<^sup>r (R \<circ>\<^sup>r R)\<close> unfolding endorel_defs comb_defs ..
lemma pseudoClique_reldef: \<open>pseudoClique R = R\<^sup>\<midarrow> \<subseteq>\<^sup>r (R \<circ>\<^sup>r R)\<close> unfolding endorel_defs comb_defs ..

(*The above properties are preserved by transposition*)
lemma transitive_defT: "transitive R = transitive (R\<^sup>\<smile>)" unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma antitransitive_defT: "antitransitive R = antitransitive (R\<^sup>\<smile>)" unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma quasiDense_defT: "dense R = dense (R\<^sup>\<smile>)" unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma quasiClique_defT: "pseudoClique R = pseudoClique (R\<^sup>\<smile>)" unfolding endorel_defs rel_defs set_defs comb_defs by auto

(*The above properties can be stated for the complemented relations in an analogous fashion*)
lemma transitive_compl_reldef: \<open>transitive R\<^sup>\<midarrow> = R  \<subseteq>\<^sup>r (R \<bullet>\<^sup>r R)\<close> unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma dense_compl_reldef:     \<open>dense R\<^sup>\<midarrow> = (R \<bullet>\<^sup>r R) \<subseteq>\<^sup>r R\<close> unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma antitransitive_compl_reldef:  \<open>antitransitive R\<^sup>\<midarrow> = R\<^sup>\<midarrow> \<subseteq>\<^sup>r (R \<bullet>\<^sup>r R)\<close> unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma pseudoClique_compl_reldef: \<open>pseudoClique R\<^sup>\<midarrow> = (R \<bullet>\<^sup>r R) \<subseteq>\<^sup>r R\<^sup>\<midarrow>\<close> unfolding endorel_defs rel_defs set_defs comb_defs by auto

(*We now conveniently encode a notion of 'interval' (wrt given relation R) as the set of elements x 
 that lie between a given pair of points a & b (seen as 'boundaries').*)
abbreviation(input) interval::"ERel('a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> Set('a)" ("_-interval")
  where "R-interval a b \<equiv> R a \<inter> R\<^sup>\<smile> b"

lemma "R-interval = (\<lambda>a b. \<lambda>x. R a x \<and> R x b)" unfolding rel_defs set_defs comb_defs ..

(*We can provide alternative definitions for the above relational properties in terms of intervals.*)
lemma \<open>transitive R     = (\<forall>a b. \<exists>(R-interval a b) \<rightarrow> R a b)\<close>  unfolding endorel_defs rel_defs set_defs comb_defs ..
lemma \<open>antitransitive R = (\<forall>a b. \<exists>(R-interval a b) \<rightarrow> R\<^sup>\<midarrow> a b)\<close> unfolding endorel_defs rel_defs set_defs comb_defs ..
lemma \<open>dense R        = (\<forall>a b. R a b  \<rightarrow> \<exists>(R-interval a b))\<close> unfolding endorel_defs rel_defs set_defs comb_defs ..
lemma \<open>pseudoClique R = (\<forall>a b. R\<^sup>\<midarrow> a b \<rightarrow> \<exists>(R-interval a b))\<close> unfolding endorel_defs rel_defs set_defs comb_defs ..

(*The following notions are often discussed in the literature (applied to strict relations/orderings)*)
abbreviation(input) \<open>quasiTransitive \<equiv> transitive \<circ> strict\<close>
abbreviation(input) \<open>quasiAntitransitive \<equiv> antitransitive \<circ> strict\<close>

lemma \<open>quasiTransitive R = (\<forall>a b. \<exists>(R\<^sup>#-interval a b) \<rightarrow> R\<^sup># a b)\<close>
  unfolding endorel_defs rel_defs set_defs comb_defs ..
lemma \<open>quasiAntitransitive R = (\<forall>a b. \<exists>(R\<^sup>#-interval a b) \<rightarrow> R\<^sup>#\<^sup>\<midarrow> a b)\<close>
  unfolding endorel_defs rel_defs set_defs comb_defs ..

(*The 'quasi' variants are weaker than their counterparts*)
lemma "transitive R \<Longrightarrow> quasiTransitive R" unfolding endorel_defs rel_defs set_defs comb_defs by metis
lemma "antitransitive R \<Longrightarrow> quasiAntitransitive R" unfolding endorel_defs rel_defs set_defs comb_defs by metis
(*However, both variants coincide under the right conditions*)
lemma "antisymmetric R \<Longrightarrow> quasiTransitive R = transitive R" unfolding endorel_defs rel_defs set_defs comb_defs by metis
lemma "asymmetric R \<Longrightarrow> quasiAntitransitive R = antitransitive R" unfolding endorel_defs rel_defs set_defs comb_defs by metis

lemma quasiTransitive_defT: "quasiTransitive R = quasiTransitive (R\<^sup>\<smile>)" unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma quasiAntitransitive_defT: "quasiAntitransitive R = quasiAntitransitive (R\<^sup>\<smile>)" unfolding endorel_defs rel_defs set_defs comb_defs by auto

lemma quasitransitive_defN: "quasiTransitive R = quasiTransitive (R\<^sup>\<midarrow>)" unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma quasiintransitive_defN: "quasiAntitransitive R = quasiAntitransitive (R\<^sup>\<midarrow>)" unfolding endorel_defs rel_defs set_defs comb_defs by auto

(*Symmetry entails both quasi-transitivity and quasi-antitransitivity*)
lemma "symmetric R \<Longrightarrow> quasiTransitive R" unfolding endorel_defs rel_defs set_defs comb_defs by metis
lemma "symmetric R \<Longrightarrow> quasiAntitransitive R" unfolding endorel_defs rel_defs set_defs comb_defs by metis

(*A natural way to obtain transitive relations*)
definition transitiveClosure::"ERel('a) \<Rightarrow> ERel('a)"
  where "transitiveClosure \<equiv> \<Inter>\<^sup>r \<circ> (\<^bold>D (\<inter>) transitive (\<subseteq>\<^sup>r))  "

lemma "transitiveClosure R = \<Inter>\<^sup>r(\<lambda>T. transitive T \<and> R \<subseteq>\<^sup>r T)" 
  unfolding transitiveClosure_def rel_defs set_defs comb_defs ..


subsection \<open>Euclideanness & co.\<close>

definition \<open>rightEuclidean \<equiv> \<^bold>S (\<supseteq>\<^sup>r) (\<^bold>S (\<circ>\<^sup>r) \<smile>)\<close>
definition \<open>leftEuclidean  \<equiv> \<^bold>S (\<supseteq>\<^sup>r) (\<^bold>\<Sigma> (\<circ>\<^sup>r) \<smile>)\<close>

lemma rightEuclidean_reldef: "rightEuclidean R = R \<circ>\<^sup>r (R\<^sup>\<smile>) \<subseteq>\<^sup>r R" unfolding rightEuclidean_def comb_defs ..
lemma leftEuclidean_reldef:  "leftEuclidean  R = (R\<^sup>\<smile>) \<circ>\<^sup>r R \<subseteq>\<^sup>r R" unfolding leftEuclidean_def comb_defs ..

declare rightEuclidean_def[endorel_defs] leftEuclidean_def[endorel_defs]

lemma "rightEuclidean R = (\<forall>a b. (\<exists>c. R c a \<and> R c b) \<rightarrow> R a b)" 
  unfolding endorel_defs rel_defs set_defs comb_defs ..
lemma "leftEuclidean R = (\<forall>a b. (\<exists>c. R a c \<and> R b c) \<rightarrow> R a b)" 
  unfolding endorel_defs rel_defs set_defs comb_defs ..

lemma "leftEuclidean R = rightEuclidean R\<^sup>\<smile>"
   unfolding endorel_defs rel_defs set_defs comb_defs by auto

lemma "symmetric R \<Longrightarrow> rightEuclidean R = leftEuclidean R"
  unfolding endorel_defs rel_defs set_defs comb_defs by blast

lemma rightEuclidean_def2: \<open>rightEuclidean R = (\<forall>a b c. R c a \<and> R c b \<rightarrow> R a b)\<close>
  unfolding endorel_defs rel_defs set_defs comb_defs by blast
lemma leftEuclidean_def2: \<open>leftEuclidean R = (\<forall>a b c. R a c \<and> R b c \<rightarrow> R a b)\<close>
  unfolding endorel_defs rel_defs set_defs comb_defs by blast

lemma "leftEuclidean R \<Longrightarrow> quasiTransitive R" unfolding endorel_defs rel_defs set_defs comb_defs by metis
lemma "rightEuclidean R \<Longrightarrow> quasiTransitive R" unfolding endorel_defs rel_defs set_defs comb_defs by metis

lemma "connected R \<Longrightarrow> rightEuclidean R \<Longrightarrow> transitive R" unfolding endorel_defs rel_defs set_defs comb_defs by metis
lemma "connected R \<Longrightarrow> leftEuclidean R \<Longrightarrow> transitive R" unfolding endorel_defs rel_defs set_defs comb_defs by metis

lemma "symmetric R \<Longrightarrow> leftEuclidean R = transitive R" unfolding endorel_defs rel_defs set_defs comb_defs by metis
lemma "symmetric R \<Longrightarrow> rightEuclidean R = transitive R" unfolding endorel_defs rel_defs set_defs comb_defs by metis

lemma "reflexive R \<Longrightarrow> rightEuclidean R \<Longrightarrow> transitive R" unfolding endorel_defs rel_defs set_defs comb_defs by metis
lemma "reflexive R \<Longrightarrow> leftEuclidean R \<Longrightarrow> transitive R" unfolding endorel_defs rel_defs set_defs comb_defs by metis

lemma "leftEuclidean R \<Longrightarrow> leftUnique R = antisymmetric R" unfolding endorel_defs rel_defs set_defs comb_defs by metis
lemma "rightEuclidean R \<Longrightarrow> rightUnique R = antisymmetric R" unfolding endorel_defs rel_defs set_defs comb_defs by metis


subsection \<open>Equivalence, equality & co.\<close>

(*Equivalence relations are their own kernels (when seen as set-valued functions)*)
definition "equivalence \<equiv> FP kernel" 

lemma equivalence_reldef: "equivalence R = (R = R\<^sup>=)" 
  unfolding equivalence_def func_defs comb_defs ..

declare equivalence_def[endorel_defs]

lemma "equivalence R = (\<forall>a b. R a b = (R a = R b))"
  unfolding endorel_defs func_defs comb_defs by metis

lemma equivalence_char: "equivalence R = (reflexive R \<and> transitive R \<and> symmetric R)"
  unfolding endorel_defs rel_defs set_defs func_defs comb_defs sorry (*zipperpin found a proof*)


(*In fact, equality (\<Q>) is an equivalence relation (which means that \<Q> is identical to its own kernel)*)
lemma "equivalence \<Q>" 
  unfolding endorel_defs func_defs comb_defs by fastforce

(*This gives a kind of recursive definition of equality (of which we can make a simplification rule)*)
lemma eq_kernel_simp: "\<Q>\<^sup>= = \<Q>" 
  unfolding endorel_defs func_defs comb_defs by fastforce

(*Equality has other alternative definitions. We can also make simplification rules out of them: *)

(*The intersection of all reflexive relations*)
lemma eq_refl_simp: "\<Inter>\<^sup>r reflexive = \<Q>\<^sup>=" 
  unfolding biginterR_def2 reflexive_def2 func_defs comb_defs by (metis (mono_tags, opaque_lifting))

(*Leibniz principle of identity of indiscernibles*)
lemma eq_leibniz_simp1: "(\<lambda>a b. \<forall>P. P a \<leftrightarrow> P b) = \<Q>\<^sup>=" (*symmetric version*)
  unfolding func_defs comb_defs by (metis (full_types))
lemma eq_leibniz_simp2: "(\<lambda>a b. \<forall>P. P a \<rightarrow> P b) = \<Q>\<^sup>=" (*simplified version*)
  unfolding func_defs comb_defs by (metis (full_types))

(*By extensionality, the above equation can be written as follows *)
lemma eq_filt_simp1: "(\<lambda>a b. (\<lambda>k. k a) \<subseteq> (\<lambda>c. c b)) = \<Q>\<^sup>=" 
  unfolding func_defs set_defs comb_defs by (metis (full_types))

(*Equality also corresponds to identity of generated principal filters *)
lemma eq_filt_simp2: "(\<lambda>a b. (\<lambda>k::Set(Set('a)). k a) = (\<lambda>c. c b)) = \<Q>\<^sup>="
  unfolding func_defs comb_defs by (metis (full_types))
(*or, in terms of combinators*)
lemma eq_filt_simp3: "(\<^bold>T::'a \<Rightarrow> Set(Set('a)))\<^sup>= = \<Q>\<^sup>="
  unfolding func_defs comb_defs by (metis (full_types))

(*Finally, note that*)
lemma "(\<forall>y::'a \<Rightarrow> o. y a = y b) \<Longrightarrow> (\<forall>y::'a \<Rightarrow> 'b. y a = y b)" oops (*Zipperpin finds a proof*)
lemma "(\<forall>y::'a \<Rightarrow> 'b. y a = y b) \<Longrightarrow> (\<forall>y::'a \<Rightarrow> o. y a = y b)" nitpick oops (*counterexample*)


subsection \<open>Orderings\<close>

definition "preorder R \<equiv> reflexive R \<and> transitive R"
definition "partial_order R \<equiv> preorder R \<and> antisymmetric R"

declare preorder_def [endorel_defs] partial_order_def [endorel_defs]

lemma preorder_def2: "preorder R = (\<forall>a b. R a b = (\<forall>x. R b x \<rightarrow> R a x))"
  unfolding preorder_def reflexive_def2 transitive_def2 comb_defs by auto

lemma partial_order_def2: "partial_order R = (skeletal R \<and> transitive R)"
  using partial_order_def preorder_def skeletal_def2 by blast


lemma reflexive_symm: "reflexive R\<^sup>\<smile> = reflexive R" unfolding reflexive_def2 rel_defs comb_defs ..
lemma transitive_symm: "transitive R\<^sup>\<smile> = transitive R" unfolding transitive_def2 rel_defs comb_defs by auto
lemma antisymmetric_symm: "antisymmetric R\<^sup>\<smile> = antisymmetric R" unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma skeletal_symm: "skeletal R\<^sup>\<smile> = skeletal R" unfolding skeletal_def2 by (simp add: antisymmetric_symm reflexive_symm)
lemma preorder_symm: "preorder R\<^sup>\<smile> = preorder R" by (simp add: preorder_def reflexive_symm transitive_symm)
lemma partial_order_symm: "partial_order R\<^sup>\<smile> = partial_order R" by (simp add: antisymmetric_symm partial_order_def preorder_symm)

(*The relations subset and subrel are in fact partial_orders*)
lemma subset_partial_order: "partial_order (\<subseteq>)" 
  unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma subrel_partial_order: "partial_order (\<subseteq>\<^sup>r)"
  unfolding endorel_defs rel_defs set_defs comb_defs by blast

subsection \<open>Set-operations defined from endorelations\<close>

(*When talking about endorelations (orderings in particular) it is customary to employ the expressions
 'up' and 'down' instead of 'right' and 'left' respectively. Similarly, we use expressions
 like 'maximal'/'greatest' and 'minimal'/'least' to mean 'rightmost' and 'leftmost' respectively.*)

(*We conveniently introduce the following alternative names for left resp. right bounds/images*)
notation(input) leftBound ("lowerBound") and leftBound ("_-lowerBound")
notation(input) rightBound ("upperBound") and rightBound ("_-upperBound")
notation(input) leftImage ("downImage") and leftImage ("_-downImage")
notation(input) rightImage ("upImage") and rightImage ("_-upImage")


subsubsection \<open>Least and greatest elements\<close>

(*The set of least (leftmost) resp. greatest (rightmost) elements of a set wrt. an endorelation*)
definition least::"ERel('a) \<Rightarrow> SetEOp('a)"
  where \<open>least \<equiv> (\<^bold>S (\<inter>)) \<circ> lowerBound\<close>
definition greatest::"ERel('a) \<Rightarrow> SetEOp('a)"
  where \<open>greatest \<equiv> (\<^bold>S (\<inter>)) \<circ> upperBound\<close>

notation(input) least ("_-least") and greatest ("_-greatest") (*convenient input notation*)

lemma "R-least A = (\<lambda>m. A m \<and> (\<forall>x. A x \<rightarrow> R m x))" unfolding least_def rel_defs set_defs comb_defs ..
lemma "R-greatest A = (\<lambda>m. A m \<and> (\<forall>x. A x \<rightarrow> R x m))" unfolding greatest_def rel_defs set_defs comb_defs ..

declare least_def[endorel_defs] greatest_def[endorel_defs]

lemma greatest_defT: \<open>R-greatest = R\<^sup>\<smile>-least\<close> unfolding endorel_defs rel_defs comb_defs ..
lemma least_defT: \<open>R-least = R\<^sup>\<smile>-greatest\<close> unfolding endorel_defs rel_defs comb_defs ..


subsubsection \<open>Maximal and minimal elements\<close>

(*The set of minimal (resp. maximal) elements of a set A wrt. a relation R. *)
definition min::"ERel('a) \<Rightarrow> SetEOp('a)"
  where \<open>min \<equiv> least \<circ> lax\<close>
definition max::"ERel('a) \<Rightarrow> SetEOp('a)"
  where \<open>max \<equiv> greatest \<circ> lax\<close>

notation(input) min ("_-min") and  max ("_-max") (*convenient input notation*)

lemma "R-min A = (\<lambda>m. A m \<and> (\<forall>x. A x \<rightarrow> R\<^sup>\<flat> m x))" unfolding min_def endorel_defs rel_defs set_defs comb_defs ..
lemma "R-max A = (\<lambda>m. A m \<and> (\<forall>x. A x \<rightarrow> R\<^sup>\<flat> x m))" unfolding max_def endorel_defs rel_defs set_defs comb_defs ..

lemma \<open>R-min = (\<lambda>A. \<lambda>m. A m \<and> (\<forall>x. A x \<rightarrow> R x m \<rightarrow> R m x))\<close> unfolding min_def endorel_defs rel_defs set_defs comb_defs by auto
lemma \<open>R-max = (\<lambda>A. \<lambda>m. A m \<and> (\<forall>x. A x \<rightarrow> R m x \<rightarrow> R x m))\<close> unfolding max_def endorel_defs rel_defs set_defs comb_defs by auto

declare min_def[endorel_defs] max_def[endorel_defs]

lemma max_defT: \<open>R-max = R\<^sup>\<smile>-min\<close> unfolding endorel_defs rel_defs set_defs comb_defs ..
lemma min_defT: \<open>R-min = R\<^sup>\<smile>-max\<close> unfolding endorel_defs rel_defs set_defs comb_defs ..

(*Minimal and maximal elements generalize least and greatest elements respectively*)
lemma "R-least A \<subseteq> R-min A"
  unfolding endorel_defs rel_defs set_defs comb_defs by simp
lemma "R-greatest A \<subseteq> R-max A" 
  unfolding endorel_defs rel_defs set_defs comb_defs by simp


subsubsection \<open>Least upper- and greatest lower-bounds\<close>

(*The (set of) least upper-bound(s) and greatest lower-bound(s) for a given set*)
definition lub::"ERel('a) \<Rightarrow> SetEOp('a)"
  where "lub \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 \<^bold>B least upperBound"
definition glb::"ERel('a) \<Rightarrow> SetEOp('a)"
  where "glb \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 \<^bold>B greatest lowerBound"

notation(input) lub ("_-lub") and  glb ("_-glb") (*convenient input notation*)

lemma "R-lub S  = R-least(R-upperBound S)" unfolding lub_def endorel_defs comb_defs ..
lemma "R-glb S  = R-greatest(R-lowerBound S)" unfolding glb_def endorel_defs comb_defs ..

declare lub_def[endorel_defs] glb_def[endorel_defs]

lemma lub_defT: "R-lub = R\<^sup>\<smile>-glb" 
  unfolding endorel_defs rel_defs set_defs comb_defs ..
lemma glb_defT: "R-glb = R\<^sup>\<smile>-lub" 
  unfolding endorel_defs rel_defs set_defs comb_defs ..

(*Moreover, when it comes to upper/lower bounds, least/greatest and glb/lub elements coincide*)
lemma lub_def3: "R-lub S = R-glb (R-upperBound S)"
  unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma glb_def3: "R-glb S = R-lub (R-lowerBound S)"
  unfolding endorel_defs rel_defs set_defs comb_defs by auto

lemma lub_prop: "S \<subseteq> R-lowerBound (R-lub S)" unfolding endorel_defs rel_defs set_defs comb_defs by simp
lemma glb_prop: "S \<subseteq> R-upperBound (R-glb S)" unfolding endorel_defs rel_defs set_defs comb_defs by simp

(*Big-union resp. big-intersection of sets and relations corresponds in fact to the lub resp. glb*)
lemma bigunion_lub: "(\<subseteq>)-lub S (\<Union>S)" unfolding endorel_defs rel_defs set_defs comb_defs by blast
lemma biginter_glb: "(\<subseteq>)-glb S (\<Inter>S)" unfolding endorel_defs rel_defs set_defs comb_defs by blast
lemma bigunionR_lub:"(\<subseteq>\<^sup>r)-lub S (\<Union>\<^sup>rS)" unfolding endorel_defs rel_defs set_defs func_defs comb_defs by blast
lemma biginterR_glb: "(\<subseteq>\<^sup>r)-glb S (\<Inter>\<^sup>rS)" unfolding endorel_defs rel_defs set_defs func_defs comb_defs by blast


subsection \<open>Existence and uniqueness under antisymmetry\<close>
(*The following properties hold under the assumption that the given relation R is antisymmetric.*)

(*There can be at most one least/greatest element in a set*)
lemma antisymm_least_unique: "antisymmetric R \<Longrightarrow> !(R-least S)" 
  unfolding endorel_defs rel_defs set_defs comb_defs by simp
lemma antisymm_greatest_unique: "antisymmetric R \<Longrightarrow> !(R-greatest S)"
  unfolding endorel_defs rel_defs set_defs comb_defs by simp

(*If (the) least/greatest elements exist then they are identical to (the) min/max elements*)
lemma antisymm_least_min: "antisymmetric R \<Longrightarrow> \<exists>(R-least S) \<Longrightarrow> (R-least S) = (R-min S)" 
  unfolding endorel_defs rel_defs set_defs comb_defs by metis
lemma antisymm_greatest_max: "antisymmetric R \<Longrightarrow> \<exists>(R-greatest S) \<Longrightarrow> (R-greatest S) = (R-max S)"
  unfolding endorel_defs rel_defs set_defs comb_defs by metis

(* If (the) least/greatest elements of a set exist then they are identical to (the) glb/lub *)
lemma antisymm_least_glb: "antisymmetric R \<Longrightarrow> \<exists>(R-least S) \<Longrightarrow> (R-least S) = (R-glb S)"
  unfolding endorel_defs rel_defs set_defs comb_defs by metis
lemma antisymm_greatest_lub: "antisymmetric R \<Longrightarrow> \<exists>(R-greatest S) \<Longrightarrow> (R-greatest S) = (R-lub S)"
  unfolding endorel_defs rel_defs set_defs comb_defs by metis


subsection \<open>Well-ordering & well-foundedness\<close>

(*The property of being a well-founded/ordered relation*)
definition wellOrdered::"Set(ERel('a))" ("wellOrdered")
  where "wellOrdered \<equiv> ((\<subseteq>) \<exists>) \<circ> (\<^bold>B \<exists>) \<circ> least"
definition wellFounded::"Set(ERel('a))" ("wellFounded")
  where "wellFounded \<equiv> ((\<subseteq>) \<exists>) \<circ> (\<^bold>B \<exists>) \<circ> min"

declare wellFounded_def[endorel_defs] wellOrdered_def[endorel_defs]

lemma "wellOrdered R = (\<forall>D. \<exists>D \<rightarrow> \<exists>(R-least D))" unfolding endorel_defs set_defs comb_defs .. 
lemma "wellFounded R = (\<forall>D. \<exists>D \<rightarrow> \<exists>(R-min D))" unfolding endorel_defs set_defs comb_defs .. 

lemma "preorder R \<Longrightarrow> wellFounded R \<Longrightarrow> A \<subseteq> R-rightImage(R-min A)" oops(*TODO prove*)


subsection \<open>Limit-completeness\<close>
(*Limit-completeness is an important property of endorelations (orderings in particular). Famously,
 this is the property that characterizes the ordering of real numbers (in contrast to the rationals).*)

(*Note that existence of lubs for all sets entails existence of glbs for all sets (and viceversa)*)
lemma "\<forall>S. \<exists>(R-lub S) \<Longrightarrow> \<forall>S. \<exists>(R-glb S)" by (simp add: glb_def3)
lemma "\<forall>S. \<exists>(R-glb S) \<Longrightarrow> \<forall>S. \<exists>(R-lub S)" by (simp add: lub_def3)

(*The above results motivate the following definition: An endorelation R is called limit-complete
 when lubs/glbs (wrt R) exist for every set S (note that they must not be necessarily contained in S).*)
definition limitComplete::"Set(ERel('a))"
  where "limitComplete \<equiv> \<forall> \<circ> (\<exists> \<circ>\<^sub>2 lub)" 

lemma "limitComplete R = (\<forall>S. \<exists>(R-lub S))" unfolding limitComplete_def comb_defs ..

lemma "limitComplete R \<Longrightarrow> (R-lub S) \<subseteq> S" nitpick oops (*counterexample*)

(*Transpose/converse definitions*)
lemma limitComplete_def2: "limitComplete =  \<forall> \<circ> (\<exists> \<circ>\<^sub>2 glb)" unfolding limitComplete_def comb_defs by (metis glb_def3 lub_def3)
lemma "limitComplete R = (\<forall>S. \<exists>(R-glb S))" unfolding limitComplete_def2 comb_defs ..

lemma limitComplete_defT: "limitComplete R\<^sup>\<smile> =  limitComplete R"
  unfolding limitComplete_def2 comb_defs by (metis glb_def3 lub_def3 lub_defT)

declare limitComplete_def[endorel_defs]

(*The subset and subrelation relations are indeed limit-complete*)
lemma subset_limitComplete: "limitComplete (\<subseteq>)" unfolding limitComplete_def comb_defs using bigunion_lub by blast
lemma subrel_limitComplete: "limitComplete (\<subseteq>\<^sup>r)" unfolding limitComplete_def comb_defs using bigunionR_lub by blast


end