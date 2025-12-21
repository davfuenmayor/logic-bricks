theory AF
imports "../../induction" "HOL-Eisbach.Eisbach"
begin

section \<open>Argumentation Frameworks\<close>

named_theorems af_defs

text \<open>We start by implementing a custom prover for this theory (called "them" for "theory-method").
Current implementation is very brute! It consists of mindless definition-unfolding followed by
 invocation of ground HOL-provers (extensionality is applied in between, if no success at first).
 A decent implementation shall unfold definitions gradually and call custom methods at each layer.\<close>
method skip = (tactic \<open>all_tac\<close>)
method them = (unfold af_defs ind_defs endorel_defs rel_defs func_defs comb_defs) ;
              (auto | meson| metis) ; (((rule ext)+)?) ; (meson | metis)


subsection \<open>Basic Notions\<close>

text \<open>Given a set of arguments A, we have the set of its attacked resp. attacking arguments.\<close>
abbreviation(input) attacked :: \<open>ERel('a) \<Rightarrow> SetEOp('a)\<close> ("_-attacked") 
  where "R-attacked \<equiv> rightImage R"
abbreviation(input) attacking :: \<open>ERel('a) \<Rightarrow> SetEOp('a)\<close> ("_-attacking") 
  where "R-attacking \<equiv> leftImage R"

lemma \<open>R-attacked A  = (\<lambda>b. \<exists>a. A a \<and> a \<leadsto> b)\<close> for R (infix "\<leadsto>" 99) by them
lemma \<open>R-attacking A = (\<lambda>b. \<exists>a. A a \<and> b \<leadsto> a)\<close> for R (infix "\<leadsto>" 99) by them


text \<open>All arguments in B are attacked by (some argument in) A\<close>
abbreviation(input) mobAttack :: "ERel('a) \<Rightarrow> ERel(Set('a))" ("_-mobAttacks")
  where "R-mobAttacks \<equiv> relLiftAE_right R"

lemma \<open>R-mobAttacks A B = B \<subseteq> R-attacked A\<close> by them
lemma \<open>R-mobAttacks A B = (\<forall>b. B b \<rightarrow> R-attacked A b)\<close> by them

text \<open>Unsurprisingly, a set of arguments A mob-attacks the set of its attacked arguments.\<close>
lemma "R-mobAttacks A (R-attacked A)" by them
text \<open>The set of A's attacked arguments is actually the largest set which is mob-attacked by A.\<close>
lemma "R-attacked A = \<Union>(R-mobAttacks A)" unfolding rightImage_def3 by them


text \<open>A set A defends an argument b when every argument that attacks b is attacked by A.\<close>
definition defense :: \<open>ERel('a) \<Rightarrow> SetEOp('a)\<close> ("_-defends")
  where \<open>R-defends A \<equiv> \<lambda>b. (R\<^sup>\<smile> b \<subseteq> R-attacked A)\<close>

declare defense_def[af_defs]

lemma "R-defends A b = (\<forall>c. R c b \<longrightarrow> (\<exists>a. A a \<and> R a c))" by them
lemma "R-defends A = (\<lambda>b. R-attacking {b} \<subseteq> R-attacked A)" by them

text \<open>The "defends" function is monotonic wrt. subset relation\<close>
lemma defends_MONO: "(\<subseteq>)-MONO R-defends" by them

text \<open>We now conveniently introduce a notion of mob-defense\<close>
definition mobDefense :: \<open>ERel('a) \<Rightarrow> ERel(Set('a))\<close> ("_-mobDefends")
  where \<open>R-mobDefends A B \<equiv> R-mobAttacks A (R-attacking B)\<close>

declare mobDefense_def[af_defs]

lemma "R-mobDefends A B = R-attacking B \<subseteq> R-attacked A" by them
lemma mobDefense_defH: "R-mobDefends A B = (\<forall>c. (\<exists>b. B b \<and> R c b) \<longrightarrow> (\<exists>a. A a \<and> R a c))" by them

text \<open>Unsurprisingly, a set of arguments A mob-defends the set of its defended arguments.\<close>
lemma "R-mobDefends A (R-defends A)" by them
text \<open>The set of A's defended arguments is actually the largest set which is mob-defended by A.\<close>
lemma defense_def2: "R-defends A = \<Union>(R-mobDefends A)" sorry (*TODO: fix kernel reconstruction*)

text \<open>Interestingly (although transitivity makes little sense for an attack relation).\<close>
lemma "transitive R \<Longrightarrow> transitive (R-mobAttacks)" unfolding transitive_def2 unfolding rel_defs func_defs comb_defs by meson
lemma "transitive R \<Longrightarrow> transitive (R-mobDefends)" unfolding transitive_def2 unfolding af_defs rel_defs func_defs comb_defs by meson


subsection \<open>Extensions\<close>

text \<open>A set S is "conflict-free" when it does not contain a pair of arguments a and b such that a attacks b.\<close>
definition conflictfreeness :: \<open>ERel('a) \<Rightarrow> Space('a)\<close> ("_-conflictfree")
  where \<open>conflictfreeness = relativeInterior \<ggreater> \<^bold>W \<ggreater> FP\<close>

declare conflictfreeness_def[af_defs]

lemma "R-conflictfree S = (S = relativeInterior R S S)" by them
lemma cf_simp: \<open>R-conflictfree S = (\<forall>a b. S a \<and> S b \<longrightarrow> \<not>R a b)\<close> by them

lemma conflictfreeness_def2: "conflictfreeness =  relativeBorder \<ggreater> \<^bold>W \<ggreater>\<^sub>2 \<nexists>" by them
lemma "R-conflictfree S = (relativeBorder R S S = \<emptyset>)" by them


text \<open>A set of arguments S is "admissible" when it is conflict-free and mob-defends itself.\<close>
definition admissibility :: \<open>ERel('a) \<Rightarrow> Space('a)\<close> ("_-admissible")
  where \<open>R-admissible S \<equiv> R-conflictfree S \<and> R-mobDefends S S\<close>

declare admissibility_def[af_defs]

lemma "R-admissible = R-conflictfree \<inter> \<^bold>W (R-mobDefends)" by them
lemma \<open>R-admissible S = (R-conflictfree S \<and> (\<forall>a. S a \<longrightarrow> R-defends S a))\<close> by them
lemma \<open>R-admissible S = (R-conflictfree S \<and> (S \<subseteq> R-defends S))\<close> by them
lemma admissibility_def2: \<open>R-admissible S = (R-conflictfree S \<and> (\<subseteq>)-postFP (R-defends) S)\<close> by them

text \<open>Dung's "fundamental lemma"\<close>
lemma FL: "R-admissible S \<Longrightarrow> R-defends S a \<Longrightarrow> R-admissible (insert a S)" by them
lemma "(\<subseteq>)-MONO R-defends" by them

lemma empty_admissible: "R-admissible \<emptyset>" by them

text \<open>Complete extensions can be defined as conflict-free fixed points of "defense".\<close>
definition completeExtension :: \<open>ERel('a) \<Rightarrow> Space('a)\<close> ("_-completeExt")
  where \<open>R-completeExt S \<equiv> R-conflictfree S \<and> FP (R-defends) S\<close>

declare completeExtension_def[af_defs]

text \<open>An admissible set S becomes a complete extension if S also contains each argument S defends.\<close>
lemma completeExtension_def2: \<open>R-completeExt S = (R-admissible S \<and> (\<forall>a. R-defends S a \<longrightarrow> S a))\<close> by them

text \<open>The grounded extension is the unique least fixed-point of the "defends" operation ([Dung 1995] Def. 20).\<close>
definition groundedExtension :: \<open>ERel('a) \<Rightarrow> Set('a)\<close> ("_-groundedExt")
  where \<open>R-groundedExt \<equiv> \<mu> (R-defends)\<close>

declare groundedExtension_def[af_defs]

lemma groundedExtension_def2: \<open>R-groundedExt = \<iota>((\<subseteq>)-lfp (R-defends))\<close>
  by (simp add: defends_MONO groundedExtension_def setMu_def2)

text \<open>The grounded extension is conflict-free.\<close>
lemma grounded_cf: "R-conflictfree (R-groundedExt)" oops (*TODO: check*)

text \<open>The grounded extension is a (unique) subset-minimal complete extension.\<close>
lemma \<open>groundedExtension R = \<iota> ((completeExtension \<ggreater> (\<subseteq>)-least) R)\<close> oops (*TODO: check*)
lemma \<open>(completeExtension \<ggreater> (\<subseteq>)-least) R (groundedExtension R)\<close> oops (*TODO: check*)

text \<open>A preferred extension is a subset-maximal complete extension.\<close>
definition preferredExtension :: \<open>ERel('a) \<Rightarrow> Space('a)\<close> ("_-groundedExt")
  where \<open>preferredExtension \<equiv> completeExtension \<ggreater> (\<subseteq>)-max\<close>

text \<open>Alternatively, preferred extensions can be defined as subset-maximal admissible sets ([Dung 1995] Def. 7)\<close>
lemma "preferredExtension = admissibility \<ggreater> (\<subseteq>)-max" oops (*TODO: check*)

end