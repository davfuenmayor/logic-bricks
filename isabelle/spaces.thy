theory spaces (* A theory of spaces qua sets of sets *)
imports setops
begin

section \<open>Spaces as sets of sets\<close> (*TODO: provide combinator-based definitions*)

subsection \<open>Spaces as quantifiers & co.\<close>

(*Quantifiers are particular kinds of spaces.*)
term "\<forall> :: Set(Set('a))" (* \<forall> is the space that contains only the universe*)
lemma All_simp1:"{\<UU>} = \<forall>" unfolding set_defs comb_defs by auto
lemma All_simp2:"(\<subseteq>) \<UU> = \<forall>" unfolding set_defs comb_defs by simp

term "\<exists> :: Set(Set('a))" (* \<exists> is the space that contains all but the empty set*)
lemma Ex_simp1: "\<lbrace>\<emptyset>\<rbrace> = \<exists>" unfolding Ex_def set_defs comb_defs by auto 
lemma Ex_simp2: "(\<supseteq>) \<emptyset> = \<nexists>" unfolding set_defs unfolding comb_defs by simp

term "\<nexists> :: Set(Set('a))" (* \<nexists> is the space that contains only the empty set*)
lemma nonEx_simp: "{\<emptyset>} = \<nexists>" unfolding Ex_def set_defs comb_defs by auto 

(*In general, any property of sets corresponds to a space. For instance:*)
term "! :: Set(Set('a))" (* ! is the space that contains all and only univalent sets (having at most one element)*)
term "\<exists>! :: Set(Set('a))" (* ! is the space that contains all and only singleton sets*)

(*Further convenient instances of spaces*)
definition doubleton::"Set(Set('a))" ("\<exists>!\<^sub>2") (*\<exists>!! contains the doubletons (sets with two (different) elements)*)
  where \<open>\<exists>!\<^sub>2 A \<equiv> \<exists>x y. x \<noteq> y \<and> A x \<and> A y \<and> (\<forall>z. A z \<rightarrow> (z = x \<or> z = y))\<close>
definition upair::"Set(Set('a))" ("\<exists>\<^sub>\<le>\<^sub>2") (*\<exists>\<^sub>\<le>\<^sub>2 contains the unordered pairs (sets with one or two elements)*)
  where \<open>\<exists>\<^sub>\<le>\<^sub>2A \<equiv> \<exists>x y. A x \<and> A y \<and> (\<forall>z. A z \<rightarrow> (z = x \<or> z = y))\<close>

declare unique_def[set_defs] singleton_def[set_defs] doubleton_def[set_defs] upair_def[set_defs] 

lemma unique_def2: "! = \<nexists> \<union> \<exists>!" unfolding set_defs comb_defs by auto
lemma singleton_def2: "\<exists>! = \<exists> \<inter> !" unfolding set_defs comb_defs by metis
lemma doubleton_def2: "\<exists>!\<^sub>2 = \<exists>\<^sub>\<le>\<^sub>2 \<setminus> \<exists>!" unfolding set_defs comb_defs by blast
lemma upair_def2: "\<exists>\<^sub>\<le>\<^sub>2 = \<exists>! \<union> \<exists>!\<^sub>2" unfolding set_defs comb_defs by blast

lemma singleton_def3: "\<exists>!A = (\<exists>a. A = {a})" unfolding singleton_def2 set_defs comb_defs by auto
lemma doubleton_def3: "\<exists>!\<^sub>2A = (\<exists>a b. a \<noteq> b \<and> A = {a,b})" unfolding set_defs comb_defs by auto
lemma upair_def3: "\<exists>\<^sub>\<le>\<^sub>2A = (\<exists>a b. A = {a,b})" unfolding set_defs comb_defs by auto

(*Convenient abbreviation for sets that have 2 or more elements*)
abbreviation nonUnique::"Set(Set('a))" ("\<exists>\<^sub>\<ge>\<^sub>2")
  where "\<exists>\<^sub>\<ge>\<^sub>2A \<equiv> \<not>!A"

(*Sets, in general, are the bigunions of their contained singletons*)
lemma singleton_gen: "S = \<Union>(\<wp>S \<inter> \<exists>!)" unfolding singleton_def3 set_defs comb_defs by metis
(*Sets with more than one element are the bigunions of their contained doubletons*)
lemma doubleton_gen: "\<exists>\<^sub>\<ge>\<^sub>2 S \<Longrightarrow> S = \<Union>(\<wp>S \<inter> \<exists>!\<^sub>2)"  unfolding doubleton_def3 set_defs comb_defs sorry (*kernel reconstruction failed*)
(*Sets, in general, are the bigunions of their contained unordered pairs*)
lemma upair_gen: "S = \<Union>(\<wp>S \<inter> \<exists>\<^sub>\<le>\<^sub>2)" unfolding upair_def2 singleton_def3 doubleton_def3 unfolding set_defs comb_defs by metis

(*Some useful equations*)
lemma singleton_prop: "(\<forall>D. D \<subseteq> S \<rightarrow> \<exists>!D \<rightarrow> P D) = (\<forall>x. S x \<rightarrow> P {x})"
  unfolding singleton_def3 unfolding set_defs comb_defs by (metis (full_types))
lemma doubleton_prop: "(\<forall>D. D \<subseteq> S \<rightarrow> \<exists>!\<^sub>2D \<rightarrow> P D) = (\<forall>x y. S x \<and> S y \<rightarrow> x \<noteq> y \<rightarrow> P {x,y})"
  unfolding doubleton_def3 unfolding set_defs comb_defs by (smt (verit))
lemma upair_prop: "(\<forall>D. D \<subseteq> S \<rightarrow> \<exists>\<^sub>\<le>\<^sub>2D \<rightarrow> P D) = (\<forall>x y. S x \<and> S y \<rightarrow> P {x,y})" 
  unfolding upair_def3 unfolding set_defs comb_defs by (smt (verit, best))


subsection \<open>Spaces via closure under operations\<close>

(*The space of sets closed under the given unary (endo)operation*)
abbreviation(input) closedUnderOp::"EOp('a) \<Rightarrow> Set(Set('a))"
  where "closedUnderOp \<phi> \<equiv> \<lambda>S. \<forall>a. S a \<longrightarrow> S (\<phi> a)"
(*The space of sets closed under the given binary (endo)operation*)
abbreviation(input) closedUnderBinOp::"EOp\<^sub>2('a) \<Rightarrow> Set(Set('a))"
  where "closedUnderBinOp \<phi> \<equiv> \<lambda>S. \<forall>a b. S a \<and> S b \<longrightarrow> S (\<phi> a b)"
(*The space of sets closed under the given generalized (endo)operation*)
abbreviation(input) closedUnderGenOp::"EOp\<^sub>G('a) \<Rightarrow> Set(Set('a))"
  where "closedUnderGenOp \<phi> \<equiv> \<lambda>S. \<forall>D. D \<subseteq> S \<longrightarrow> S (\<phi> D)"

(*The same notation can be used for the three cases above in unambiguous contexts*)
notation closedUnderOp ("closedUnder") and closedUnderBinOp ("closedUnder") and closedUnderGenOp ("closedUnder")

(*Moreover, we can state that a set S is closed under a given (endo)operation on its subsets*)
abbreviation(input) closedUnderSetOp::"EOp(Set('a)) \<Rightarrow> Set(Set('a))" ("closedUnderSetOp")
  where "closedUnderSetOp \<phi> \<equiv> \<lambda>S. \<forall>D. D \<subseteq> S \<longrightarrow> (\<phi> D) \<subseteq> S"
(*Oftentimes, we need to restrict the quantification domain to S-subsets that satisfy a property P*)
abbreviation(input) closedUnderSetOp_restr::"Set(Set('a)) \<Rightarrow> EOp(Set('a)) \<Rightarrow> Set(Set('a))" ("closedUnderSetOp|(_)")
  where "closedUnderSetOp|P \<phi> \<equiv> \<lambda>S. \<forall>D. D \<subseteq> S \<longrightarrow> P D \<longrightarrow> (\<phi> D) \<subseteq> S"

(*It is common to restrict the quantification domain to non-empty sets. Following lemmata apply:*)
lemma "closedUnderSetOp \<phi> S \<longrightarrow> closedUnderSetOp|\<exists> \<phi> S" 
  unfolding set_defs by simp

(*Note, however that*)
lemma "\<exists>S \<Longrightarrow> (closedUnderSetOp|\<exists> \<phi> S) \<longrightarrow> closedUnderSetOp \<phi> S" nitpick oops (*counterexample*)

(*It holds, indeed, that*)
lemma closedUnderSetOp_nonEmpty: "MONO \<phi> \<Longrightarrow> \<exists>S \<Longrightarrow> closedUnderSetOp|\<exists> \<phi> S = closedUnderSetOp \<phi> S" 
  unfolding setop_defs rel_defs set_defs comb_defs by blast


subsection \<open>Spaces from endorelations\<close>
(*The following definitions correspond to functions that take an endorelation R and return the space 
 of those sets satisfying a particular property wrt. R*)


subsubsection \<open>Lub/glb-related definitions\<close>

(*These definitions generalize the "complete join/meet-semilattice" property (existence of suprema resp. infima)*)
definition lubComplete::"ERel('a) \<Rightarrow> Set(Set('a))" ("_-lubComplete")
  where "R-lubComplete \<equiv> \<lambda>S. \<forall>D. D \<subseteq> S \<longrightarrow> \<exists>(R-lub D \<inter> S)" (*all of S-subsets have a lub (wrt R) in S*)
definition glbComplete::"ERel('a) \<Rightarrow> Set(Set('a))" ("_-glbComplete")
  where "R-glbComplete \<equiv> \<lambda>S. \<forall>D. D \<subseteq> S \<longrightarrow> \<exists>(R-glb D \<inter> S)" (*all of S-subsets have a glb (wrt R) in S*)

(*The following related propertes correspond to closure under the lub resp. glb set-operation wrt R*)
definition lubClosed::"ERel('a) \<Rightarrow> Set(Set('a))" ("_-lubClosed")
  where "R-lubClosed \<equiv> closedUnderSetOp R-lub" 
definition glbClosed::"ERel('a) \<Rightarrow> Set(Set('a))" ("_-glbClosed")
  where "R-glbClosed \<equiv> closedUnderSetOp R-glb"

declare lubComplete_def[endorel_defs] glbComplete_def[endorel_defs]
        lubClosed_def[endorel_defs] glbClosed_def[endorel_defs]

lemma lubComplete_defT: "R-lubComplete = R\<^sup>\<smile>-glbComplete" unfolding endorel_defs rel_defs comb_defs ..
lemma glbComplete_defT: "R-glbComplete = R\<^sup>\<smile>-lubComplete" unfolding endorel_defs rel_defs comb_defs ..

lemma lubClosed_defT: "R-lubClosed = R\<^sup>\<smile>-glbClosed" unfolding rightBound_defT endorel_defs rel_defs comb_defs ..
lemma glbClosed_defT: "R-glbClosed = R\<^sup>\<smile>-lubClosed" unfolding leftBound_defT endorel_defs rel_defs comb_defs ..

(*Limit-completeness of a relation can be expressed in terms of either lub- or glb-completeness*)
lemma limitComplete_def3: "limitComplete R = R-lubComplete \<UU>"
  unfolding endorel_defs set_defs comb_defs by simp
lemma limitComplete_def4: "limitComplete R = R-glbComplete \<UU>"
  unfolding limitComplete_def2 endorel_defs set_defs comb_defs by simp

(*Note that lub/glb-completeness is neither monotonic nor antitonic, for instance*)
lemma "A \<subseteq> B \<Longrightarrow> R-lubComplete A \<Longrightarrow> R-lubComplete B" nitpick oops (*countermodel*)
lemma "A \<subseteq> B \<Longrightarrow> R-lubComplete B \<Longrightarrow> R-lubComplete A" nitpick oops (*countermodel*)

(*Recalling that antisymmetry entails uniqueness of lub/glb (when they exist), we have in fact*)
lemma lubComplete_lubClosed: "antisymmetric R \<Longrightarrow> R-lubComplete \<subseteq> R-lubClosed" 
  unfolding endorel_defs rel_defs set_defs comb_defs by metis
lemma glbComplete_glbClosed: "antisymmetric R \<Longrightarrow> R-glbComplete \<subseteq> R-glbClosed" 
  unfolding endorel_defs rel_defs set_defs comb_defs by metis

(*However, being closed under lub/glb does not entail existence of lub/glb*)
lemma "\<exists>S \<Longrightarrow> R-lubClosed S \<Longrightarrow>  R-lubComplete S" nitpick oops (*countermodel*)
lemma "\<exists>S \<Longrightarrow> R-glbClosed S \<Longrightarrow> R-glbComplete S" nitpick oops (*countermodel*)

(*In fact, for limit-complete relations, closure under lub/glb does entail existence of lub/glb*)
lemma lubClosed_lubComplete: "limitComplete R \<Longrightarrow> R-lubClosed \<subseteq> R-lubComplete" 
  unfolding endorel_defs set_defs comb_defs by metis
lemma glbClosed_glbComplete: "limitComplete R \<Longrightarrow> R-glbClosed \<subseteq> R-glbComplete" 
  unfolding limitComplete_def2 endorel_defs set_defs comb_defs by metis

lemma lubClosed_def2: "antisymmetric R \<Longrightarrow> limitComplete R \<Longrightarrow> R-lubComplete = R-lubClosed" 
  by (simp add: lubClosed_lubComplete lubComplete_lubClosed subset_antisymm)
lemma glbClosed_def2: "antisymmetric R \<Longrightarrow> limitComplete R \<Longrightarrow> R-glbComplete = R-glbClosed" 
  by (simp add: glbClosed_glbComplete glbComplete_glbClosed subset_antisymm)


subsubsection \<open>Upwards/downwards closed\<close>

definition upwardsClosed::"ERel('a) \<Rightarrow> Set('a) \<Rightarrow> o" ("_-upwardsClosed")
  where "R-upwardsClosed \<equiv> closedUnderSetOp (R-upImage)"
definition downwardsClosed::"ERel('a) \<Rightarrow> Set('a) \<Rightarrow> o" ("_-downwardsClosed")
  where "R-downwardsClosed \<equiv> closedUnderSetOp (R-downImage)"

declare upwardsClosed_def[endorel_defs] downwardsClosed_def[endorel_defs]

lemma upwardsClosed_defT: "R-upwardsClosed = R\<^sup>\<smile>-downwardsClosed" unfolding endorel_defs rightImage_defT ..
lemma downwardsClosed_defT: "R-downwardsClosed = R\<^sup>\<smile>-upwardsClosed" unfolding endorel_defs leftImage_defT ..

lemma upwardsClosed_def2: "R-upwardsClosed S = (\<forall>x y. R x y \<longrightarrow> S x \<longrightarrow> S y)"
  unfolding endorel_defs rel_defs set_defs comb_defs by blast
lemma downwardsClosed_def2: "R-downwardsClosed S = (\<forall>x y. R x y \<longrightarrow> S y \<longrightarrow> S x)"
  unfolding endorel_defs rel_defs set_defs comb_defs by blast

lemma upwardsClosed_def3: "skeletal R \<Longrightarrow> R-upwardsClosed S = (\<forall>D. \<exists>(R-glb D) \<longrightarrow> (R-glb D) \<subseteq> S  \<longrightarrow> D \<subseteq> S)"
  unfolding upwardsClosed_def endorel_defs rel_defs set_defs comb_defs sorry (*reconstr fails*)
lemma downwardsClosed_def3: "skeletal R \<Longrightarrow> R-downwardsClosed S = (\<forall>D. \<exists>(R-lub D) \<longrightarrow> (R-lub D) \<subseteq> S  \<longrightarrow> D \<subseteq> S)"
  by (simp add: downwardsClosed_defT lub_defT skeletal_symm upwardsClosed_def3)

lemma upwardsClosed_def4: "skeletal R \<Longrightarrow> limitComplete R \<Longrightarrow> R-upwardsClosed S = (\<forall>D. (R-glb D) \<subseteq> S \<longrightarrow> D \<subseteq> S)"  
  unfolding upwardsClosed_def3 limitComplete_def2 comb_defs by simp
lemma downwardsClosed_def4: "skeletal R \<Longrightarrow> limitComplete R \<Longrightarrow> R-downwardsClosed S = (\<forall>D. (R-lub D) \<subseteq> S \<longrightarrow> D \<subseteq> S)"  
  by (simp add: downwardsClosed_defT limitComplete_defT lub_defT skeletal_symm upwardsClosed_def4)


subsubsection \<open>Greatest/least existence\<close>

(*Another interesting property is existence of greatest resp. least elements*)
definition greatestExist::"ERel('a) \<Rightarrow> Set(Set('a))" ("_-greatestExist")
  where "R-greatestExist \<equiv> \<lambda>S. \<exists>(R-greatest S)"
definition leastExist::"ERel('a) \<Rightarrow> Set(Set('a))" ("_-leastExist")
  where "R-leastExist \<equiv> \<lambda>S. \<exists>(R-least S)"

declare greatestExist_def[endorel_defs] leastExist_def[endorel_defs]

(*In fact, recalling that...*)
lemma "R-greatest S = (S \<inter> R-upperBound S)" unfolding greatest_def comb_defs ..
lemma "R-least S = (S \<inter> R-lowerBound S)" unfolding least_def comb_defs ..

lemma greatestExist_defT: "R-greatestExist = R\<^sup>\<smile>-leastExist" unfolding rightBound_defT endorel_defs comb_defs ..
lemma leastExist_defT: "R-leastExist = R\<^sup>\<smile>-greatestExist" unfolding leftBound_defT endorel_defs comb_defs ..

(*... we have that existence of greatest/least elements for S is equivalent to every S-subset having 
 upper/lower bounds (wrt R) in S. (Note that this is a strong variant of up/downwards directedness.)*)
lemma greatestExist_def2: "R-greatestExist S = (\<forall>D. D \<subseteq> S \<longrightarrow> \<exists>(S \<inter> R-upperBound D))"
  unfolding greatestExist_def endorel_defs rel_defs set_defs comb_defs by auto
lemma leastExist_def2:    "R-leastExist S    = (\<forall>D. D \<subseteq> S \<longrightarrow> \<exists>(S \<inter> R-lowerBound D))"
  unfolding leastExist_def endorel_defs rel_defs set_defs comb_defs by auto

(*or, alternatively*) 
lemma greatestExist_def3: "R-greatestExist S = (\<exists>S \<and> (\<forall>D. D \<subseteq> S \<longrightarrow> \<exists>D \<longrightarrow> \<exists>(S \<inter> R-upperBound D)))"
  unfolding greatestExist_def2 rel_defs set_defs comb_defs by auto
lemma leastExist_def3:    "R-leastExist S    = (\<exists>S \<and> (\<forall>D. D \<subseteq> S \<longrightarrow> \<exists>D \<longrightarrow> \<exists>(S \<inter> R-lowerBound D)))"
  unfolding leastExist_def2  rel_defs set_defs comb_defs by auto (*TODO: compare with well-ordered*)

(*In fact, existence of greatest/least-elements is a strictly weaker property than lub/glb-completeness*)
lemma glbComplete_least: "R-glbComplete \<subseteq> R-leastExist" 
  unfolding endorel_defs set_defs comb_defs by auto
lemma lubComplete_greatest: "R-lubComplete \<subseteq> R-greatestExist"
  unfolding endorel_defs set_defs comb_defs by auto
lemma "R-greatestExist \<subseteq> R-lubComplete" nitpick oops (*countermodel*)
lemma "R-leastExist \<subseteq> R-glbComplete" nitpick oops (*countermodel*)

lemma greatestExist_lubClosed: "R-downwardsClosed S \<Longrightarrow> R-greatestExist S \<Longrightarrow> R-lubClosed S"
  unfolding endorel_defs rel_defs set_defs comb_defs by blast
lemma leastExist_glbClosed: "R-upwardsClosed S \<Longrightarrow> R-leastExist S \<Longrightarrow> R-glbClosed S"
  unfolding endorel_defs rel_defs set_defs comb_defs by blast

lemma greatestExist_def4: "limitComplete R \<Longrightarrow> R-downwardsClosed S \<Longrightarrow> R-greatestExist S = R-lubClosed S"
  using greatestExist_lubClosed lubClosed_lubComplete lubComplete_greatest unfolding set_defs comb_defs by metis
lemma leastExist_def4: "limitComplete R \<Longrightarrow> R-upwardsClosed S \<Longrightarrow> R-leastExist S = R-glbClosed S"
  by (simp add: glbClosed_defT greatestExist_def4 leastExist_defT limitComplete_defT upwardsClosed_defT)


subsubsection \<open>Up-/downwards directedness\<close>

(*The property of a set being 'up/downwards directed' wrt. an endorelation:
  Every pair of S-elements has upper/lower-bounds (wrt R) in S *)
definition upwardsDirected::"ERel('a) \<Rightarrow> Set(Set('a))" ("_-upwardsDirected")
  where "R-upwardsDirected   \<equiv> \<lambda>S. \<forall>a b. S a \<and> S b \<longrightarrow> (\<exists>c. S c \<and> R a c \<and> R b c)"
definition downwardsDirected::"ERel('a) \<Rightarrow> Set(Set('a))" ("_-downwardsDirected")
  where "R-downwardsDirected \<equiv> \<lambda>S. \<forall>a b. S a \<and> S b \<longrightarrow> (\<exists>c. S c \<and> R c a \<and> R c b)"

declare upwardsDirected_def[endorel_defs] downwardsDirected_def[endorel_defs]

lemma upwardsDirected_defT: "R-upwardsDirected = R\<^sup>\<smile>-downwardsDirected" unfolding endorel_defs rel_defs comb_defs ..
lemma downwardsDirected_defT: "R-downwardsDirected = R\<^sup>\<smile>-upwardsDirected" unfolding endorel_defs rel_defs comb_defs ..

(*The definition above can be rephrased as*)
lemma upwardsDirected_def2: "R-upwardsDirected S = (\<forall>a b. S a \<and> S b \<longrightarrow> \<exists>(S \<inter> R-upperBound {a,b}))" 
  unfolding endorel_defs rel_defs set_defs comb_defs by metis
lemma downwardsDirected_def2: "R-downwardsDirected S = (\<forall>a b. S a \<and> S b \<longrightarrow> \<exists>(S \<inter> R-lowerBound {a,b}))" 
  unfolding endorel_defs rel_defs set_defs comb_defs by metis
(*or, alternatively*)
lemma upwardsDirected_def3:  "R-upwardsDirected S = (\<forall>D. D \<subseteq> S \<longrightarrow> \<exists>\<^sub>\<le>\<^sub>2D \<longrightarrow> \<exists>(S \<inter> R-upperBound D))"
  unfolding upwardsDirected_def2 unfolding upair_prop ..
lemma downwardsDirected_def3:  "R-downwardsDirected S = (\<forall>D. D \<subseteq> S \<longrightarrow> \<exists>\<^sub>\<le>\<^sub>2D \<longrightarrow> \<exists>(S \<inter> R-lowerBound D))"
  unfolding downwardsDirected_def2 unfolding upair_prop ..

(*Note that up/downwards directedness does not entail non-emptyness of S*)
lemma "R-upwardsDirected S \<longrightarrow> \<exists>S" nitpick oops (*counterexample*)
lemma "R-downwardsDirected S \<longrightarrow> \<exists>S" nitpick oops (*counterexample*)


subsubsection \<open>Join- and meet-closure\<close>

(*Convenient abbreviations*)
abbreviation(input) join ("_-join")
  where "R-join a b \<equiv> R-lub {a,b}"
abbreviation(input) meet ("_-meet")
  where "R-meet a b \<equiv> R-glb {a,b}"

lemma join_prop1:  "R-lowerBound (R-join a b) a" unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma join_prop2:  "R-lowerBound (R-join a b) b" unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma meet_prop1:  "R-upperBound (R-meet a b) a" unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma meet_prop2:  "R-upperBound (R-meet a b) b" unfolding endorel_defs rel_defs set_defs comb_defs by auto

(*The following are weaker versions of lub/glb-closure customarily used in the literature*)
definition joinClosed::"ERel('a) \<Rightarrow> Set(Set('a))" ("_-joinClosed")
  where "R-joinClosed \<equiv> \<lambda>S. \<forall>a b. S a \<and> S b \<longrightarrow> R-join a b \<subseteq> S"
definition meetClosed::"ERel('a) \<Rightarrow> Set(Set('a))" ("_-meetClosed")
  where "R-meetClosed \<equiv> \<lambda>S. \<forall>a b. S a \<and> S b \<longrightarrow> R-meet a b \<subseteq> S"

declare joinClosed_def[endorel_defs] meetClosed_def[endorel_defs]

lemma joinClosed_defT: "R-joinClosed = R\<^sup>\<smile>-meetClosed" unfolding endorel_defs rel_defs comb_defs ..
lemma meetClosed_defT: "R-meetClosed = R\<^sup>\<smile>-joinClosed" unfolding endorel_defs rel_defs comb_defs ..

lemma joinClosed_def2: "joinClosed R S = (\<forall>p. p \<subseteq> S \<rightarrow> \<exists>\<^sub>\<le>\<^sub>2 p \<rightarrow> (R-lub p) \<subseteq> S)" 
  unfolding joinClosed_def upair_prop ..
lemma meetClosed_def2: "meetClosed R S = (\<forall>p. p \<subseteq> S \<rightarrow> \<exists>\<^sub>\<le>\<^sub>2 p \<rightarrow> (R-glb p) \<subseteq> S)" 
  unfolding meetClosed_def upair_prop ..

lemma joinClosed_upwardsDirected: "limitComplete R \<Longrightarrow> R-joinClosed S \<Longrightarrow> R-upwardsDirected S"
 unfolding limitComplete_def joinClosed_def2 upwardsDirected_def3 lub_def least_def set_defs comb_defs by metis
lemma meetClosed_downwardsDirected: "limitComplete R \<Longrightarrow> R-meetClosed S \<Longrightarrow> R-downwardsDirected S"
   by (simp add: downwardsDirected_defT joinClosed_upwardsDirected limitComplete_defT meetClosed_defT)

(*Thus we have*)
lemma greatestExist_upwardsDirected: "R-greatestExist S \<Longrightarrow> R-upwardsDirected S" 
  unfolding greatestExist_def3 upwardsDirected_def3 set_defs comb_defs by auto
lemma leastExist_downwardsDirected: "R-leastExist S \<Longrightarrow> R-downwardsDirected S" 
  by (simp add: downwardsDirected_defT greatestExist_upwardsDirected leastExist_defT)
(*However*)
lemma "\<exists>S \<Longrightarrow> R-upwardsDirected S \<Longrightarrow> R-greatestExist S" nitpick[card 'a=3] oops (*counterexample*)
lemma "\<exists>S \<Longrightarrow> R-downwardsDirected S \<Longrightarrow> R-leastExist S" nitpick[card 'a=3] oops (*counterexample*)

lemma downwardsDirected_meetClosed: "R-upwardsClosed S \<Longrightarrow> R-downwardsDirected S \<Longrightarrow> R-meetClosed S"
  unfolding meetClosed_def2 endorel_defs rel_defs set_defs comb_defs by fast
lemma upwardsDirected_joinClosed: "R-downwardsClosed S \<Longrightarrow> R-upwardsDirected S \<Longrightarrow> R-joinClosed S"
  by (simp add: downwardsClosed_defT downwardsDirected_meetClosed joinClosed_defT upwardsDirected_defT)

lemma downwardsDirected_def4: "limitComplete R \<Longrightarrow> R-upwardsClosed S \<Longrightarrow> R-downwardsDirected S = R-meetClosed S"
  using downwardsDirected_meetClosed meetClosed_downwardsDirected by blast
lemma upwardsDirected_def4: "limitComplete R \<Longrightarrow> R-downwardsClosed S \<Longrightarrow> R-upwardsDirected S = R-joinClosed S"
  using joinClosed_upwardsDirected upwardsDirected_joinClosed by blast


subsubsection \<open>Ideals and Filters\<close>

definition pseudoFilter::"ERel('a) \<Rightarrow> Set(Set('a))" ("_-pseudoFilter")
  where "R-pseudoFilter \<equiv> \<lambda>S. \<forall>a b. R-meet a b \<subseteq> S \<longrightarrow> (S a \<and> S b)"
definition pseudoIdeal::"ERel('a) \<Rightarrow> Set(Set('a))" ("_-pseudoIdeal")
  where "R-pseudoIdeal  \<equiv> \<lambda>S. \<forall>a b. R-join a b \<subseteq> S \<longrightarrow> (S a \<and> S b)"

declare pseudoFilter_def[endorel_defs] pseudoIdeal_def[endorel_defs]

lemma pseudoFilter_defT: "R-pseudoFilter = R\<^sup>\<smile>-pseudoIdeal" unfolding endorel_defs rel_defs comb_defs ..
lemma pseudoIdeal_defT: "R-pseudoIdeal = R\<^sup>\<smile>-pseudoFilter" unfolding endorel_defs rel_defs comb_defs ..

lemma pseudoFilter_upwardsClosed: "skeletal R \<Longrightarrow> R-pseudoFilter S \<Longrightarrow> R-upwardsClosed S" 
  unfolding endorel_defs rel_defs set_defs comb_defs by (smt (verit, del_insts))
lemma pseudoIdeal_downwardsClosed: "skeletal R \<Longrightarrow> R-pseudoIdeal S \<Longrightarrow> R-downwardsClosed S" 
  unfolding endorel_defs rel_defs set_defs comb_defs by (smt (verit, del_insts))

lemma upwardsClosed_pseudoFilter: "limitComplete R \<Longrightarrow> R-upwardsClosed S \<Longrightarrow> R-pseudoFilter S"
  sorry (*TODO: proven by external systems but internal reconstruction fails*)
lemma downwardsClosed_pseudoIdeal: "limitComplete R \<Longrightarrow> R-downwardsClosed S \<Longrightarrow> R-pseudoIdeal S"
  by (simp add: downwardsClosed_defT limitComplete_defT pseudoIdeal_defT upwardsClosed_pseudoFilter)

lemma pseudoFilter_def2: "skeletal R \<Longrightarrow> limitComplete R \<Longrightarrow> R-pseudoFilter S = R-upwardsClosed S" 
  using pseudoFilter_upwardsClosed upwardsClosed_pseudoFilter by blast
lemma pseudoIdeal_def2: "skeletal R \<Longrightarrow> limitComplete R \<Longrightarrow> R-pseudoIdeal S = R-downwardsClosed S"
  using downwardsClosed_pseudoIdeal pseudoIdeal_downwardsClosed by blast


(*The following notions abstract the order-theoretical property of filter/ideal towards relations in
 general: S is a filter/ideal when all and only pairs of S-elements have their meet/join (wrt R) in S*)
abbreviation(input) filter::"ERel('a) \<Rightarrow> Set(Set('a))" ("_-filter")
  where "R-filter S \<equiv> R-pseudoFilter S \<and> R-meetClosed S"
abbreviation(input) ideal::"ERel('a) \<Rightarrow> Set(Set('a))" ("_-ideal")
  where "R-ideal S  \<equiv> R-pseudoIdeal S \<and> R-joinClosed S"

lemma filter_defT: "R-filter S = R\<^sup>\<smile>-ideal S" by (simp add: meetClosed_defT pseudoFilter_defT)
lemma ideal_defT: "R-ideal S = R\<^sup>\<smile>-filter S"  by (simp add: joinClosed_defT pseudoIdeal_defT)

lemma filter_char: "R-filter S = (\<forall>a b. R-meet a b \<subseteq> S \<longleftrightarrow> S a \<and> S b)" 
  unfolding meetClosed_def pseudoFilter_def by auto
lemma ideal_char: "R-ideal S = (\<forall>a b. R-join a b \<subseteq> S \<longleftrightarrow> S a \<and> S b)" 
  unfolding joinClosed_def pseudoIdeal_def by auto

lemma filter_prop1: "limitComplete R \<Longrightarrow> R-upwardsClosed S \<Longrightarrow> R-downwardsDirected S \<Longrightarrow> R-filter S"
  using downwardsDirected_def4 upwardsClosed_pseudoFilter by blast
lemma filter_prop2: "limitComplete R \<Longrightarrow> R-filter S \<Longrightarrow> R-downwardsDirected S" 
  using meetClosed_downwardsDirected by blast
lemma filter_prop3: "partial_order R \<Longrightarrow> limitComplete R \<Longrightarrow> R-filter S \<Longrightarrow> R-upwardsClosed S" 
  using partial_order_def2 pseudoFilter_def2 by blast

lemma ideal_prop1: "limitComplete R \<Longrightarrow> R-downwardsClosed S \<Longrightarrow> R-upwardsDirected S \<Longrightarrow> R-ideal S" 
  by (simp add: downwardsClosed_pseudoIdeal upwardsDirected_joinClosed)
lemma ideal_prop2: "limitComplete R \<Longrightarrow> R-ideal S \<Longrightarrow> R-upwardsDirected S"
  by (simp add: joinClosed_upwardsDirected)
lemma ideal_prop3: "partial_order R \<Longrightarrow> limitComplete R \<Longrightarrow> R-ideal S \<Longrightarrow> R-downwardsClosed S" 
  using partial_order_def2 pseudoIdeal_def2 by blast

lemma filter_def2: "partial_order R \<Longrightarrow> limitComplete R \<Longrightarrow> R-filter = (R-upwardsClosed \<inter> R-downwardsDirected)"
  unfolding set_defs  comb_defs by (metis filter_prop1 filter_prop2 filter_prop3)
lemma ideal_def2: "partial_order R \<Longrightarrow> limitComplete R \<Longrightarrow> R-ideal = (R-downwardsClosed \<inter> R-upwardsDirected)" 
  unfolding set_defs  comb_defs by (metis ideal_prop1 ideal_prop2 ideal_prop3)


subsubsection \<open>Well-founded and well-ordered sets\<close>

(*Well-foundedness of sets wrt. a given relation (as in "Nat is well-founded wrt. < ")*)
definition wellFoundedSet::"ERel('a) \<Rightarrow> Set(Set('a))" ("_-wellFoundedSet")
  where "wellFoundedSet \<equiv> \<^bold>B\<^sub>1\<^sub>1 (\<supseteq>) (\<exists> \<circ>\<^sub>2 min) (((\<inter>) \<exists>) \<circ> (\<supseteq>))" (*TODO: simplify?*)
definition wellOrderedSet::"ERel('a) \<Rightarrow> Set(Set('a))" ("_-wellOrderedSet")
  where "wellOrderedSet \<equiv> \<^bold>B\<^sub>1\<^sub>1 (\<supseteq>) (\<exists> \<circ>\<^sub>2 least) (((\<inter>) \<exists>) \<circ> (\<supseteq>))" (*TODO: simplify?*) 

declare wellFoundedSet_def[endorel_defs] wellOrderedSet_def[endorel_defs]

lemma "R-wellFoundedSet S = (\<forall>D. D \<subseteq> S \<longrightarrow> \<exists>D \<longrightarrow> \<exists>(R-min D))" (*every non-empty S-subset S has min elements (in D)*)
  unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma "R-wellOrderedSet S = (\<forall>D. D \<subseteq> S \<longrightarrow> \<exists>D \<longrightarrow> \<exists>(R-least D))" (*every non-empty S-subset D has least elements (in D)*)
  unfolding endorel_defs rel_defs set_defs comb_defs by auto

(*As expected*)
lemma "wellFounded R = R-wellFoundedSet \<UU>" unfolding endorel_defs rel_defs set_defs comb_defs by simp
lemma "wellOrdered R = R-wellOrderedSet \<UU>" unfolding endorel_defs rel_defs set_defs comb_defs by simp

(*For non-empty sets, well-orderedness entails existence of least elements (but not the other way round)*)
lemma "\<exists>S \<Longrightarrow> R-wellOrderedSet S \<Longrightarrow> R-leastExist S" unfolding endorel_defs set_defs comb_defs by simp
lemma "\<exists>S \<Longrightarrow> R-leastExist S \<Longrightarrow> R-wellOrderedSet S" nitpick oops (*countermodel*)

lemma "(\<subseteq>)-wellFoundedSet {{1::nat},{2},{1,2}}" 
  unfolding endorel_defs rel_defs endorel_defs set_defs comb_defs by (smt (verit, best))
lemma "\<not> (\<subseteq>)-wellOrderedSet {{1::nat},{2},{1,2}}" 
  unfolding endorel_defs rel_defs set_defs comb_defs oops (*TODO: this used to work - fix*)

end