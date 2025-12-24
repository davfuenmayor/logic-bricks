section \<open>Spaces\<close>
text \<open>Spaces are sets of sets (of ... "points"). They are the main playground of mathematicians.\<close>

theory spaces (* A theory of spaces qua sets of sets *)
imports endorelations
begin

named_theorems space_defs

subsection \<open>Spaces as Quantifiers and co.\<close>

text \<open>Quantifiers are particular kinds of spaces.\<close>
term "\<forall> :: Space('a)" \<comment> \<open>\<open>\<forall>\<close> is the space that contains only the universe\<close>
lemma All_simp1:"{\<UU>} = \<forall>" unfolding func_defs comb_defs by auto
lemma All_simp2:"(\<subseteq>) \<UU> = \<forall>" unfolding func_defs comb_defs by simp

term "\<exists> :: Space('a)" \<comment> \<open>\<open>\<exists>\<close> is the space that contains all but the empty set\<close>
lemma Ex_simp1: "\<lbrace>\<emptyset>\<rbrace> = \<exists>" unfolding Ex_def func_defs comb_defs by auto 
lemma Ex_simp2: "(\<supseteq>) \<emptyset> = \<nexists>" unfolding func_defs unfolding comb_defs by simp

term "\<nexists> :: Space('a)"  \<comment> \<open>\<open>\<nexists>\<close> is the space that contains only the empty set\<close>
lemma nonEx_simp: "{\<emptyset>} = \<nexists>" unfolding Ex_def func_defs comb_defs by auto 

text \<open>In general, any property of sets corresponds to a space. For instance:\<close>
term "unique :: Space('a)" \<comment> \<open>unique is the space that contains all and only univalent sets (having at most one element)\<close>
term "\<exists>! :: Space('a)" \<comment> \<open>\<open>\<exists>!\<close> is the space that contains all and only singleton sets\<close>

lemma unique_def2: "unique = \<nexists> \<union> \<exists>!" unfolding func_defs comb_defs by auto
lemma singleton_def2: "\<exists>! = \<exists> \<inter> unique" unfolding func_defs comb_defs by metis
lemma singleton_def3: "\<exists>!A = (\<exists>a. A = {a})" unfolding singleton_def2 func_defs comb_defs by auto

text \<open>Further convenient instances of spaces.\<close>
definition upair::"Space('a)" ("\<exists>\<^sub>\<le>\<^sub>2") \<comment> \<open>\<open>\<exists>\<^sub>\<le>\<^sub>2\<close> contains the unordered pairs (sets with one or two elements)\<close>
  where \<open>\<exists>\<^sub>\<le>\<^sub>2 \<equiv> (\<^bold>\<Phi>\<^sub>2\<^sub>1 (\<inter>\<^sup>2) (\<^bold>W (\<times>)) (\<^bold>R\<^sub>3 \<^bold>E (\<^bold>\<Psi>\<^sub>2\<^sub>1 (\<union>) \<Q>) (\<subseteq>))) \<ggreater> \<exists>\<^sup>2\<close>
definition doubleton::"Space('a)" ("\<exists>!\<^sub>2") \<comment> \<open>\<open>\<exists>!\<^sub>2\<close> contains the doubletons (sets with two (different) elements)\<close>
  where \<open>\<exists>!\<^sub>2 \<equiv> \<exists>\<^sub>\<le>\<^sub>2 \<setminus> \<exists>!\<close>

declare unique_def[space_defs] singleton_def[space_defs] doubleton_def[space_defs] upair_def[space_defs] 

lemma "\<exists>\<^sub>\<le>\<^sub>2A = \<exists>\<^sup>2((A \<times> A) \<inter>\<^sup>2 (\<lambda>x y. A \<subseteq> {x,y}))" unfolding space_defs comb_defs ..
lemma doubleton_def2: "\<exists>\<^sub>\<le>\<^sub>2A = (\<exists>x y. A x \<and> A y \<and> (\<forall>z. A z \<rightarrow> (z = x \<or> z = y)))" unfolding space_defs rel_defs func_defs comb_defs by auto

lemma \<open>\<exists>!\<^sub>2 A = (\<exists>x y. x \<noteq> y \<and> A x \<and> A y \<and> (\<forall>z. A z \<rightarrow> (z = x \<or> z = y)))\<close> unfolding space_defs rel_defs func_defs comb_defs by blast
lemma upair_def2: "\<exists>\<^sub>\<le>\<^sub>2 = \<exists>! \<union> \<exists>!\<^sub>2" unfolding space_defs func_defs rel_defs comb_defs by blast

lemma doubleton_def3: "\<exists>!\<^sub>2A = (\<exists>a b. a \<noteq> b \<and> A = {a,b})" unfolding space_defs rel_defs func_defs comb_defs by blast
lemma upair_def3: "\<exists>\<^sub>\<le>\<^sub>2A = (\<exists>a b. A = {a,b})" unfolding space_defs rel_defs func_defs comb_defs by metis


text \<open>Convenient abbreviation for sets that have 2 or more elements.\<close>
abbreviation(input) nonUnique::"Space('a)" ("\<exists>\<^sub>\<ge>\<^sub>2")
  where "\<exists>\<^sub>\<ge>\<^sub>2A \<equiv> \<not>(unique A)"

text \<open>Sets, in general, are the bigunions of their contained singletons.\<close>
lemma singleton_gen: "S = \<Union>(\<wp>S \<inter> \<exists>!)" unfolding singleton_def3 func_defs comb_defs by metis
text \<open>Sets with more than one element are the bigunions of their contained doubletons.\<close>
lemma doubleton_gen: "\<exists>\<^sub>\<ge>\<^sub>2 S \<Longrightarrow> S = \<Union>(\<wp>S \<inter> \<exists>!\<^sub>2)"  unfolding doubleton_def3 func_defs comb_defs apply auto apply (rule ext)+ by (smt (verit, best))
text \<open>Sets, in general, are the bigunions of their contained unordered pairs.\<close>
lemma upair_gen: "S = \<Union>(\<wp>S \<inter> \<exists>\<^sub>\<le>\<^sub>2)" unfolding upair_def2 singleton_def3 doubleton_def3 unfolding func_defs comb_defs by metis

text \<open>Some useful equations:\<close>
lemma singleton_prop: "(\<forall>D. D \<subseteq> S \<rightarrow> \<exists>!D \<rightarrow> P D) = (\<forall>x. S x \<rightarrow> P {x})"
  unfolding singleton_def3 unfolding func_defs comb_defs by (metis (full_types))
lemma doubleton_prop: "(\<forall>D. D \<subseteq> S \<rightarrow> \<exists>!\<^sub>2D \<rightarrow> P D) = (\<forall>x y. S x \<and> S y \<rightarrow> x \<noteq> y \<rightarrow> P {x,y})"
  unfolding doubleton_def3 unfolding func_defs comb_defs by (smt (verit))
lemma upair_prop: "(\<forall>D. D \<subseteq> S \<rightarrow> \<exists>\<^sub>\<le>\<^sub>2D \<rightarrow> P D) = (\<forall>x y. S x \<and> S y \<rightarrow> P {x,y})" 
  unfolding upair_def3 unfolding func_defs comb_defs by (smt (verit, best))


subsection \<open>Spaces via Closure under Endo-operations\<close>

text \<open>We obtain spaces by considering the set of sets closed under the given (n-ary) endo-operation.\<close>

text \<open>We start, quite trivially, with closure under nullary endooperations.\<close>
abbreviation(input) op0_closed::"'a \<Rightarrow> Space('a)"  ("_-closed\<^sub>0")
  where "op0_closed \<equiv> \<^bold>T"

lemma "c-closed\<^sub>0 S = S c" unfolding comb_defs ..

text \<open>Things get more interesting with closure under unary endooperations.\<close>
definition op1_closed::"EOp('a) \<Rightarrow> Space('a)" ("_-closed\<^sub>1")
  where "op1_closed \<equiv> image \<ggreater> (\<subseteq>)-preFP"

declare op1_closed_def[space_defs]

lemma "f-closed\<^sub>1 S = (image f S \<subseteq> S)" unfolding space_defs func_defs comb_defs ..

text \<open>Recalling that image and preimage are residuated, we have in fact that:\<close>
lemma op1_closed_def2: "op1_closed = preimage \<ggreater> (\<subseteq>)-postFP" unfolding space_defs func_defs comb_defs by auto
lemma "f-closed\<^sub>1 S = (S \<subseteq> preimage f S)" unfolding op1_closed_def2 func_defs comb_defs ..
lemma "f-closed\<^sub>1 S = (S \<subseteq> f \<ggreater> S)" unfolding op1_closed_def2 func_defs comb_defs ..
lemma op1_closed_def3: "f-closed\<^sub>1 S = (\<forall>x. S x \<rightarrow> S(f x))" unfolding op1_closed_def2 func_defs comb_defs ..

text \<open>Note also that we have:\<close>
lemma "op1_closed = (\<^bold>B\<^sub>1\<^sub>0 \<ggreater>\<^sub>2 \<^bold>S (\<subseteq>)) op0_closed" unfolding space_defs func_defs comb_defs by auto

text \<open>In fact, we can define "closure under an n-ary endooperation" inductively on n, as follows.\<close>
definition op2_closed::"EOp\<^sub>2('a) \<Rightarrow> Space('a)" ("_-closed\<^sub>2")
  where "op2_closed \<equiv> (\<^bold>B\<^sub>1\<^sub>0 \<ggreater>\<^sub>2 \<^bold>S (\<subseteq>)) op1_closed"
definition op3_closed::"('a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> Space('a)" ("_-closed\<^sub>3")
  where "op3_closed \<equiv> (\<^bold>B\<^sub>1\<^sub>0 \<ggreater>\<^sub>2 \<^bold>S (\<subseteq>)) op2_closed"
\<comment> \<open>... and so on\<close>

declare op2_closed_def[space_defs] op3_closed_def[space_defs]

lemma op2_closed_def2: "g-closed\<^sub>2 S = (\<forall>x y. S x \<and> S y \<rightarrow> S(g x y))"  unfolding space_defs func_defs comb_defs by auto
lemma op3_closed_def2: "g-closed\<^sub>3 S = (\<forall>x y z. S x \<and> S y \<and> S z \<rightarrow> S(g x y z))" unfolding space_defs func_defs comb_defs by auto


text \<open>Closure under set-endo-operations of different arities can be defined as follows.\<close>
abbreviation(input) setop0_closed::"Set('a) \<Rightarrow> Space('a)" ("_-closed\<^sub>S\<^sub>0")
  where "setop0_closed F S \<equiv> op0_closed F (\<wp> S)"
abbreviation(input) setop1_closed::"SetEOp('a) \<Rightarrow> Space('a)" ("_-closed\<^sub>S\<^sub>1")
  where "setop1_closed F S \<equiv> op1_closed F (\<wp> S)"
abbreviation(input) setop2_closed::"SetEOp\<^sub>2('a) \<Rightarrow> Space('a)" ("_-closed\<^sub>S\<^sub>2")
  where "setop2_closed F S \<equiv> op2_closed F (\<wp> S)"
\<comment> \<open>... and so on\<close>

lemma "C-closed\<^sub>S\<^sub>0 = (\<lambda>S. C \<subseteq> S)"  unfolding func_defs comb_defs by auto
lemma "F-closed\<^sub>S\<^sub>1 = (\<lambda>S. \<forall>X. X \<subseteq> S \<rightarrow> F X \<subseteq> S)"  unfolding space_defs func_defs comb_defs by auto
lemma "G-closed\<^sub>S\<^sub>2 = (\<lambda>S. \<forall>X Y. X \<subseteq> S \<and> Y \<subseteq> S \<rightarrow> G X Y \<subseteq> S)"  unfolding space_defs func_defs comb_defs by blast


text \<open>Moreover, a set S can also be closed under generalized endooperations (unary in this case).\<close>
definition opG_closed::"EOp\<^sub>G('a) \<Rightarrow> Space('a)" ("_-closed\<^sub>G")
  where "opG_closed \<equiv> (\<^bold>B\<^sub>1\<^sub>0 \<ggreater>\<^sub>2 \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<subseteq>) \<wp>) op0_closed"

declare opG_closed_def[space_defs]

lemma "F-closed\<^sub>G S = (\<forall>X. X \<subseteq> S \<rightarrow> S(F X))" unfolding space_defs func_defs comb_defs by auto

text \<open>The space of all those sets closed under some function(s) is always closed under arbitrary 
 intersections (\<open>\<Inter>\<close>). Such spaces are known in the literature as "closure systems".\<close>
abbreviation(input) closureSystem :: "Set(Space('a))"
  where "closureSystem S \<equiv> \<Inter>-closed\<^sub>G S"

lemma "closureSystem (c-closed\<^sub>0)" unfolding comb_defs func_defs space_defs by simp
lemma "closureSystem (f-closed\<^sub>1)" unfolding comb_defs func_defs space_defs by metis
lemma "closureSystem (g-closed\<^sub>2)" unfolding comb_defs func_defs space_defs by metis
lemma "closureSystem (C-closed\<^sub>S\<^sub>0)" unfolding comb_defs func_defs space_defs by metis
lemma "closureSystem (F-closed\<^sub>S\<^sub>1)" unfolding comb_defs func_defs space_defs by metis
lemma "closureSystem (G-closed\<^sub>S\<^sub>2)" unfolding comb_defs func_defs space_defs by metis
lemma "closureSystem (F-closed\<^sub>G)" unfolding comb_defs func_defs space_defs by auto

text \<open>Closure systems are closed under (arbitrary) intersections.\<close>
lemma closureSystem_meetClosed: "(\<inter>)-closed\<^sub>2 closureSystem" unfolding comb_defs func_defs space_defs by auto
lemma closureSystem_infimumClosed: "closureSystem closureSystem" unfolding comb_defs func_defs space_defs by auto
lemma closureSystem_nonEmpty: "closureSystem X \<Longrightarrow> \<exists>X" unfolding func_defs comb_defs space_defs by auto

text \<open>Closure systems closed under a single nullary (constant) and an n-ary constructor arise often.\<close>
definition op01_closed::"'a \<Rightarrow> EOp('a) \<Rightarrow> Space('a)" ("_,_-closed\<^sub>0\<^sub>1")
  where "z,f-closed\<^sub>0\<^sub>1 \<equiv> z-closed\<^sub>0 \<inter> f-closed\<^sub>1" \<comment> \<open>one unary constructor\<close>
definition op02_closed::"'a \<Rightarrow> EOp\<^sub>2('a) \<Rightarrow> Space('a)" ("_,_-closed\<^sub>0\<^sub>2")
  where "z,g-closed\<^sub>0\<^sub>2 \<equiv> z-closed\<^sub>0 \<inter> g-closed\<^sub>2" \<comment> \<open>one binary constructor\<close>
\<comment> \<open>...and so on\<close>

declare op01_closed_def[space_defs] op02_closed_def[space_defs]

lemma "z,f-closed\<^sub>0\<^sub>1 = (\<lambda>S. S z \<and> f-closed\<^sub>1 S)" unfolding func_defs space_defs comb_defs .. 
lemma "z,g-closed\<^sub>0\<^sub>2 = (\<lambda>S. S z \<and> g-closed\<^sub>2 S)" unfolding func_defs space_defs comb_defs ..

text \<open>Being closure systems, their intersections are also closure systems.\<close>
lemma op01_ClosureSystem: "closureSystem (z,f-closed\<^sub>0\<^sub>1)" unfolding comb_defs func_defs space_defs by metis
lemma op02_ClosureSystem: "closureSystem (z,g-closed\<^sub>0\<^sub>2)" unfolding comb_defs func_defs space_defs by metis


text \<open>More generally, we can introduce (on demand) closure systems that are generated by an arbitrary 
 set \<open>G\<close> of generators by using a sequence of constructors.\<close>
definition opGen1_closed::"EOp('a) \<Rightarrow> Set('a) \<Rightarrow> Space('a)" ("_-closedGen\<^sub>1")
  where "f-closedGen\<^sub>1 G \<equiv> G-closed\<^sub>S\<^sub>0 \<inter> f-closed\<^sub>1" \<comment> \<open>one unary constructor\<close>
definition opGen2_closed::"EOp\<^sub>2('a) \<Rightarrow> Set('a) \<Rightarrow> Space('a)" ("_-closedGen\<^sub>2")
  where "g-closedGen\<^sub>2 G \<equiv> G-closed\<^sub>S\<^sub>0 \<inter> g-closed\<^sub>2" \<comment> \<open>one binary constructor\<close>
    \<comment> \<open>...and so on\<close>
definition opGen12_closed::"EOp('a) \<Rightarrow> EOp\<^sub>2('a) \<Rightarrow> Set('a) \<Rightarrow> Space('a)" ("_,_-closedGen\<^sub>1\<^sub>2")
  where "f,g-closedGen\<^sub>1\<^sub>2 G \<equiv> G-closed\<^sub>S\<^sub>0 \<inter> f-closed\<^sub>1 \<inter> g-closed\<^sub>2" \<comment> \<open>one unary and one binary constructor\<close>
\<comment> \<open>...and so on\<close>

declare opGen1_closed_def[space_defs] opGen2_closed_def[space_defs] opGen12_closed_def[space_defs]

lemma "f-closedGen\<^sub>1 G S = (G \<subseteq> S \<and> f-closed\<^sub>1 S)" unfolding comb_defs func_defs space_defs by simp
lemma "f,g-closedGen\<^sub>1\<^sub>2 G S = (G \<subseteq> S \<and> f-closed\<^sub>1 S \<and> g-closed\<^sub>2 S)" unfolding comb_defs func_defs space_defs by simp

text \<open>Being closure systems, their intersections are also closure systems.\<close>
lemma opGen1_ClosureSystem: "closureSystem (f-closedGen\<^sub>1 G)" unfolding comb_defs space_defs func_defs by metis
lemma opGen2_ClosureSystem: "closureSystem (g-closedGen\<^sub>2 G)" unfolding comb_defs space_defs func_defs by metis

text \<open>Set-operations, in general, do not distribute over arbitrary unions or intersections (of spaces).\<close>
proposition "F (\<Union> S) = \<Union> (image F S)" nitpick \<comment> \<open>countermodel found\<close> oops
proposition "F (\<Inter> S) = \<Inter> (image F S)" nitpick \<comment> \<open>countermodel found\<close> oops

text \<open>Distribution over arbitrary unions and intersections holds if the set-operation is a preimage.\<close>
lemma preimage_distr_bigunion: "preimage f (\<Union> S) = \<Union> ((preimage \<ggreater> image) f S)"
  unfolding comb_defs func_defs apply rule by (smt (verit, best))
lemma preimage_distr_biginter: "preimage F (\<Inter> S) = \<Inter> ((preimage \<ggreater> image) F S)" 
  unfolding comb_defs func_defs apply rule by (smt (verit, best))

text \<open>If the set-operation is an image, distribution over arbitrary unions also obtains.\<close>
lemma image_distr_bigunion: "image f (\<Union> S) = \<Union> ((image \<ggreater> image) f S)"
  unfolding comb_defs func_defs apply rule by (smt (verit, best))
text \<open>However, distribution over arbitrary intersections requires that the space is a closure system.\<close>
lemma image_distr_biginter: "closureSystem S \<Longrightarrow> image F (\<Inter> S) = \<Inter> ((image \<ggreater> image) F S)"
  unfolding comb_defs space_defs func_defs apply rule by (smt (verit, best))


text \<open>Another convenient lemma: closure under a function (wrt one generator) can be conveniently 
 stated in terms of closure under composition with that function (wrt the identity function \<open>\<^bold>I\<close>).\<close>
lemma funClosure_prop: "z,f-closed\<^sub>0\<^sub>1 = (image \<ggreater> image) (\<^bold>T z) (\<^bold>I,((\<ggreater>) f)-closed\<^sub>0\<^sub>1)"
  unfolding comb_defs func_defs apply (rule ext) apply (rule iffI) defer apply auto sorry (*TODO: kernel reconstruction*) 

text \<open>Also note that:\<close>
lemma "\<Inter>((\<ggreater>)-closed\<^sub>2)  = \<Inter> ((\<ggreater>) f)-closed\<^sub>1" for f::"'a \<Rightarrow> 'a" unfolding space_defs func_defs comb_defs by fast
lemma "\<Inter>((;)-closed\<^sub>2) = \<Inter> ((\<ggreater>) f)-closed\<^sub>1" for f::"SetEOp('a)" unfolding space_defs func_defs comb_defs by fast
lemma "\<Inter>((;)-closed\<^sub>2) = \<Inter> ((;) f)-closed\<^sub>1" for f::"ERel('a)" unfolding space_defs func_defs comb_defs by fast
lemma "\<Inter>((\<ggreater>)-closed\<^sub>2) = \<Inter> (\<lambda>x. x ; f)-closed\<^sub>1" for f::"ERel('a)" unfolding space_defs func_defs comb_defs by fast
lemma "\<Inter>((;)-closed\<^sub>2) = \<Inter> (\<lambda>x. x \<ggreater> f)-closed\<^sub>1" for f::"SetEOp('a)" unfolding space_defs func_defs comb_defs by fast
lemma "\<Inter>((;)-closed\<^sub>2) = \<Inter> (\<lambda>x. x ; f)-closed\<^sub>1" for f::"ERel('a)" unfolding space_defs func_defs comb_defs by fast
text \<open>However:\<close>
proposition "((\<ggreater>)-closed\<^sub>2)  = ((\<ggreater>) f-closed\<^sub>1)" nitpick \<comment> \<open>counterexample found\<close> oops
proposition "((;)-closed\<^sub>2) = ((\<lambda>x. x ; f)-closed\<^sub>1)" nitpick \<comment> \<open>counterexample found\<close> oops


subsection \<open>Spaces from Endorelations\<close>
text \<open>The following definitions correspond to functions that take an endorelation R and return the space 
 of those sets satisfying a particular property wrt. R.\<close>

subsubsection \<open>Lub- and Glb-related Definitions\<close>

text \<open>These definitions generalize the "complete join/meet-semilattice" property (existence of suprema resp. infima).\<close>
definition lubComplete::"ERel('a) \<Rightarrow> Space('a)" ("_-lubComplete")
  where "R-lubComplete \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<subseteq>) \<wp> ((\<^bold>R\<^sub>3 \<^bold>D (R-lub)) (\<sqinter>))" 
definition glbComplete::"ERel('a) \<Rightarrow> Space('a)" ("_-glbComplete")
  where "R-glbComplete \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<subseteq>) \<wp> ((\<^bold>R\<^sub>3 \<^bold>D (R-glb)) (\<sqinter>))" \<comment> \<open>all of S-subsets have a glb (wrt R) in S\<close>

declare lubComplete_def[space_defs] glbComplete_def[space_defs]

text \<open>All of S-subsets have a lub (wrt R) in S.\<close>
lemma "R-lubComplete = (\<lambda>S. \<wp> S \<subseteq> ((\<^bold>R\<^sub>3 \<^bold>D (R-lub)) (\<sqinter>) S))" unfolding space_defs comb_defs ..
lemma lubComplete_def2: "R-lubComplete = (\<lambda>S. \<forall>D. D \<subseteq> S \<longrightarrow> (R-lub D \<sqinter> S))" unfolding space_defs rel_defs func_defs comb_defs by blast

text \<open>All of S-subsets have a glb (wrt R) in S.\<close>
lemma "R-glbComplete = (\<lambda>S. \<wp> S \<subseteq> ((\<^bold>R\<^sub>3 \<^bold>D (R-glb)) (\<sqinter>) S))" unfolding space_defs comb_defs ..
lemma glbComplete_def2: "R-glbComplete = (\<lambda>S. \<forall>D. D \<subseteq> S \<longrightarrow> (R-glb D \<sqinter> S))" unfolding space_defs rel_defs func_defs comb_defs by blast

lemma lubComplete_defT: "R-lubComplete = R\<^sup>\<smile>-glbComplete" unfolding space_defs endorel_defs rel_defs comb_defs ..
lemma glbComplete_defT: "R-glbComplete = R\<^sup>\<smile>-lubComplete" unfolding space_defs endorel_defs rel_defs comb_defs ..

text \<open>Limit-completeness of a relation can be expressed in terms of either lub- or glb-completeness.\<close>
lemma limitComplete_def3: "limitComplete R = R-lubComplete \<UU>"
  unfolding space_defs endorel_defs func_defs comb_defs by simp
lemma limitComplete_def4: "limitComplete R = R-glbComplete \<UU>"
  unfolding limitComplete_def2 space_defs func_defs comb_defs by simp

text \<open>Note that lub/glb-completeness is neither monotonic nor antitonic, for instance:\<close>
proposition "A \<subseteq> B \<Longrightarrow> R-lubComplete A \<Longrightarrow> R-lubComplete B" nitpick \<comment> \<open>countermodel found\<close> oops
proposition "A \<subseteq> B \<Longrightarrow> R-lubComplete B \<Longrightarrow> R-lubComplete A" nitpick \<comment> \<open>countermodel found\<close> oops


text \<open>The following related propertes correspond to closure under the lub resp. glb set-operation wrt R.\<close>
definition lubClosed::"ERel('a) \<Rightarrow> Space('a)" ("_-lubClosed")
  where "R-lubClosed \<equiv> (R-lub)-closed\<^sub>S\<^sub>1" 
definition glbClosed::"ERel('a) \<Rightarrow> Space('a)" ("_-glbClosed")
  where "R-glbClosed \<equiv> (R-glb)-closed\<^sub>S\<^sub>1"

declare lubClosed_def[space_defs] glbClosed_def[space_defs]

lemma lubClosed_defT: "R-lubClosed = R\<^sup>\<smile>-glbClosed" unfolding rightBound_defT space_defs endorel_defs rel_defs comb_defs ..
lemma glbClosed_defT: "R-glbClosed = R\<^sup>\<smile>-lubClosed" unfolding leftBound_defT space_defs endorel_defs rel_defs comb_defs ..

text \<open>Recalling that antisymmetry entails uniqueness of lub/glb (when they exist), we have in fact.\<close>
lemma lubComplete_lubClosed: "antisymmetric R \<Longrightarrow> R-lubComplete S \<Longrightarrow> R-lubClosed S" 
  unfolding space_defs endorel_defs rel_defs func_defs comb_defs apply safe by metis
lemma glbComplete_glbClosed: "antisymmetric R \<Longrightarrow> R-glbComplete S \<Longrightarrow>  R-glbClosed S" 
  unfolding space_defs endorel_defs rel_defs func_defs comb_defs apply safe by metis

text \<open>However, being closed under lub/glb does not entail existence of lub/glb.\<close>
proposition "\<exists>S \<Longrightarrow> R-lubClosed S \<Longrightarrow>  R-lubComplete S" nitpick \<comment> \<open>countermodel found\<close> oops
proposition "\<exists>S \<Longrightarrow> R-glbClosed S \<Longrightarrow> R-glbComplete S" nitpick \<comment> \<open>countermodel found\<close> oops

text \<open>In fact, for limit-complete relations, closure under lub/glb does entail existence of lub/glb.\<close>
lemma lubClosed_lubComplete: "limitComplete R \<Longrightarrow> R-lubClosed S \<Longrightarrow> R-lubComplete S" 
  unfolding space_defs endorel_defs func_defs comb_defs by blast
lemma glbClosed_glbComplete: "limitComplete R \<Longrightarrow> R-glbClosed S \<Longrightarrow>  R-glbComplete S" 
  unfolding limitComplete_def2 space_defs endorel_defs func_defs comb_defs by blast

lemma lubClosed_def2: "antisymmetric R \<Longrightarrow> limitComplete R \<Longrightarrow> R-lubComplete = R-lubClosed" 
  using lubClosed_lubComplete lubComplete_lubClosed by blast
lemma glbClosed_def2: "antisymmetric R \<Longrightarrow> limitComplete R \<Longrightarrow> R-glbComplete = R-glbClosed" 
  using glbClosed_glbComplete glbComplete_glbClosed by blast


subsubsection \<open>Upwards- and Downwards-Closure\<close>

definition upwardsClosed::"ERel('a) \<Rightarrow> Space('a)" ("_-upwardsClosed")
  where "R-upwardsClosed \<equiv> (R-upImage)-closed\<^sub>S\<^sub>1"
definition downwardsClosed::"ERel('a) \<Rightarrow> Space('a)" ("_-downwardsClosed")
  where "R-downwardsClosed \<equiv> (R-downImage)-closed\<^sub>S\<^sub>1"

declare upwardsClosed_def[space_defs] downwardsClosed_def[space_defs]

lemma upwardsClosed_defT: "R-upwardsClosed = R\<^sup>\<smile>-downwardsClosed" unfolding space_defs rightImage_defT ..
lemma downwardsClosed_defT: "R-downwardsClosed = R\<^sup>\<smile>-upwardsClosed" unfolding space_defs leftImage_defT ..

lemma upwardsClosed_def2: "R-upwardsClosed S = (\<forall>x y. R x y \<longrightarrow> S x \<longrightarrow> S y)"
  unfolding space_defs rel_defs func_defs comb_defs by blast
lemma downwardsClosed_def2: "R-downwardsClosed S = (\<forall>x y. R x y \<longrightarrow> S y \<longrightarrow> S x)"
  unfolding space_defs rel_defs func_defs comb_defs by blast

lemma upwardsClosed_def3: "skeletal R \<Longrightarrow> R-upwardsClosed S = (\<forall>D. \<exists>(R-glb D) \<longrightarrow> (R-glb D) \<subseteq> S  \<longrightarrow> D \<subseteq> S)"
  unfolding space_defs endorel_defs rel_defs func_defs comb_defs apply (rule iffI) apply blast by (smt (verit, del_insts))
lemma downwardsClosed_def3: "skeletal R \<Longrightarrow> R-downwardsClosed S = (\<forall>D. \<exists>(R-lub D) \<longrightarrow> (R-lub D) \<subseteq> S  \<longrightarrow> D \<subseteq> S)"
  by (simp add: downwardsClosed_defT lub_defT skeletal_symm upwardsClosed_def3)

lemma upwardsClosed_def4: "skeletal R \<Longrightarrow> limitComplete R \<Longrightarrow> R-upwardsClosed S = (\<forall>D. (R-glb D) \<subseteq> S \<longrightarrow> D \<subseteq> S)"  
  unfolding upwardsClosed_def3 limitComplete_def2 comb_defs by simp
lemma downwardsClosed_def4: "skeletal R \<Longrightarrow> limitComplete R \<Longrightarrow> R-downwardsClosed S = (\<forall>D. (R-lub D) \<subseteq> S \<longrightarrow> D \<subseteq> S)"  
  by (simp add: downwardsClosed_defT limitComplete_defT lub_defT skeletal_symm upwardsClosed_def4)


subsubsection \<open>Existence of Greatest- and Least-Elements\<close>

text \<open>Another interesting property is existence of greatest resp. least elements.\<close>
definition greatestExist::"ERel('a) \<Rightarrow> Space('a)" ("_-greatestExist")
  where "R-greatestExist \<equiv> R-greatest \<ggreater> \<exists>"
definition leastExist::"ERel('a) \<Rightarrow> Space('a)" ("_-leastExist")
  where "R-leastExist \<equiv> R-least \<ggreater> \<exists>"

declare greatestExist_def[space_defs] leastExist_def[space_defs]

text \<open>In fact, recalling that:\<close>
lemma "R-greatest S = (S \<inter> R-upperBound S)" unfolding greatest_def comb_defs ..
lemma "R-least S = (S \<inter> R-lowerBound S)" unfolding least_def comb_defs ..

lemma greatestExist_defT: "R-greatestExist = R\<^sup>\<smile>-leastExist" unfolding rightBound_defT space_defs endorel_defs comb_defs ..
lemma leastExist_defT: "R-leastExist = R\<^sup>\<smile>-greatestExist" unfolding leftBound_defT space_defs endorel_defs comb_defs ..

text \<open>We have that existence of greatest/least elements for S is equivalent to every S-subset having 
 upper/lower bounds (wrt R) in S. (Note that this is a strong variant of up/downwards directedness.)\<close>
lemma greatestExist_def2: "R-greatestExist S = (\<forall>D. D \<subseteq> S \<longrightarrow> \<exists>(S \<inter> R-upperBound D))"
  unfolding space_defs endorel_defs rel_defs func_defs comb_defs by auto
lemma leastExist_def2:    "R-leastExist S    = (\<forall>D. D \<subseteq> S \<longrightarrow> \<exists>(S \<inter> R-lowerBound D))"
  unfolding space_defs endorel_defs rel_defs func_defs comb_defs by auto

text \<open>Or, alternatively:\<close>
lemma greatestExist_def3: "R-greatestExist S = (\<exists>S \<and> (\<forall>D. D \<subseteq> S \<longrightarrow> \<exists>D \<longrightarrow> \<exists>(S \<inter> R-upperBound D)))"
  unfolding greatestExist_def2 rel_defs func_defs comb_defs by auto
lemma leastExist_def3:    "R-leastExist S    = (\<exists>S \<and> (\<forall>D. D \<subseteq> S \<longrightarrow> \<exists>D \<longrightarrow> \<exists>(S \<inter> R-lowerBound D)))"
  unfolding leastExist_def2  rel_defs func_defs comb_defs by auto

text \<open>In fact, existence of greatest/least-elements is a strictly weaker property than lub/glb-completeness.\<close>
lemma glbComplete_least: "R-glbComplete \<subseteq> R-leastExist" 
  unfolding space_defs endorel_defs func_defs comb_defs by auto
lemma lubComplete_greatest: "R-lubComplete \<subseteq> R-greatestExist"
  unfolding space_defs endorel_defs func_defs comb_defs by auto
proposition "R-greatestExist \<subseteq> R-lubComplete" nitpick \<comment> \<open>countermodel found\<close> oops
proposition "R-leastExist \<subseteq> R-glbComplete" nitpick \<comment> \<open>countermodel found\<close> oops

lemma greatestExist_lubClosed: "R-downwardsClosed S \<Longrightarrow> R-greatestExist S \<Longrightarrow> R-lubClosed S"
  unfolding space_defs endorel_defs rel_defs func_defs comb_defs by blast
lemma leastExist_glbClosed: "R-upwardsClosed S \<Longrightarrow> R-leastExist S \<Longrightarrow> R-glbClosed S"
  unfolding space_defs endorel_defs rel_defs func_defs comb_defs by blast

lemma greatestExist_def4: "limitComplete R \<Longrightarrow> R-downwardsClosed S \<Longrightarrow> R-greatestExist S = R-lubClosed S"
  using greatestExist_lubClosed lubClosed_lubComplete lubComplete_greatest unfolding func_defs comb_defs by metis
lemma leastExist_def4: "limitComplete R \<Longrightarrow> R-upwardsClosed S \<Longrightarrow> R-leastExist S = R-glbClosed S"
  by (simp add: glbClosed_defT greatestExist_def4 leastExist_defT limitComplete_defT upwardsClosed_defT)


subsubsection \<open>Upwards- and Downwards-Directedness\<close>

text \<open>The property of a set being "up/downwards directed" wrt. an endorelation:
  Every pair of S-elements has upper/lower-bounds (wrt R) in S.\<close>
definition upwardsDirected::"ERel('a) \<Rightarrow> Space('a)" ("_-upwardsDirected")
  where "R-upwardsDirected  \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<subseteq>\<^sup>2) (\<^bold>W (\<times>)) (\<^bold>R\<^sub>3 \<^bold>E (\<^bold>\<Psi>\<^sub>2\<^sub>1 (\<inter>) R) (\<sqinter>))"
definition downwardsDirected::"ERel('a) \<Rightarrow> Space('a)" ("_-downwardsDirected")
  where "R-downwardsDirected \<equiv>  \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<subseteq>\<^sup>2) (\<^bold>W (\<times>)) (\<^bold>R\<^sub>3 \<^bold>E (\<^bold>\<Psi>\<^sub>2\<^sub>1 (\<inter>) (\<^bold>C R)) (\<sqinter>))"

declare upwardsDirected_def[space_defs] downwardsDirected_def[space_defs]

lemma "R-upwardsDirected = (\<lambda>S. (S \<times> S) \<subseteq>\<^sup>2 (\<lambda>a b. S \<sqinter> (\<^bold>\<Psi>\<^sub>2\<^sub>1 (\<inter>) R a b)))" unfolding space_defs comb_defs ..
lemma "R-upwardsDirected = (\<lambda>S. (S \<times> S) \<subseteq>\<^sup>2 (\<lambda>a b. S \<sqinter> (R a \<inter> R b) ))" unfolding space_defs comb_defs ..
lemma "R-upwardsDirected = (\<lambda>S. \<forall>a b. S a \<and> S b \<longrightarrow> (\<exists>c. S c \<and> R a c \<and> R b c))" unfolding space_defs rel_defs func_defs comb_defs ..

lemma "R-downwardsDirected = (\<lambda>S. (S \<times> S) \<subseteq>\<^sup>2 (\<lambda>a b. S \<sqinter> (\<^bold>\<Psi>\<^sub>2\<^sub>1 (\<inter>) (\<^bold>C R) a b)))" unfolding space_defs comb_defs ..
lemma "R-downwardsDirected = (\<lambda>S. (S \<times> S) \<subseteq>\<^sup>2 (\<lambda>a b. S \<sqinter> (R\<^sup>\<smile> a \<inter> R\<^sup>\<smile> b)))" unfolding space_defs rel_defs func_defs comb_defs ..
lemma "R-downwardsDirected = (\<lambda>S. \<forall>a b. S a \<and> S b \<longrightarrow> (\<exists>c. S c \<and> R c a \<and> R c b))" unfolding space_defs rel_defs func_defs comb_defs ..

lemma upwardsDirected_defT: "R-upwardsDirected = R\<^sup>\<smile>-downwardsDirected" unfolding space_defs rel_defs comb_defs ..
lemma downwardsDirected_defT: "R-downwardsDirected = R\<^sup>\<smile>-upwardsDirected" unfolding space_defs rel_defs comb_defs ..

text \<open>The definition above can be rephrased as:\<close>
lemma upwardsDirected_def2: "R-upwardsDirected S = (\<forall>a b. S a \<and> S b \<longrightarrow> \<exists>(S \<inter> R-upperBound {a,b}))" 
  unfolding space_defs rel_defs func_defs comb_defs by metis
lemma downwardsDirected_def2: "R-downwardsDirected S = (\<forall>a b. S a \<and> S b \<longrightarrow> \<exists>(S \<inter> R-lowerBound {a,b}))" 
  unfolding space_defs rel_defs func_defs comb_defs by metis
text \<open>or, alternatively:\<close>
lemma upwardsDirected_def3:  "R-upwardsDirected S = (\<forall>D. D \<subseteq> S \<longrightarrow> \<exists>\<^sub>\<le>\<^sub>2D \<longrightarrow> \<exists>(S \<inter> R-upperBound D))"
  unfolding upwardsDirected_def2 unfolding upair_prop ..
lemma downwardsDirected_def3:  "R-downwardsDirected S = (\<forall>D. D \<subseteq> S \<longrightarrow> \<exists>\<^sub>\<le>\<^sub>2D \<longrightarrow> \<exists>(S \<inter> R-lowerBound D))"
  unfolding downwardsDirected_def2 unfolding upair_prop ..

text \<open>Note that up/downwards directedness does not entail non-emptyness of S.\<close>
proposition "R-upwardsDirected S \<longrightarrow> \<exists>S" nitpick  \<comment> \<open>countermodel found\<close> oops
proposition "R-downwardsDirected S \<longrightarrow> \<exists>S" nitpick  \<comment> \<open>countermodel found\<close> oops

text \<open>For antisymmetric relations, upwards- (resp. downwards-) directedness entails the identity of
the notions of maximal and greatest (resp. minimal and least).\<close>
lemma upwardsDirected_maxGreatest: "antisymmetric R \<Longrightarrow> R-upwardsDirected S \<Longrightarrow> R-max S = R-greatest S"
  unfolding space_defs endorel_defs rel_defs func_defs comb_defs by metis
lemma downwardsDirected_minLeast: "antisymmetric R \<Longrightarrow> R-downwardsDirected S \<Longrightarrow> R-min S = R-least S"
  unfolding space_defs endorel_defs rel_defs func_defs comb_defs by metis


subsubsection \<open>Join- and Meet-Closure\<close>

text \<open>Convenient abbreviations for joins resp. meets (lub resp. glb of sets with 2 elements).\<close>
abbreviation(input) join ("_-join")
  where "R-join a b \<equiv> R-lub {a,b}"
abbreviation(input) meet ("_-meet")
  where "R-meet a b \<equiv> R-glb {a,b}"

text \<open>Some platitudes about meets and joins.\<close>
lemma join_prop1:  "R-lowerBound (R-join a b) a" unfolding endorel_defs rel_defs func_defs comb_defs by auto
lemma join_prop2:  "R-lowerBound (R-join a b) b" unfolding endorel_defs rel_defs func_defs comb_defs by auto
lemma meet_prop1:  "R-upperBound (R-meet a b) a" unfolding endorel_defs rel_defs func_defs comb_defs by auto
lemma meet_prop2:  "R-upperBound (R-meet a b) b" unfolding endorel_defs rel_defs func_defs comb_defs by auto

text \<open>The following are weaker versions of lub/glb-closure customarily used in the literature.\<close>
definition joinClosed::"ERel('a) \<Rightarrow> Space('a)" ("_-joinClosed")
  where "R-joinClosed \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<subseteq>\<^sup>2) (\<^bold>W (\<times>)) (\<^bold>R\<^sub>3 \<^bold>E (R-join) \<wp>)"
definition meetClosed::"ERel('a) \<Rightarrow> Space('a)" ("_-meetClosed")
  where "R-meetClosed \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<subseteq>\<^sup>2) (\<^bold>W (\<times>)) (\<^bold>R\<^sub>3 \<^bold>E (R-meet) \<wp>)"

declare joinClosed_def[space_defs] meetClosed_def[space_defs]

lemma "R-joinClosed = (\<lambda>S. (S \<times> S) \<subseteq>\<^sup>2 (\<^bold>R\<^sub>3 \<^bold>E (R-join) \<wp> S))" unfolding space_defs comb_defs ..
lemma "R-joinClosed = (\<lambda>S. (S \<times> S) \<subseteq>\<^sup>2 (\<lambda>a b. R-join a b \<subseteq> S))" unfolding space_defs comb_defs ..
lemma "R-joinClosed = (\<lambda>S. \<forall>a b. S a \<and> S b \<longrightarrow> R-join a b \<subseteq> S)" unfolding space_defs rel_defs func_defs comb_defs ..

lemma "R-meetClosed = (\<lambda>S. (S \<times> S) \<subseteq>\<^sup>2 (\<^bold>R\<^sub>3 \<^bold>E (R-meet) \<wp> S))" unfolding space_defs comb_defs ..
lemma "R-meetClosed = (\<lambda>S. (S \<times> S) \<subseteq>\<^sup>2 (\<lambda>a b. R-meet a b \<subseteq> S))" unfolding space_defs comb_defs ..
lemma "R-meetClosed = (\<lambda>S. \<forall>a b. S a \<and> S b \<longrightarrow> R-meet a b \<subseteq> S)" unfolding space_defs rel_defs func_defs comb_defs ..

lemma joinClosed_defT: "R-joinClosed = R\<^sup>\<smile>-meetClosed" unfolding space_defs endorel_defs rel_defs func_defs comb_defs ..
lemma meetClosed_defT: "R-meetClosed = R\<^sup>\<smile>-joinClosed" unfolding space_defs endorel_defs rel_defs func_defs comb_defs ..

lemma joinClosed_def2: "joinClosed R S = (\<forall>p. p \<subseteq> S \<rightarrow> \<exists>\<^sub>\<le>\<^sub>2 p \<rightarrow> (R-lub p) \<subseteq> S)" 
  unfolding upair_prop unfolding space_defs endorel_defs rel_defs func_defs comb_defs by auto
lemma meetClosed_def2: "meetClosed R S = (\<forall>p. p \<subseteq> S \<rightarrow> \<exists>\<^sub>\<le>\<^sub>2 p \<rightarrow> (R-glb p) \<subseteq> S)" 
  unfolding upair_prop unfolding space_defs endorel_defs rel_defs func_defs comb_defs by auto

lemma joinClosed_upwardsDirected: "limitComplete R \<Longrightarrow> R-joinClosed S \<Longrightarrow> R-upwardsDirected S"
 unfolding limitComplete_def joinClosed_def2 upwardsDirected_def3 lub_def least_def func_defs comb_defs by metis
lemma meetClosed_downwardsDirected: "limitComplete R \<Longrightarrow> R-meetClosed S \<Longrightarrow> R-downwardsDirected S"
   by (simp add: downwardsDirected_defT joinClosed_upwardsDirected limitComplete_defT meetClosed_defT)

text \<open>Thus we have:\<close>
lemma greatestExist_upwardsDirected: "R-greatestExist S \<Longrightarrow> R-upwardsDirected S" 
  by (simp add: greatestExist_def2 upwardsDirected_def3)
lemma leastExist_downwardsDirected: "R-leastExist S \<Longrightarrow> R-downwardsDirected S" 
  by (simp add: downwardsDirected_defT greatestExist_upwardsDirected leastExist_defT)
text \<open>Note, however:\<close>
proposition "\<exists>S \<Longrightarrow> R-upwardsDirected S \<Longrightarrow> R-greatestExist S" nitpick  \<comment> \<open>countermodel found\<close> oops
proposition "\<exists>S \<Longrightarrow> R-downwardsDirected S \<Longrightarrow> R-leastExist S" nitpick  \<comment> \<open>countermodel found\<close> oops

lemma downwardsDirected_meetClosed: "R-upwardsClosed S \<Longrightarrow> R-downwardsDirected S \<Longrightarrow> R-meetClosed S"
  unfolding meetClosed_def2 space_defs endorel_defs rel_defs func_defs comb_defs by fast
lemma upwardsDirected_joinClosed: "R-downwardsClosed S \<Longrightarrow> R-upwardsDirected S \<Longrightarrow> R-joinClosed S"
  by (simp add: downwardsClosed_defT downwardsDirected_meetClosed joinClosed_defT upwardsDirected_defT)

lemma downwardsDirected_def4: "limitComplete R \<Longrightarrow> R-upwardsClosed S \<Longrightarrow> R-downwardsDirected S = R-meetClosed S"
  using downwardsDirected_meetClosed meetClosed_downwardsDirected by blast
lemma upwardsDirected_def4: "limitComplete R \<Longrightarrow> R-downwardsClosed S \<Longrightarrow> R-upwardsDirected S = R-joinClosed S"
  using joinClosed_upwardsDirected upwardsDirected_joinClosed by blast


subsubsection \<open>Ideals and Filters\<close>

definition pseudoFilter::"ERel('a) \<Rightarrow> Space('a)" ("_-pseudoFilter")
  where "R-pseudoFilter \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<subseteq>\<^sup>2) (\<^bold>R\<^sub>3 \<^bold>E R-meet \<wp>) (\<^bold>W (\<times>))"
definition pseudoIdeal::"ERel('a) \<Rightarrow> Space('a)" ("_-pseudoIdeal")
  where "R-pseudoIdeal  \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<subseteq>\<^sup>2) (\<^bold>R\<^sub>3 \<^bold>E R-join \<wp>) (\<^bold>W (\<times>))"

declare pseudoFilter_def[space_defs] pseudoIdeal_def[space_defs]


lemma "R-pseudoFilter = (\<lambda>S. (\<^bold>R\<^sub>3 \<^bold>E R-meet \<wp> S) \<subseteq>\<^sup>2 (S \<times> S))" unfolding space_defs comb_defs ..
lemma "R-pseudoFilter = (\<lambda>S. \<forall>a b. R-meet a b \<subseteq> S \<longrightarrow> (S a \<and> S b))" unfolding space_defs rel_defs func_defs comb_defs ..

lemma "R-pseudoIdeal = (\<lambda>S. (\<^bold>R\<^sub>3 \<^bold>E R-join \<wp> S) \<subseteq>\<^sup>2 (S \<times> S))" unfolding space_defs comb_defs ..
lemma "R-pseudoIdeal = (\<lambda>S. \<forall>a b. R-join a b \<subseteq> S \<longrightarrow> (S a \<and> S b))" unfolding space_defs rel_defs func_defs comb_defs ..

lemma pseudoFilter_defT: "R-pseudoFilter = R\<^sup>\<smile>-pseudoIdeal" unfolding space_defs endorel_defs rel_defs comb_defs ..
lemma pseudoIdeal_defT: "R-pseudoIdeal = R\<^sup>\<smile>-pseudoFilter" unfolding space_defs endorel_defs rel_defs comb_defs ..

lemma pseudoFilter_upwardsClosed: "skeletal R \<Longrightarrow> R-pseudoFilter S \<Longrightarrow> R-upwardsClosed S" 
  unfolding space_defs endorel_defs rel_defs func_defs comb_defs by (smt (verit, del_insts))
lemma pseudoIdeal_downwardsClosed: "skeletal R \<Longrightarrow> R-pseudoIdeal S \<Longrightarrow> R-downwardsClosed S" 
  unfolding space_defs endorel_defs rel_defs func_defs comb_defs by (smt (verit, del_insts))

lemma upwardsClosed_pseudoFilter: "limitComplete R \<Longrightarrow> R-upwardsClosed S \<Longrightarrow> R-pseudoFilter S"
  using meet_prop1 meet_prop2 unfolding limitComplete_def2 upwardsClosed_def2 unfolding space_defs rel_defs func_defs comb_defs by metis
lemma downwardsClosed_pseudoIdeal: "limitComplete R \<Longrightarrow> R-downwardsClosed S \<Longrightarrow> R-pseudoIdeal S"
  by (simp add: downwardsClosed_defT limitComplete_defT pseudoIdeal_defT upwardsClosed_pseudoFilter)

lemma pseudoFilter_def2: "skeletal R \<Longrightarrow> limitComplete R \<Longrightarrow> R-pseudoFilter S = R-upwardsClosed S" 
  using pseudoFilter_upwardsClosed upwardsClosed_pseudoFilter by blast
lemma pseudoIdeal_def2: "skeletal R \<Longrightarrow> limitComplete R \<Longrightarrow> R-pseudoIdeal S = R-downwardsClosed S"
  using downwardsClosed_pseudoIdeal pseudoIdeal_downwardsClosed by blast


text \<open>The following notions abstract the order-theoretical property of filter/ideal towards relations in
 general: S is a filter/ideal when all and only pairs of S-elements have their meet/join (wrt R) in S.\<close>
abbreviation(input) filter::"ERel('a) \<Rightarrow> Space('a)" ("_-filter")
  where "R-filter S \<equiv> R-pseudoFilter S \<and> R-meetClosed S"
abbreviation(input) ideal::"ERel('a) \<Rightarrow> Space('a)" ("_-ideal")
  where "R-ideal S  \<equiv> R-pseudoIdeal S \<and> R-joinClosed S"

lemma filter_defT: "R-filter S = R\<^sup>\<smile>-ideal S" by (simp add: meetClosed_defT pseudoFilter_defT)
lemma ideal_defT: "R-ideal S = R\<^sup>\<smile>-filter S"  by (simp add: joinClosed_defT pseudoIdeal_defT)

lemma filter_char: "R-filter S = (\<forall>a b. R-meet a b \<subseteq> S \<longleftrightarrow> S a \<and> S b)" 
  unfolding space_defs endorel_defs rel_defs func_defs comb_defs apply (rule iffI) apply metis by simp
lemma ideal_char: "R-ideal S = (\<forall>a b. R-join a b \<subseteq> S \<longleftrightarrow> S a \<and> S b)" 
  by (simp add: filter_char ideal_defT lub_defT)

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
  unfolding func_defs  comb_defs by (metis filter_prop1 filter_prop2 filter_prop3)
lemma ideal_def2: "partial_order R \<Longrightarrow> limitComplete R \<Longrightarrow> R-ideal = (R-downwardsClosed \<inter> R-upwardsDirected)" 
  unfolding func_defs  comb_defs by (metis ideal_prop1 ideal_prop2 ideal_prop3)


subsubsection \<open>Well-Founded- and Well-Ordered-Sets\<close>

text \<open>Well-foundedness of sets wrt. a given relation (as in "Nat is well-founded wrt. \<open><\<close> ").\<close>
definition wellFoundedSet::"ERel('a) \<Rightarrow> Space('a)" ("_-wellFoundedSet")
  where "wellFoundedSet \<equiv> \<^bold>B\<^sub>1\<^sub>1 (\<supseteq>) (min \<ggreater>\<^sub>2 \<exists>) ((\<supseteq>) \<ggreater> (\<inter>) \<exists>)"
definition wellOrderedSet::"ERel('a) \<Rightarrow> Space('a)" ("_-wellOrderedSet")
  where "wellOrderedSet \<equiv> \<^bold>B\<^sub>1\<^sub>1 (\<supseteq>) (least \<ggreater>\<^sub>2  \<exists>) ((\<supseteq>) \<ggreater> (\<inter>) \<exists>)" 

declare wellFoundedSet_def[endorel_defs] wellOrderedSet_def[endorel_defs]

text \<open>Every non-empty S-subset S has min elements (in D).\<close>
lemma wellFoundedSet_def2: "R-wellFoundedSet S = (\<forall>D. D \<subseteq> S \<longrightarrow> \<exists>D \<longrightarrow> \<exists>(R-min D))" 
  unfolding endorel_defs rel_defs func_defs comb_defs by auto
text \<open>Every non-empty S-subset D has least elements (in D).\<close>
lemma wellOrderedSet_def2: "R-wellOrderedSet S = (\<forall>D. D \<subseteq> S \<longrightarrow> \<exists>D \<longrightarrow> \<exists>(R-least D))"
  unfolding endorel_defs rel_defs func_defs comb_defs by auto

text \<open>As expected, we have:\<close>
lemma "wellFounded R = R-wellFoundedSet \<UU>" unfolding endorel_defs rel_defs func_defs comb_defs by simp
lemma "wellOrdered R = R-wellOrderedSet \<UU>" unfolding endorel_defs rel_defs func_defs comb_defs by simp

text \<open>For non-empty sets, well-orderedness entails existence of least elements (but not the other way round).\<close>
lemma "\<exists>S \<Longrightarrow> R-wellOrderedSet S \<Longrightarrow> R-leastExist S" unfolding space_defs endorel_defs func_defs comb_defs by simp
proposition "\<exists>S \<Longrightarrow> R-leastExist S \<Longrightarrow> R-wellOrderedSet S" nitpick \<comment> \<open>countermodel found\<close> oops

lemma "(\<subseteq>)-wellFoundedSet {{1::nat},{2},{1,2}}" 
  unfolding endorel_defs rel_defs endorel_defs func_defs comb_defs by (smt (verit, best))
lemma "\<not> (\<subseteq>)-wellOrderedSet {{1::nat},{2},{1,2}}" 
  unfolding endorel_defs rel_defs func_defs comb_defs \<comment> \<open>proof by external provers\<close> oops (*TODO: this used to work - fix*)


subsubsection \<open>Chain and Antichain\<close>

definition chain :: "ERel('a) \<Rightarrow> Space('a)" ("_-chain")
  where "R-chain \<equiv> \<^bold>W (\<times>) \<ggreater> \<wp>\<^sup>2 (symmetricClosure R)"
definition antichain::"ERel('a) \<Rightarrow> Space('a)" ("_-antichain")
  where "R-antichain \<equiv> \<^bold>W (\<times>) \<ggreater> \<wp>\<^sup>2 (connectedExpansion R)"

declare chain_def[space_defs] antichain_def[space_defs]

lemma "R-chain S = (S \<times> S) \<subseteq>\<^sup>2 symmetricClosure R" unfolding space_defs comb_defs ..
lemma "R-chain S = (S \<times> S) \<subseteq>\<^sup>2 (R \<union>\<^sup>2 (R\<^sup>\<smile>))" unfolding space_defs endorel_defs comb_defs ..
lemma "R-chain S = (\<forall>x y. (S x \<and> S y) \<rightarrow> (R x y \<or> R y x))" unfolding space_defs endorel_defs rel_defs func_defs comb_defs ..

lemma "R-antichain S = (S \<times> S) \<subseteq>\<^sup>2 connectedExpansion R" unfolding space_defs comb_defs ..
lemma "R-antichain S = (S \<times> S) \<subseteq>\<^sup>2 (R \<union>\<^sup>2 (R\<^sup>\<sim>))" unfolding space_defs endorel_defs comb_defs ..
lemma "R-antichain S = (\<forall>x y. (S x \<and> S y) \<rightarrow> (R x y \<or> \<not>R y x))" unfolding space_defs endorel_defs rel_defs func_defs comb_defs ..

lemma "chain = symmetricClosure \<ggreater> \<wp>\<^sup>2 \<ggreater> (\<^bold>W \<ggreater> (\<ggreater>)) (\<times>)" unfolding space_defs endorel_defs rel_defs func_defs comb_defs ..
lemma "antichain = connectedExpansion \<ggreater> \<wp>\<^sup>2 \<ggreater> (\<^bold>W \<ggreater> (\<ggreater>)) (\<times>)" unfolding space_defs endorel_defs rel_defs func_defs comb_defs ..

lemma chain_def2: "R-chain S = (S \<times> S \<bottom>\<^sup>2 symmetricInterior (R\<^sup>\<midarrow>))" unfolding space_defs endorel_defs rel_defs func_defs comb_defs by blast
lemma antichain_def2: "R-antichain S = (S \<times> S \<bottom>\<^sup>2 asymmetricContraction R)" unfolding space_defs endorel_defs rel_defs func_defs comb_defs by blast

lemma chain_def3: "semiconnected R \<Longrightarrow> R-chain S = (S \<subseteq> \<Delta> R)"
  unfolding space_defs endorel_defs rel_defs func_defs comb_defs by metis
lemma antichain_def3: "antisymmetric R \<Longrightarrow> R-antichain S = ((S \<times> S) \<inter>\<^sup>2 R \<subseteq>\<^sup>2 \<Q>)"
  unfolding space_defs endorel_defs rel_defs func_defs comb_defs by blast

lemma "R-chain (R-greatest S)"  unfolding space_defs endorel_defs rel_defs func_defs comb_defs by simp
lemma "R-chain (R-least S)"  unfolding space_defs endorel_defs rel_defs func_defs comb_defs by simp
lemma "R-antichain (R-max S)" unfolding space_defs endorel_defs rel_defs func_defs comb_defs by blast
lemma "R-antichain (R-min S)" unfolding space_defs endorel_defs rel_defs func_defs comb_defs by blast

lemma antichain_def4:  "R-antichain = FP (R-max)" unfolding space_defs endorel_defs rel_defs func_defs comb_defs by metis
lemma antichain_def5:  "R-antichain = FP (R-min)" unfolding space_defs endorel_defs rel_defs func_defs comb_defs by metis
lemma antichain_def6: "R-antichain = range R-max" unfolding space_defs endorel_defs rel_defs func_defs comb_defs by blast
lemma antichain_def7: "R-antichain = range R-min" unfolding space_defs endorel_defs rel_defs func_defs comb_defs by blast

text \<open>Chains are both upwards- and downwards-directed.\<close>
lemma chain_upwardsDirected: "R-chain S \<Longrightarrow> R-upwardsDirected S"  unfolding space_defs endorel_defs rel_defs func_defs comb_defs by blast
lemma chain_downwardsDirected: "R-chain S \<Longrightarrow> R-downwardsDirected S"  unfolding space_defs endorel_defs rel_defs func_defs comb_defs by blast


text \<open>A set S is called chain-complete wrt. an endorelation R when every nonempty subset of S that 
 is a chain (wrt. R) has a supremum (wrt. R) in S.\<close>
definition chainComplete :: "ERel('a) \<Rightarrow> Space('a)"  ("_-chainComplete")
  where "R-chainComplete S \<equiv> \<forall>C. C \<subseteq> S \<rightarrow> \<exists>C \<rightarrow> R-chain C \<rightarrow> R-lub C \<subseteq> S"

declare chainComplete_def[space_defs] 

lemma chainComplete_set_def: "(\<subseteq>)-chainComplete S = (\<forall>C. C \<subseteq> S \<rightarrow> \<exists>C \<rightarrow> (\<subseteq>)-chain C \<rightarrow> S(\<Union>C))"
  by (simp add: bigunion_lub_def chainComplete_def iota_simp set_lub_singleton)

text \<open>A set S is called directed-complete (aka. dcpo) wrt. an endorelation R when every nonempty 
 subset of S that is upwards-directed (wrt. R) has a supremum (wrt. R) in S.\<close>
definition directedComplete :: "ERel('a) \<Rightarrow> Space('a)"  ("_-directedComplete")
  where "R-directedComplete S \<equiv> \<forall>D. D \<subseteq> S \<rightarrow> \<exists>D \<rightarrow> R-upwardsDirected D \<rightarrow> R-lub D \<subseteq> S"

declare directedComplete_def[space_defs] 

lemma directedComplete_set_def: "(\<subseteq>)-directedComplete S = (\<forall>D. D \<subseteq> S \<rightarrow> \<exists>D \<rightarrow> (\<subseteq>)-upwardsDirected D \<longrightarrow> S(\<Union>D))"
  by (simp add: bigunion_lub_def directedComplete_def iota_simp set_lub_singleton)

text \<open>Clearly, directed-complete sets are also chain-complete.\<close>
lemma directed_chainComplete: "R-directedComplete S \<longrightarrow> R-chainComplete S"
  by (simp add: chainComplete_def chain_upwardsDirected directedComplete_def)

end