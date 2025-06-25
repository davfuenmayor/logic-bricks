theory induction
  imports diagrams spaces
begin

section \<open>Induction, Fixed-points & co.\<close>

named_theorems ind_defs

subsection \<open>Inductively-generated Sets\<close>

definition inductiveSet01 :: "'a \<Rightarrow> EOp('a) \<Rightarrow> Set('a)" ("_,_-indSet\<^sub>0\<^sub>1") 
  where "z,f-indSet\<^sub>0\<^sub>1 \<equiv> \<Inter>(z,f-closed\<^sub>0\<^sub>1)"
definition inductiveSet02 :: "'a \<Rightarrow> EOp\<^sub>2('a) \<Rightarrow> Set('a)" ("_,_-indSet\<^sub>0\<^sub>2") 
  where "z,g-indSet\<^sub>0\<^sub>2 \<equiv> \<Inter>(z,g-closed\<^sub>0\<^sub>2)" 
\<comment> \<open>and so on ...\<close>

declare inductiveSet01_def[ind_defs] inductiveSet02_def[ind_defs]

definition inductiveSetGen1 :: "EOp('a) \<Rightarrow> Set('a) \<Rightarrow> Set('a)" ("_-indSetGen\<^sub>1") 
  where "f-indSetGen\<^sub>1 G \<equiv> \<Inter>(f-closedGen\<^sub>1 G)"
definition inductiveSetGen2 :: "EOp\<^sub>2('a) \<Rightarrow> Set('a) \<Rightarrow> Set('a)" ("_-indSetGen\<^sub>2") 
  where "g-indSetGen\<^sub>2 G \<equiv> \<Inter>(g-closedGen\<^sub>2 G)"
\<comment> \<open>...and so on\<close>

declare inductiveSetGen1_def[ind_defs] inductiveSetGen2_def[ind_defs] 

lemma inductiveSet01_def2: "z,f-indSet\<^sub>0\<^sub>1 = f-indSetGen\<^sub>1 {z}" unfolding ind_defs func_defs comb_defs by simp
lemma inductiveSet02_def2: "z,g-indSet\<^sub>0\<^sub>2 = g-indSetGen\<^sub>2 {z}" unfolding ind_defs func_defs comb_defs by simp 
\<comment> \<open>...and so on\<close>

text \<open>We now provide the corresponding induction rules for the above definitions.\<close>
lemma induction01: "S z \<Longrightarrow> f-closed\<^sub>1 S \<Longrightarrow> z,f-indSet\<^sub>0\<^sub>1 \<subseteq> S"
  unfolding ind_defs func_defs comb_defs by auto
lemma induction02: "S z \<Longrightarrow> g-closed\<^sub>2 S \<Longrightarrow> z,g-indSet\<^sub>0\<^sub>2 \<subseteq> S"
  unfolding ind_defs func_defs comb_defs by metis
lemma inductionGen1: "G \<subseteq> S \<Longrightarrow> f-closed\<^sub>1 S \<Longrightarrow> f-indSetGen\<^sub>1 G \<subseteq> S"
  unfolding ind_defs func_defs comb_defs by auto
lemma inductionGen2: "G \<subseteq> S \<Longrightarrow> g-closed\<^sub>2 S \<Longrightarrow> g-indSetGen\<^sub>2 G \<subseteq> S"
  unfolding ind_defs func_defs comb_defs by metis
\<comment> \<open>...and so on\<close>

text \<open>Some useful lemmata.\<close>
lemma image_indSet01: "image h (z,f-indSet\<^sub>0\<^sub>1) = \<Inter>((image \<circ> image) h (z,f-closed\<^sub>0\<^sub>1))" 
  by (simp add: image_distr_biginter inductiveSet01_def op01_ClosureSystem)
lemma preimage_indSet01: "preimage h (z,f-indSet\<^sub>0\<^sub>1) = \<Inter>((image \<circ> preimage) h (z,f-closed\<^sub>0\<^sub>1))" 
  by (simp add: preimage_distr_biginter inductiveSet01_def op01_ClosureSystem)
lemma image_indSet02: "image h (z,g-indSet\<^sub>0\<^sub>2) = \<Inter>((image \<circ> image) h (z,g-closed\<^sub>0\<^sub>2))" 
  by (simp add: image_distr_biginter inductiveSet02_def op02_ClosureSystem)
lemma preimage_indSet02: "preimage h (z,g-indSet\<^sub>0\<^sub>2) = \<Inter>((image \<circ> preimage) h (z,g-closed\<^sub>0\<^sub>2))" 
  by (simp add: preimage_distr_biginter inductiveSet02_def op02_ClosureSystem)
lemma image_indSetGen1: "image h (f-indSetGen\<^sub>1 G) = \<Inter>((image \<circ> image) h (f-closedGen\<^sub>1 G))" 
  by (simp add: image_distr_biginter inductiveSetGen1_def opGen1_ClosureSystem)
lemma preimage_indSetGen1: "preimage h (f-indSetGen\<^sub>1 G) = \<Inter>((image \<circ> preimage) h (f-closedGen\<^sub>1 G))" 
  by (simp add: preimage_distr_biginter inductiveSetGen1_def opGen1_ClosureSystem)
lemma image_indSetGen2: "image h (f-indSetGen\<^sub>2 G) = \<Inter>((image \<circ> image) h (f-closedGen\<^sub>2 G))" 
  by (simp add: image_distr_biginter inductiveSetGen2_def opGen2_ClosureSystem)
lemma preimage_indSetGen2: "preimage h (f-indSetGen\<^sub>2 G) = \<Inter>((image \<circ> preimage) h (f-closedGen\<^sub>2 G))" 
  by (simp add: preimage_distr_biginter inductiveSetGen2_def opGen2_ClosureSystem)


subsection \<open>Function Powers\<close>

text \<open>The set of all powers (via iterated composition) for a given endofunction \<open>f\<close> can be defined 
 in two ways. First, by taking composition \<open>(\<circ>)\<close> as a binary constructor (with \<open>f\<close> as the generator).
 Second, by taking \<open>(\<circ>) f\<close> as a unary constructor (with \<open>\<^bold>I\<close> as the generator).\<close>
definition funPower :: "ERel(EOp('a))"
  where "funPower f \<equiv> f,(\<circ>)-indSet\<^sub>0\<^sub>2"
definition funPower0::"ERel(EOp('a))"
  where "funPower0 f \<equiv> \<^bold>I,((\<circ>) f)-indSet\<^sub>0\<^sub>1"

declare funPower_def[ind_defs] funPower0_def[ind_defs]

text \<open>The first variant can also be defined with \<open>(\<circ>) f\<close> as a unary constructor and \<open>f\<close> as generator.\<close>
lemma "funPower f = f,((\<circ>) f)-indSet\<^sub>0\<^sub>1" oops (*TODO: check*)

text \<open>Extensionally, both variants differ on whether the "zero-power" (i.e. \<open>f\<^sup>0 = \<^bold>I\<close>) is included.\<close>
lemma "funPower0 f = funPower f \<union> {\<^bold>I}" oops (*TODO: check*)

text \<open>Definitions work as expected:\<close>
proposition "funPower f \<^bold>I" nitpick \<comment> \<open>countermodel found\<close> oops
lemma "funPower f f" unfolding ind_defs func_defs comb_defs by simp
lemma "funPower f (f\<circ>f)" unfolding ind_defs func_defs comb_defs by metis
lemma "funPower f (f\<circ>f\<circ>f)" unfolding ind_defs func_defs comb_defs by metis
lemma "funPower f (f\<circ>f\<circ>f\<circ>f\<circ>f\<circ>f\<circ>f\<circ>f\<circ>f\<circ>f\<circ>f\<circ>f)" unfolding ind_defs func_defs comb_defs by metis
lemma "funPower0 f \<^bold>I" unfolding ind_defs func_defs comb_defs by simp
lemma "funPower0 f f" unfolding ind_defs func_defs comb_defs by auto
lemma "funPower0 f (f\<circ>f)" unfolding ind_defs func_defs comb_defs by auto
lemma "funPower0 f (f\<circ>f\<circ>f)" unfolding ind_defs func_defs comb_defs by auto
lemma "funPower0 f (f\<circ>f\<circ>f\<circ>f\<circ>f\<circ>f\<circ>f\<circ>f\<circ>f\<circ>f\<circ>f\<circ>f)" unfolding ind_defs func_defs comb_defs by blast

lemma funPower_ind: "funPower f g \<Longrightarrow> funPower f (f \<circ> g)" unfolding ind_defs func_defs comb_defs by metis
lemma funPower0_ind: "funPower0 f g \<Longrightarrow> funPower0 f (f \<circ> g)" unfolding ind_defs func_defs comb_defs by blast

text \<open>Finally, we obtain a useful alternative (in a sense recursive) definition of inductive sets.\<close>
lemma inductiveSet01_def3: "(z,f-indSet\<^sub>0\<^sub>1) = image (\<^bold>T z) (funPower0 f)"
  apply (unfold funPower0_def) apply (unfold image_indSet01) apply(fold funClosure_prop) apply (fold inductiveSet01_def) ..
lemma "inductiveSet01 = \<^bold>B\<^sub>1\<^sub>1 image \<^bold>T funPower0" unfolding inductiveSet01_def3 comb_defs ..


subsection \<open>Relation Powers\<close>

text \<open>The set of all powers (via iterated composition) for a given endorelation \<open>R\<close> can also be defined 
 in two ways. First, by taking composition \<open>(\<circ>\<^sup>r)\<close> as a binary constructor (with \<open>R\<close> as the generator).
 Second, by taking \<open>(\<circ>\<^sup>r) R\<close> as a unary constructor (with \<open>\<Q>\<close> as the generator).\<close>
definition relPower :: "ERel(ERel('a))"
  where "relPower R \<equiv> R,(\<circ>\<^sup>r)-indSet\<^sub>0\<^sub>2"
definition relPower0::"ERel(ERel('a))"
  where "relPower0 R \<equiv> \<Q>,((\<circ>\<^sup>r) R)-indSet\<^sub>0\<^sub>1"

declare relPower_def[ind_defs] relPower0_def[ind_defs]

text \<open>The first variant can also be defined with \<open>(\<circ>\<^sup>r) R\<close> as a unary constructor and \<open>R\<close> as generator.\<close>
lemma "relPower R = R,((\<circ>\<^sup>r) R)-indSet\<^sub>0\<^sub>1" oops (*TODO: check*)

text \<open>Extensionally, both variants differ on whether the "zero-power" (i.e. \<open>R\<^sup>0 = \<Q>\<close>) is included.\<close>
lemma "relPower0 R = relPower R \<union> {\<Q>}" oops (*TODO: check*)

text \<open>Definitions work as expected:\<close>
proposition "relPower R \<Q>" nitpick \<comment> \<open>countermodel found\<close> oops
lemma "relPower R R" unfolding ind_defs func_defs comb_defs by simp
lemma "relPower R (R\<circ>\<^sup>rR)" unfolding ind_defs func_defs comb_defs by metis
lemma "relPower R (R\<circ>\<^sup>rR\<circ>\<^sup>rR)" unfolding ind_defs func_defs comb_defs by auto
lemma "relPower R (R\<circ>\<^sup>rR\<circ>\<^sup>rR\<circ>\<^sup>rR\<circ>\<^sup>rR\<circ>\<^sup>rR\<circ>\<^sup>rR\<circ>\<^sup>rR\<circ>\<^sup>rR\<circ>\<^sup>rR\<circ>\<^sup>rR\<circ>\<^sup>rR)" unfolding ind_defs func_defs comb_defs by metis
lemma "relPower0 R \<Q>" unfolding ind_defs func_defs comb_defs by simp
lemma "relPower0 R R" unfolding ind_defs rel_defs func_defs comb_defs by auto
lemma "relPower0 R (R\<circ>\<^sup>rR)" unfolding ind_defs func_defs comb_defs using relComp_id2 by blast
lemma "relPower0 R (R\<circ>\<^sup>rR\<circ>\<^sup>rR)" unfolding ind_defs func_defs comb_defs by (metis relComp_assoc relComp_id2)
lemma "relPower0 R (R\<circ>\<^sup>rR\<circ>\<^sup>rR\<circ>\<^sup>rR\<circ>\<^sup>rR\<circ>\<^sup>rR\<circ>\<^sup>rR\<circ>\<^sup>rR\<circ>\<^sup>rR\<circ>\<^sup>rR\<circ>\<^sup>rR\<circ>\<^sup>rR)" unfolding ind_defs func_defs comb_defs by (metis (no_types, lifting) relComp_assoc relComp_id2)

lemma relPower_ind: "relPower R T \<Longrightarrow> relPower R (R \<circ>\<^sup>r T)" unfolding ind_defs func_defs comb_defs by metis
lemma relPower0_ind: "relPower0 R T \<Longrightarrow> relPower0 R (R \<circ>\<^sup>r T)" unfolding ind_defs func_defs comb_defs by blast

text \<open>We can relate both functional and relational power to each other\<close>
lemma "funPower f = image asFun (relPower (asRel f))" oops (*TODO: check*)
lemma "totalFunction R \<Longrightarrow> relPower R = image asRel (funPower (asFun f))" oops (*TODO: check*)

text \<open>A way to obtain an endorelation from an endo-operation\<close>
definition reachableClosure :: "('a \<Rightarrow> 'a) \<Rightarrow> ERel('a)"
  where "reachableClosure \<equiv> \<^bold>C inductiveSet01"
definition reachableClosure2 :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ERel('a)"
  where "reachableClosure2 \<equiv> \<^bold>C inductiveSet02"

declare reachableClosure_def[ind_defs] reachableClosure2_def[ind_defs]

lemma reachableClosure_def2: "reachableClosure f z = image (\<^bold>T z) (funPower0 f)"
  by (simp add: C21_comb_def inductiveSet01_def3 reachableClosure_def)
lemma reachableClosure_def2: "reachableClosure2 g z = image (\<^bold>T z) (funPower0 (g z))" oops (*TODO: check*)

lemma reachableClosure_bigunion: "\<Union>(reachableClosure f z) = \<Union>\<^sup>r(funPower0 f) z" 
  by (simp add: B10_comb_def B2_comb_def bigunionR_def reachableClosure_def2)
lemma reachableClosure_biginter: "\<Inter>(reachableClosure f z) = \<Inter>\<^sup>r(funPower0 f) z" 
  by (simp add: B10_comb_def B2_comb_def biginterR_def reachableClosure_def2)


text \<open>Natural ways to obtain transitive relations resp. preorders.\<close>
definition transitiveClosure::"ERel('a) \<Rightarrow> ERel('a)" ("_\<^sup>+")
  where "transitiveClosure \<equiv> \<Union>\<^sup>r \<circ> relPower"
definition preorderClosure::"ERel('a) \<Rightarrow> ERel('a)"  ("_\<^sup>*") \<comment> \<open>aka. reflexive-transitive closure\<close>
  where "preorderClosure \<equiv> \<Union>\<^sup>r \<circ> relPower0"

declare transitiveClosure_def [ind_defs] preorderClosure_def [ind_defs]

lemma "R\<^sup>+ = \<Union>\<^sup>r(relPower R)" unfolding ind_defs comb_defs ..
lemma "R\<^sup>* = \<Union>\<^sup>r(relPower0 R)" unfolding ind_defs comb_defs ..

lemma transitiveClosure_char: "R\<^sup>+ = \<Inter>\<^sup>r(\<lambda>T. transitive T \<and> R \<subseteq>\<^sup>r T)" \<comment> \<open>proof by external provers\<close>
  unfolding transitiveClosure_def relPower_def transitive_def2
  unfolding ind_defs rel_defs func_defs comb_defs 
  apply (rule ext)+ apply (rule iffI) oops (*TODO: prove*)

lemma "R\<^sup>* = reflexiveClosure (R\<^sup>+)" \<comment> \<open>proof by external provers\<close> oops (*TODO: prove*)


text \<open>Functional-power is a preorder.\<close>
lemma funPower0_preorder: "preorder funPower0" oops (*TODO: check*)
lemma funPower_preorder: "preorder funPower" oops (*TODO: check*)
text \<open>Relational-power is a preorder\<close>
lemma relPower_preorder: "preorder relPower" oops (*TODO: check*)
lemma relPower0_preorder: "preorder relPower0" oops (*TODO: check*)

text \<open>However, relational-power is not antisymmetric (and thus not partially ordered), because we have:\<close>
proposition "R = T \<circ>\<^sup>r T \<Longrightarrow> T = R \<circ>\<^sup>r R \<Longrightarrow> R = T" nitpick[card 'a=3] \<comment> \<open>countermodel found\<close> oops 

text \<open>Iterative-closure is a preorder\<close>
lemma "preorder (reachableClosure f)" unfolding ind_defs endorel_defs rel_defs func_defs comb_defs by metis

text \<open>Moreover.\<close>
lemma "reachableClosure f = preorderClosure (asRel f)" oops (*TODO: check*)


subsection \<open>Fixed-points\<close>

subsubsection \<open>In General\<close>

text \<open>The \<open>\<mu>\<close> resp. \<open>\<nu>\<close> operators (Beware: in our approach they are NOT always least- or greatest-fixedpoints).\<close>
definition mu :: "ERel('a) \<Rightarrow> EOp('a) \<Rightarrow> Set('a)" ("_-\<mu>")
  where "R-\<mu> \<equiv> R-glb \<circ> (R-preFP)"
definition nu :: "ERel('a) \<Rightarrow> EOp('a) \<Rightarrow> Set('a)" ("_-\<nu>") 
  where "R-\<nu> \<equiv> R-lub \<circ> (R-postFP)"

declare mu_def[ind_defs] nu_def[ind_defs]

text \<open>Antisymmetry resp. limit-completeness of R entails uniqueness resp. existence of \<open>R-\<mu>/\<nu>\<close>\<close>
lemma mu_unique: "antisymmetric R \<Longrightarrow> unique (R-\<mu> f)" by (simp add: B1_comb_def \<Phi>21_comb_def antisymm_greatest_unique glb_def mu_def partial_order_def)
lemma nu_unique: "antisymmetric R \<Longrightarrow> unique (R-\<nu> f)" by (simp add: B1_comb_def \<Phi>21_comb_def antisymm_least_unique lub_def nu_def partial_order_def)
lemma mu_exists: "limitComplete R \<Longrightarrow> \<exists>(R-\<mu> f)" by (simp add: B1_comb_def B2_comb_def limitComplete_def2 mu_def)
lemma nu_exists: "limitComplete R \<Longrightarrow> \<exists>(R-\<nu> f)" by (simp add: B1_comb_def B2_comb_def limitComplete_def nu_def)
lemma mu_singleton: "antisymmetric R \<Longrightarrow> limitComplete R \<Longrightarrow> \<exists>!(R-\<mu> f)" unfolding singleton_def2 inter_def comb_defs by (simp add: mu_exists mu_unique)
lemma nu_singleton: "antisymmetric R \<Longrightarrow> limitComplete R \<Longrightarrow> \<exists>!(R-\<nu> f)" unfolding singleton_def2 inter_def comb_defs by (simp add: nu_exists nu_unique)

text \<open>Now we draw the connection to the notions of least-/greatest-fixedpoints.\<close>
definition leastFixedPoint :: "ERel('a) \<Rightarrow> EOp('a) \<Rightarrow> Set('a)" ("_-lfp")
  where "R-lfp \<equiv> R-least \<circ> FP"
definition greatestFixedPoint :: "ERel('a) \<Rightarrow> EOp('a) \<Rightarrow> Set('a)" ("_-gfp")
  where "R-gfp \<equiv> R-greatest \<circ> FP"

declare leastFixedPoint_def[ind_defs] greatestFixedPoint_def[ind_defs]

text \<open>Uniqueness for lfp/gfp is strightforward.\<close>
lemma lfp_unique: "antisymmetric R \<Longrightarrow> unique (R-lfp f)" by (simp add: ind_defs B1_comb_def antisymm_least_unique)
lemma gfp_unique: "antisymmetric R \<Longrightarrow> unique (R-gfp f)" by (simp add: ind_defs B1_comb_def antisymm_greatest_unique)

text \<open>To show existence of lfp/gfp (a weak version of Knaster-Tarski theorem), we first observe that:\<close>
lemma mu_lfp: "partial_order R \<Longrightarrow> R-MONO f \<Longrightarrow> (R-\<mu> f) x \<Longrightarrow> (R-lfp f) x"
  unfolding ind_defs endorel_defs rel_defs func_defs comb_defs by metis
lemma nu_gfp: "partial_order R \<Longrightarrow> R-MONO f \<Longrightarrow> (R-\<nu> f) x \<Longrightarrow> (R-gfp f) x"
  unfolding ind_defs endorel_defs rel_defs func_defs comb_defs by metis
\<comment> \<open>and thus\<close>
lemma lfp_exists: "partial_order R \<Longrightarrow> limitComplete R \<Longrightarrow> R-MONO f \<Longrightarrow> \<exists>(R-lfp f)" 
  by (meson mu_exists mu_lfp)
lemma gfp_exists: "partial_order R \<Longrightarrow> limitComplete R \<Longrightarrow> R-MONO f \<Longrightarrow> \<exists>(R-gfp f)" 
  by (meson nu_exists nu_gfp)
\<comment> \<open>therefore\<close>
lemma lfp_singleton: "partial_order R \<Longrightarrow> limitComplete R \<Longrightarrow> R-MONO f \<Longrightarrow> \<exists>!(R-lfp f)"
  by (simp add: \<Phi>21_comb_def inter_def lfp_exists lfp_unique partial_order_def singleton_def2)
lemma gfp_singleton: "partial_order R \<Longrightarrow> limitComplete R \<Longrightarrow> R-MONO f \<Longrightarrow> \<exists>!(R-gfp f)"
  by (simp add: \<Phi>21_comb_def gfp_exists gfp_unique inter_def partial_order_def singleton_def2)

text \<open>\<open>\<mu>\<close> resp. \<open>\<nu>\<close> are the least resp. greatest-fixedpoints for R-preserving functions, when R is a complete lattice.\<close>
lemma mu_def2: "partial_order R \<Longrightarrow> limitComplete R \<Longrightarrow> R-MONO f \<Longrightarrow> R-\<mu> f = R-lfp f"
  by (metis (full_types) lfp_singleton mu_lfp mu_singleton partial_order_def singleton_def3)
lemma nu_def2: "partial_order R \<Longrightarrow> limitComplete R \<Longrightarrow> R-MONO f \<Longrightarrow> R-\<nu> f = R-gfp f"
  by (metis (full_types) gfp_singleton nu_gfp nu_singleton partial_order_def singleton_def3)


subsubsection \<open>For Sets and Relations\<close>

definition setMu :: "SetEOp('a) \<Rightarrow> Set('a)" ("\<mu>")
  where "\<mu> \<equiv> \<Inter> \<circ> (\<subseteq>)-preFP"
definition setNu :: "SetEOp('a) \<Rightarrow> Set('a)" ("\<nu>") 
  where "\<nu> \<equiv> \<Union> \<circ> (\<subseteq>)-postFP"
definition relMu :: "(Rel('a,'b) \<Rightarrow> Rel('a,'b)) \<Rightarrow> Rel('a,'b)" ("\<mu>\<^sup>r")
  where "\<mu>\<^sup>r \<equiv> \<Inter>\<^sup>r \<circ> (\<subseteq>\<^sup>r)-preFP"
definition relNu :: "(Rel('a,'b) \<Rightarrow> Rel('a,'b)) \<Rightarrow> Rel('a,'b)" ("\<nu>\<^sup>r")
  where "\<nu>\<^sup>r \<equiv> \<Union>\<^sup>r \<circ> (\<subseteq>\<^sup>r)-postFP"

declare setMu_def[ind_defs] setNu_def[ind_defs] 
        relMu_def[ind_defs] relNu_def[ind_defs]

text \<open>For illustration: the definitions unfold as follows:\<close>
lemma "\<mu> = (\<lambda>F x. \<forall>A. (F A \<subseteq> A) \<rightarrow> A x)" unfolding ind_defs func_defs comb_defs ..
lemma "\<nu> = (\<lambda>F x. \<exists>A. (F A \<supseteq> A) \<and> A x)" unfolding ind_defs func_defs comb_defs ..
lemma "\<mu> = (\<lambda>F x. \<forall>A. (\<forall>b. F A b \<rightarrow> A b) \<rightarrow> A x)" unfolding ind_defs func_defs comb_defs ..
lemma "\<nu> = (\<lambda>F x. \<exists>A. (\<forall>b. A b \<rightarrow> F A b) \<and> A x)" unfolding ind_defs func_defs comb_defs ..

text \<open>As a corollary, in the case of sets and relations, we have that:\<close>
lemma setMu_singleton: "singleton ((\<subseteq>)-\<mu> f)" using mu_singleton partial_order_def subset_limitComplete subset_partial_order by auto
lemma setNu_singleton: "singleton ((\<subseteq>)-\<nu> f)" using nu_singleton partial_order_def subset_limitComplete subset_partial_order by auto
lemma relMu_singleton: "singleton ((\<subseteq>\<^sup>r)-\<mu> R)" using mu_singleton partial_order_def subrel_limitComplete subrel_partial_order by auto
lemma relNu_singleton: "singleton ((\<subseteq>\<^sup>r)-\<nu> R)" using nu_singleton partial_order_def subrel_limitComplete subrel_partial_order by auto

text \<open>They are clearly (unique) instances of the general variants.\<close>
lemma setMu_simp: "\<iota> \<circ> (\<subseteq>)-\<mu> = \<mu> "
  using mu_unique partial_order_def subset_partial_order biginter_glb unfolding unique_def ind_defs comb_defs by blast
lemma setNu_simp: "\<iota> \<circ> (\<subseteq>)-\<nu> = \<nu>"
  using nu_unique partial_order_def subset_partial_order bigunion_lub unfolding unique_def ind_defs comb_defs by blast
lemma relMu_simp: "\<iota> \<circ> (\<subseteq>\<^sup>r)-\<mu> = \<mu>\<^sup>r"
  using mu_unique partial_order_def subrel_partial_order biginterR_glb unfolding unique_def ind_defs comb_defs by blast
lemma relNu_simp: "\<iota> \<circ> (\<subseteq>\<^sup>r)-\<nu> = \<nu>\<^sup>r"
  using nu_unique partial_order_def subrel_partial_order bigunionR_lub unfolding unique_def ind_defs comb_defs by blast

text \<open>Clearly, \<open>\<mu>\<close> resp. \<open>\<nu>\<close> are the least resp. greatest-fixedpoints for subset/subrel-monotonic set-operations.\<close>
lemma setMu_def2: "(\<subseteq>)-MONO f \<Longrightarrow> \<mu> f = \<iota>((\<subseteq>)-lfp f)" 
  by (simp add: B1_comb_def mu_def2 setMu_simp[symmetric] subset_limitComplete subset_partial_order)
lemma setNu_def2: "(\<subseteq>)-MONO f \<Longrightarrow> \<nu> f = \<iota>((\<subseteq>)-gfp f)" 
  by (simp add: B1_comb_def nu_def2 setNu_simp[symmetric] subset_limitComplete subset_partial_order)
lemma relMu_def2: "(\<subseteq>\<^sup>r)-MONO f \<Longrightarrow> \<mu>\<^sup>r f = \<iota>((\<subseteq>\<^sup>r)-lfp f)" 
  by (simp add: B1_comb_def mu_def2 relMu_simp[symmetric] subrel_limitComplete subrel_partial_order)
lemma relNu_def2: "(\<subseteq>\<^sup>r)-MONO f \<Longrightarrow> \<nu>\<^sup>r f = \<iota>((\<subseteq>\<^sup>r)-gfp f)" 
  by (simp add: B1_comb_def nu_def2 relNu_simp[symmetric] subrel_limitComplete subrel_partial_order)

text \<open>We introduce the customary binder notation.\<close>
notation setMu (binder "\<mu>" 10) and setNu (binder "\<nu>" 10)
notation relMu (binder "\<mu>\<^sup>r" 10) and relNu (binder "\<nu>\<^sup>r" 10)

text \<open>Check notation\<close>
lemma "(\<nu> X. \<phi>) = \<nu>(\<lambda>X. \<phi>)" ..
lemma "(\<mu> X. \<phi>) = \<mu>(\<lambda>X. \<phi>)" ..

text \<open>Some useful theorems.\<close>
lemma preFP_dual1: "(\<subseteq>)-preFP f\<^sup>d = ((\<subseteq>)-postFP f) \<circ> \<midarrow>" 
  unfolding func_defs comb_defs by auto
lemma preFP_dual2: "(\<subseteq>)-preFP f\<^sup>d = image (\<midarrow>) ((\<subseteq>)-postFP f)" 
  by (simp add: C21_comb_def compl_invol invol_image preFP_dual1)
lemma postFP_dual1:"(\<subseteq>)-postFP f\<^sup>d = ((\<subseteq>)-preFP f) \<circ> \<midarrow>" 
  unfolding func_defs comb_defs by auto
lemma postFP_dual2:"(\<subseteq>)-postFP f\<^sup>d = image (\<midarrow>) ((\<subseteq>)-preFP f)"
  by (simp add: C21_comb_def compl_invol invol_image postFP_dual1)

text \<open>Check theorems\<close>
lemma setMu_dualdef: "\<mu> = \<midarrow> \<circ> \<nu> \<circ> dualop" unfolding ind_defs comb_defs by (metis compl_bigdeMorgan2 compl_involutive postFP_dual2)
lemma setNu_dualdef: "\<nu> = \<midarrow> \<circ> \<mu> \<circ> dualop" unfolding ind_defs comb_defs by (metis compl_bigdeMorgan1 compl_involutive preFP_dual2)
lemma "(\<mu> X. \<phi> X) = \<midarrow>(\<nu> X. \<phi>\<^sup>d X)" unfolding setMu_dualdef comb_defs ..
lemma "(\<nu> X. \<phi> X) = \<midarrow>(\<mu> X. \<phi>\<^sup>d X)" unfolding setNu_dualdef comb_defs ..

end