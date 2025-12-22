theory induction
  imports diagrams spaces
begin

section \<open>Induction, Fixed-points & co.\<close>

named_theorems ind_defs

subsection \<open>Inductively-generated Sets\<close>

text \<open>The "smallest" set containing a set of generators and closed under an n-ary operation.\<close>
definition inductiveSetGen1 :: "EOp('a) \<Rightarrow> Set('a) \<Rightarrow> Set('a)" ("_-indSetGen\<^sub>1") 
  where "f-indSetGen\<^sub>1 G \<equiv> \<Inter>(f-closedGen\<^sub>1 G)"
definition inductiveSetGen2 :: "EOp\<^sub>2('a) \<Rightarrow> Set('a) \<Rightarrow> Set('a)" ("_-indSetGen\<^sub>2") 
  where "g-indSetGen\<^sub>2 G \<equiv> \<Inter>(g-closedGen\<^sub>2 G)"
\<comment> \<open>...and so on\<close>

text \<open>Inductive set with no generators but closed under (i.e. containing) a nullary "zero" operation.\<close>
definition inductiveSet01 :: "'a \<Rightarrow> EOp('a) \<Rightarrow> Set('a)" ("_,_-indSet\<^sub>0\<^sub>1") 
  where "z,f-indSet\<^sub>0\<^sub>1 \<equiv> \<Inter>(z,f-closed\<^sub>0\<^sub>1)"
definition inductiveSet02 :: "'a \<Rightarrow> EOp\<^sub>2('a) \<Rightarrow> Set('a)" ("_,_-indSet\<^sub>0\<^sub>2") 
  where "z,g-indSet\<^sub>0\<^sub>2 \<equiv> \<Inter>(z,g-closed\<^sub>0\<^sub>2)" 
\<comment> \<open>and so on ...\<close>

declare inductiveSetGen1_def[ind_defs] inductiveSetGen2_def[ind_defs] 
        inductiveSet01_def[ind_defs] inductiveSet02_def[ind_defs]

lemma inductiveSet01_def2: "z,f-indSet\<^sub>0\<^sub>1 = f-indSetGen\<^sub>1 {z}" unfolding ind_defs space_defs func_defs comb_defs by simp
lemma inductiveSet02_def2: "z,g-indSet\<^sub>0\<^sub>2 = g-indSetGen\<^sub>2 {z}" unfolding ind_defs space_defs func_defs comb_defs by simp 
\<comment> \<open>...and so on\<close>

text \<open>We now provide the corresponding induction rules for the above definitions.\<close>
lemma induction01: "S z \<Longrightarrow> f-closed\<^sub>1 S \<Longrightarrow> z,f-indSet\<^sub>0\<^sub>1 \<subseteq> S"
  unfolding ind_defs space_defs func_defs comb_defs by auto
lemma induction02: "S z \<Longrightarrow> g-closed\<^sub>2 S \<Longrightarrow> z,g-indSet\<^sub>0\<^sub>2 \<subseteq> S"
  unfolding ind_defs space_defs func_defs comb_defs by metis
\<comment> \<open>...and so on\<close>
lemma inductionGen1: "G \<subseteq> S \<Longrightarrow> f-closed\<^sub>1 S \<Longrightarrow> f-indSetGen\<^sub>1 G \<subseteq> S"
  unfolding ind_defs space_defs func_defs comb_defs by auto
lemma inductionGen2: "G \<subseteq> S \<Longrightarrow> g-closed\<^sub>2 S \<Longrightarrow> g-indSetGen\<^sub>2 G \<subseteq> S"
  unfolding ind_defs space_defs func_defs comb_defs by metis
\<comment> \<open>...and so on\<close>

text \<open>Some useful lemmata.\<close>
lemma image_indSet01: "image h (z,f-indSet\<^sub>0\<^sub>1) = \<Inter>((image \<ggreater> image) h (z,f-closed\<^sub>0\<^sub>1))" 
  by (simp add: image_distr_biginter inductiveSet01_def op01_ClosureSystem)

lemma preimage_indSet01: "preimage h (z,f-indSet\<^sub>0\<^sub>1) = \<Inter>((preimage \<ggreater> image) h (z,f-closed\<^sub>0\<^sub>1))" 
  by (simp add: preimage_distr_biginter inductiveSet01_def op01_ClosureSystem)

lemma image_indSet02: "image h (z,g-indSet\<^sub>0\<^sub>2) = \<Inter>((image \<ggreater> image) h (z,g-closed\<^sub>0\<^sub>2))" 
  by (simp add: image_distr_biginter inductiveSet02_def op02_ClosureSystem)

lemma preimage_indSet02: "preimage h (z,g-indSet\<^sub>0\<^sub>2) = \<Inter>((preimage \<ggreater> image) h (z,g-closed\<^sub>0\<^sub>2))" 
  by (simp add: preimage_distr_biginter inductiveSet02_def op02_ClosureSystem)

lemma image_indSetGen1: "image h (f-indSetGen\<^sub>1 G) = \<Inter>((image \<ggreater> image) h (f-closedGen\<^sub>1 G))" 
  by (simp add: image_distr_biginter inductiveSetGen1_def opGen1_ClosureSystem)

lemma preimage_indSetGen1: "preimage h (f-indSetGen\<^sub>1 G) = \<Inter>((preimage \<ggreater> image) h (f-closedGen\<^sub>1 G))" 
  by (simp add: preimage_distr_biginter inductiveSetGen1_def opGen1_ClosureSystem)

lemma image_indSetGen2: "image h (f-indSetGen\<^sub>2 G) = \<Inter>((image \<ggreater> image) h (f-closedGen\<^sub>2 G))" 
  by (simp add: image_distr_biginter inductiveSetGen2_def opGen2_ClosureSystem)

lemma preimage_indSetGen2: "preimage h (f-indSetGen\<^sub>2 G) = \<Inter>((preimage \<ggreater> image) h (f-closedGen\<^sub>2 G))" 
  by (simp add: preimage_distr_biginter inductiveSetGen2_def opGen2_ClosureSystem)


subsection \<open>Function Powers\<close>

text \<open>The set of all powers (via iterated composition) for a given endofunction \<open>f\<close> can be defined 
 in two ways. First, by taking composition \<open>(\<circ>)\<close> as a binary constructor (with \<open>f\<close> as the generator).
 Second, by taking \<open>(\<ggreater>) f\<close> as a unary constructor (with \<open>\<^bold>I\<close> as the generator).\<close>
definition funPower :: "ERel(EOp('a))"
  where "funPower f \<equiv> f,(\<ggreater>)-indSet\<^sub>0\<^sub>2"
definition funPower0::"ERel(EOp('a))"
  where "funPower0 f \<equiv> \<^bold>I,((\<ggreater>) f)-indSet\<^sub>0\<^sub>1"

declare funPower_def[ind_defs] funPower0_def[ind_defs]

text \<open>Definitions work as expected:\<close>
proposition "funPower f \<^bold>I" nitpick \<comment> \<open>countermodel found\<close> oops
lemma "funPower f f" unfolding ind_defs space_defs func_defs comb_defs by simp
lemma "funPower f (f\<ggreater>f)" unfolding ind_defs space_defs func_defs comb_defs by metis
lemma "funPower f (f\<ggreater>f\<ggreater>f)" unfolding ind_defs space_defs func_defs comb_defs by metis
lemma "funPower f (f\<ggreater>f\<ggreater>f\<ggreater>f\<ggreater>f\<ggreater>f\<ggreater>f\<ggreater>f\<ggreater>f\<ggreater>f\<ggreater>f\<ggreater>f)" unfolding ind_defs space_defs func_defs comb_defs by metis
lemma "funPower0 f \<^bold>I" unfolding ind_defs space_defs func_defs comb_defs by simp
lemma "funPower0 f f" unfolding ind_defs space_defs func_defs comb_defs by auto
lemma "funPower0 f (f\<ggreater>f)" unfolding ind_defs space_defs func_defs comb_defs by auto
lemma "funPower0 f (f\<ggreater>f\<ggreater>f)" unfolding ind_defs space_defs func_defs comb_defs by auto
lemma "funPower0 f (f\<ggreater>f\<ggreater>f\<ggreater>f\<ggreater>f\<ggreater>f\<ggreater>f\<ggreater>f\<ggreater>f\<ggreater>f\<ggreater>f\<ggreater>f)" unfolding ind_defs space_defs func_defs comb_defs by blast

lemma funPower_comp1: "funPower f g \<Longrightarrow> funPower f (f \<ggreater> g)" unfolding ind_defs space_defs func_defs comb_defs by metis
lemma funPower_comp2: "funPower f g \<Longrightarrow> funPower f (g \<ggreater> f)" unfolding ind_defs space_defs func_defs comb_defs by metis
lemma funPower0_comp1: "funPower0 f g \<Longrightarrow> funPower0 f (f \<ggreater> g)" unfolding ind_defs space_defs func_defs comb_defs by blast
lemma funPower0_comp2: "funPower0 f g \<Longrightarrow> funPower0 f (g \<ggreater> f)" sorry (*TODO: fix kernel reconstruction*)

text \<open>The first variant can also be defined with \<open>(\<circ>) f\<close> as a unary constructor and \<open>f\<close> as generator.\<close>
lemma "funPower f = f,((\<ggreater>) f)-indSet\<^sub>0\<^sub>1" oops (*TODO: check*)

text \<open>Extensionally, both variants differ on whether the "zero-power" (i.e. \<open>f\<^sup>0 = \<^bold>I\<close>) is included.\<close>
lemma "funPower0 f = funPower f \<union> {\<^bold>I}" oops (*TODO: check*)
  

text \<open>Finally, we obtain a useful alternative (in a sense recursive) definition of inductive sets.\<close>
lemma inductiveSet01_def3: "(z,f-indSet\<^sub>0\<^sub>1) = image (\<^bold>T z) (funPower0 f)"
  apply (unfold funPower0_def) apply (unfold image_indSet01) apply(fold funClosure_prop) apply (fold inductiveSet01_def) ..
lemma "inductiveSet01 = \<^bold>B\<^sub>1\<^sub>1 image \<^bold>T funPower0" unfolding inductiveSet01_def3 comb_defs ..


subsection \<open>Relation Powers\<close>

text \<open>The set of all powers (via iterated composition) for a given endorelation \<open>R\<close> can also be defined 
 in two ways. First, by taking composition \<open>(;)\<close> as a binary constructor (with \<open>R\<close> as the generator).
 Second, by taking \<open>(;) R\<close> as a unary constructor (with \<open>\<Q>\<close> as the generator).\<close>
definition relPower :: "ERel(ERel('a))"
  where "relPower R \<equiv> R,(;)-indSet\<^sub>0\<^sub>2"
definition relPower0::"ERel(ERel('a))"
  where "relPower0 R \<equiv> \<Q>,((;) R)-indSet\<^sub>0\<^sub>1"

declare relPower_def[ind_defs] relPower0_def[ind_defs]

text \<open>The first variant can also be defined with \<open>(;) R\<close> as a unary constructor and \<open>R\<close> as generator.\<close>
lemma "relPower R = R,((;) R)-indSet\<^sub>0\<^sub>1" unfolding rel_defs ind_defs space_defs func_defs comb_defs 
  apply (rule ext)+ apply safe defer apply (metis (no_types, lifting) ext) oops (*TODO: check*)

text \<open>Extensionally, both variants differ on whether the "zero-power" (i.e. \<open>R\<^sup>0 = \<Q>\<close>) is included.\<close>
lemma "relPower0 R = relPower R \<union> {\<Q>}" oops (*TODO: check*)

text \<open>Definitions work as expected:\<close>
proposition "relPower R \<Q>" nitpick \<comment> \<open>countermodel found\<close> oops
lemma "relPower R R" unfolding ind_defs space_defs func_defs comb_defs by simp
lemma "relPower R (R ; R)" unfolding ind_defs space_defs func_defs comb_defs by metis
lemma "relPower R (R ; R ; R)" unfolding ind_defs space_defs func_defs comb_defs by metis
lemma "relPower R (R ; R ; R ; R ; R ; R ; R ; R ; R ; R ; R ; R)" unfolding ind_defs space_defs func_defs comb_defs by metis
lemma "relPower0 R \<Q>" unfolding ind_defs space_defs func_defs comb_defs by simp
lemma "relPower0 R R" unfolding ind_defs space_defs rel_defs func_defs comb_defs by auto
lemma "relPower0 R (R ; R)" unfolding ind_defs space_defs func_defs comb_defs using relComp_id2 by blast
lemma "relPower0 R (R ; R ; R)" unfolding ind_defs space_defs func_defs comb_defs by (metis relComp_assoc relComp_id2)
lemma "relPower0 R (R ; R ; R ; R ; R ; R ; R ; R ; R ; R ; R ; R)" unfolding ind_defs space_defs func_defs comb_defs by (metis (no_types, lifting) relComp_assoc relComp_id2)

lemma relPower_ind: "relPower R T \<Longrightarrow> relPower R (R ; T)" unfolding ind_defs space_defs func_defs comb_defs by metis
lemma relPower0_ind: "relPower0 R T \<Longrightarrow> relPower0 R (R ; T)" unfolding ind_defs space_defs func_defs comb_defs by blast

text \<open>We can relate both functional and relational power to each other.\<close>
lemma "funPower f = image asFun (relPower (asRel f))" oops (*TODO: check*)
lemma "totalFunction R \<Longrightarrow> relPower R = image asRel (funPower (asFun f))" oops (*TODO: check*)


text \<open>A way to obtain an endorelation from an n-ary endo-operation.\<close>
definition iterativeClosure :: "EOp('a) \<Rightarrow> ERel('a)"
  where "iterativeClosure \<equiv> \<^bold>C inductiveSet01"
definition iterativeClosure2 :: "EOp\<^sub>2('a) \<Rightarrow> ERel('a)"
  where "iterativeClosure2 \<equiv> \<^bold>C inductiveSet02"
\<comment> \<open>...and so on\<close>

declare iterativeClosure_def[ind_defs] iterativeClosure2_def[ind_defs]

lemma iterativeClosure_def2: "iterativeClosure f z = image (\<^bold>T z) (funPower0 f)"
  by (simp add: C21_comb_def inductiveSet01_def3 iterativeClosure_def)
lemma iterativeClosure2_def2: "iterativeClosure2 g z = image (\<^bold>T z) (funPower0 (g z))" 
  oops (*TODO: check*)

lemma iterativeClosure_bigunion: "\<Union>(iterativeClosure f z) = \<Union>\<^sup>r(funPower0 f) z" 
  by (simp add: B10_comb_def B2_comb_def bigunionR_def iterativeClosure_def2)
lemma iterativeClosure_biginter: "\<Inter>(iterativeClosure f z) = \<Inter>\<^sup>r(funPower0 f) z" 
  by (simp add: B10_comb_def B2_comb_def biginterR_def iterativeClosure_def2)

lemma iterativeClosure_nonEmpty: "\<exists>(iterativeClosure f z)" unfolding ind_defs space_defs func_defs comb_defs by blast


text \<open>Natural ways to obtain transitive relations resp. preorders.\<close>
definition transitiveClosure::"ERel('a) \<Rightarrow> ERel('a)" ("_\<^sup>+")
  where "transitiveClosure \<equiv> relPower \<ggreater> \<Union>\<^sup>r"
definition preorderClosure::"ERel('a) \<Rightarrow> ERel('a)"  ("_\<^sup>*") \<comment> \<open>aka. reflexive-transitive closure\<close>
  where "preorderClosure \<equiv>  relPower0 \<ggreater> \<Union>\<^sup>r"

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
proposition "R = T ; T \<Longrightarrow> T = R ; R \<Longrightarrow> R = T" nitpick[card 'a=3] \<comment> \<open>countermodel found\<close> oops 

text \<open>Iterative-closure is a preorder\<close>
lemma "preorder (iterativeClosure f)" unfolding ind_defs space_defs endorel_defs rel_defs func_defs comb_defs by metis

text \<open>Moreover.\<close>
lemma "iterativeClosure f = preorderClosure (asRel f)" oops (*TODO: check*)

text \<open>The iterative-closure of a monotonic set-operator when applied to the empty set builds a chain.\<close>
lemma iterativeClosure_prop1: "(\<subseteq>)-MONO f \<Longrightarrow> (\<subseteq>)-chain (iterativeClosure f \<emptyset>)"
  sorry (*TODO: prove*)

text \<open>The iterative-closure "absorbs" the function.\<close>
lemma iterativeClosure_prop2: "(\<subseteq>)-MONO f \<Longrightarrow> \<Union>(image f (iterativeClosure f \<emptyset>)) = (\<Union>(iterativeClosure f \<emptyset>))"
  sorry (*TODO: prove (monotonicity required?)*)


subsection \<open>Fixed-points\<close>

subsubsection \<open>In General\<close>

text \<open>The \<open>\<mu>\<close> resp. \<open>\<nu>\<close> operators (Beware: in our approach they are NOT always least- or greatest-fixedpoints).\<close>
definition mu :: "ERel('a) \<Rightarrow> EOp('a) \<Rightarrow> Set('a)" ("_-\<mu>")
  where "R-\<mu> \<equiv> R-preFP \<ggreater> R-glb"
definition nu :: "ERel('a) \<Rightarrow> EOp('a) \<Rightarrow> Set('a)" ("_-\<nu>") 
  where "R-\<nu> \<equiv> R-postFP \<ggreater> R-lub"

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
  where "R-lfp \<equiv> FP \<ggreater> R-least"
definition greatestFixedPoint :: "ERel('a) \<Rightarrow> EOp('a) \<Rightarrow> Set('a)" ("_-gfp")
  where "R-gfp \<equiv> FP \<ggreater> R-greatest"

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
  where "\<mu> \<equiv> (\<subseteq>)-preFP \<ggreater> \<Inter>"
definition setNu :: "SetEOp('a) \<Rightarrow> Set('a)" ("\<nu>") 
  where "\<nu> \<equiv> (\<subseteq>)-postFP \<ggreater> \<Union>"
definition relMu :: "(Rel('a,'b) \<Rightarrow> Rel('a,'b)) \<Rightarrow> Rel('a,'b)" ("\<mu>\<^sup>r")
  where "\<mu>\<^sup>r \<equiv> (\<subseteq>\<^sup>r)-preFP \<ggreater> \<Inter>\<^sup>r"
definition relNu :: "(Rel('a,'b) \<Rightarrow> Rel('a,'b)) \<Rightarrow> Rel('a,'b)" ("\<nu>\<^sup>r")
  where "\<nu>\<^sup>r \<equiv> (\<subseteq>\<^sup>r)-postFP \<ggreater> \<Union>\<^sup>r"

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
lemma setMu_simp: "(\<subseteq>)-\<mu> \<ggreater> \<iota> = \<mu> "
  using mu_unique partial_order_def subset_partial_order biginter_glb unfolding unique_def ind_defs comb_defs by blast
lemma setNu_simp: "(\<subseteq>)-\<nu> \<ggreater> \<iota> = \<nu>"
  using nu_unique partial_order_def subset_partial_order bigunion_lub unfolding unique_def ind_defs comb_defs by blast
lemma relMu_simp: "(\<subseteq>\<^sup>r)-\<mu> \<ggreater> \<iota> = \<mu>\<^sup>r"
  using mu_unique partial_order_def subrel_partial_order biginterR_glb unfolding unique_def ind_defs comb_defs by blast
lemma relNu_simp: "(\<subseteq>\<^sup>r)-\<nu> \<ggreater> \<iota>  = \<nu>\<^sup>r"
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
lemma preFP_dual1: "(\<subseteq>)-preFP f\<^sup>d = \<midarrow> \<ggreater> ((\<subseteq>)-postFP f)" 
  unfolding func_defs comb_defs by auto
lemma preFP_dual2: "(\<subseteq>)-preFP f\<^sup>d = image (\<midarrow>) ((\<subseteq>)-postFP f)" 
  by (simp add: C21_comb_def compl_invol invol_image preFP_dual1)
lemma postFP_dual1:"(\<subseteq>)-postFP f\<^sup>d = \<midarrow> \<ggreater> ((\<subseteq>)-preFP f)" 
  unfolding func_defs comb_defs by auto
lemma postFP_dual2:"(\<subseteq>)-postFP f\<^sup>d = image (\<midarrow>) ((\<subseteq>)-preFP f)"
  by (simp add: C21_comb_def compl_invol invol_image postFP_dual1)

text \<open>Check theorems\<close>
lemma setMu_dualdef: "\<mu> = dualop \<ggreater> \<nu> \<ggreater> \<midarrow>" unfolding ind_defs comb_defs by (metis compl_bigdeMorgan2 compl_involutive postFP_dual2)
lemma setNu_dualdef: "\<nu> = dualop \<ggreater> \<mu> \<ggreater> \<midarrow>" unfolding ind_defs comb_defs by (metis compl_bigdeMorgan1 compl_involutive preFP_dual2)
lemma "(\<mu> X. \<phi> X) = \<midarrow>(\<nu> X. \<phi>\<^sup>d X)" unfolding setMu_dualdef comb_defs ..
lemma "(\<nu> X. \<phi> X) = \<midarrow>(\<mu> X. \<phi>\<^sup>d X)" unfolding setNu_dualdef comb_defs ..


text \<open>A "step" in a generative process wrt. a set G of generators and a constructor function F.)\<close>
definition genStep :: "EOp('a) \<Rightarrow> Set('a) \<Rightarrow> SetEOp('a)"
  where "genStep \<equiv> \<lambda>F G S. image F S \<union> G "

declare genStep_def[ind_defs]

text \<open>Generation-step operators are monotonic wrt. subset relation.\<close>
lemma genStep_MONO: "(\<subseteq>)-MONO (genStep F G)" unfolding ind_defs func_defs rel_defs comb_defs by auto

text \<open>From the previous we obtain alternative definition of inductive sets based on least fixed-points.\<close>
lemma opGen1_closed_def2: "opGen1_closed = genStep \<ggreater>\<^sub>2 (\<subseteq>)-preFP" unfolding ind_defs space_defs func_defs comb_defs by blast
lemma inductiveSetGen1_def2: "inductiveSetGen1 = genStep \<ggreater>\<^sub>2 \<mu>" unfolding inductiveSetGen1_def setMu_def opGen1_closed_def2 comb_defs ..
lemma inductiveSetGen1_def3: "inductiveSetGen1 = genStep \<ggreater>\<^sub>2 (\<subseteq>)-lfp \<ggreater> \<iota>" by (simp add: B1_comb_def B2_comb_def genStep_MONO inductiveSetGen1_def2 setMu_def2)

text \<open>As a corollary, the set of function-powers is the least-fixed-point of a generation-step operator.\<close>
lemma funPower0_def3: "funPower0 f = \<mu>(genStep ((\<ggreater>) f) {\<^bold>I})"
  by (simp add: B2_comb_def funPower0_def inductiveSet01_def2 inductiveSetGen1_def2)
lemma funPower0_def4: "funPower0 f = \<iota>((\<subseteq>)-lfp (genStep ((\<ggreater>) f) {\<^bold>I}))"
  by (simp add: funPower0_def3 genStep_MONO setMu_def2)


subsection \<open>Kleene Fixed-Point theorem\<close>

text \<open>We introduce some "continuity" notions useful in this context.\<close>
definition chainContinuous:: "Set(SetOp('a,'b))"
  where "chainContinuous f \<equiv> \<forall>S. \<exists>S \<rightarrow> (\<subseteq>)-chain S \<longrightarrow> f(\<Union>S) = \<Union>(image f S)"
definition scottContinuous:: "Set(SetOp('a,'b))"
  where "scottContinuous f \<equiv> \<forall>S. \<exists>S \<rightarrow> (\<subseteq>)-upwardsDirected S \<longrightarrow> f(\<Union>S) = \<Union>(image f S)"

declare chainContinuous_def[ind_defs] scottContinuous_def[ind_defs]

lemma "scottContinuous f \<Longrightarrow> chainContinuous f" 
  unfolding ind_defs using chain_upwardsDirected by auto

text \<open>A (Scott- or chain-) continuous function is monotonic wrt. set inclusion.\<close>
lemma continuous_MONO: "chainContinuous f \<Longrightarrow> (\<subseteq>)-MONO f" 
  sorry (*TODO: prove*)

lemma kleene1:  "chainContinuous f \<Longrightarrow> FP f (\<Union>(iterativeClosure f \<emptyset>))"
  by (simp add: S11_comb_def continuous_MONO chainContinuous_def fixedPoint_def postFixedPoint_def iterativeClosure_nonEmpty iterativeClosure_prop1 iterativeClosure_prop2)

lemma kleene2:  "chainContinuous f \<Longrightarrow> (\<subseteq>)-lfp f (\<Union>(iterativeClosure f \<emptyset>))"
  unfolding leastFixedPoint_def least_def leftBound_def comb_defs inter_def 
  apply safe
  apply (simp add: kleene1) 
  apply (subst subset_def, unfold relLiftAll_def comb_defs)
  unfolding bigunion_resid
  unfolding iterativeClosure_def comb_defs
  apply safe
  apply (rule induction01)
  unfolding fixedPoint_def postFixedPoint_def S11_comb_def
  apply (simp add: B3_comb_def K21_comb_def \<Phi>21_comb_def emptyset_def relLiftAll_def subset_def)
  by (metis continuous_MONO monotonic_def op1_closed_def3)

lemma kleene3:  "chainContinuous f \<Longrightarrow> \<mu> f = \<Union>(iterativeClosure f \<emptyset>)"
  apply (simp add: continuous_MONO setMu_def2)
  by (metis (full_types) continuous_MONO kleene2 lfp_singleton singleton_def3 subset_limitComplete subset_partial_order theI_unique)


end