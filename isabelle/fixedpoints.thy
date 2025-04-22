theory fixedpoints
  imports operators spaces
begin

section \<open>Fixed-points\<close>

named_theorems fp_defs

subsection \<open>In General\<close>

text \<open>The \<open>\<mu>\<close> resp. \<open>\<nu>\<close> operators (Beware: in our approach they are NOT always least- or greatest-fixedpoints).\<close>
definition mu :: "ERel('a) \<Rightarrow> EOp('a) \<Rightarrow> Set('a)" ("_-\<mu>")
  where "R-\<mu> \<equiv> R-glb \<circ> (R-preFP)"
definition nu :: "ERel('a) \<Rightarrow> EOp('a) \<Rightarrow> Set('a)" ("_-\<nu>") 
  where "R-\<nu> \<equiv> R-lub \<circ> (R-postFP)"

declare mu_def[fp_defs] nu_def[fp_defs]

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

declare leastFixedPoint_def[fp_defs] greatestFixedPoint_def[fp_defs]

text \<open>Uniqueness for lfp/gfp is strightforward.\<close>
lemma lfp_unique: "antisymmetric R \<Longrightarrow> unique (R-lfp f)" by (simp add: fp_defs B1_comb_def antisymm_least_unique)
lemma gfp_unique: "antisymmetric R \<Longrightarrow> unique (R-gfp f)" by (simp add: fp_defs B1_comb_def antisymm_greatest_unique)

text \<open>To show existence of lfp/gfp (a weak version of Knaster-Tarski theorem), we first observe that:\<close>
lemma mu_lfp: "partial_order R \<Longrightarrow> R-MONO f \<Longrightarrow> (R-\<mu> f) x \<Longrightarrow> (R-lfp f) x"
  unfolding fp_defs endorel_defs rel_defs func_defs comb_defs by metis
lemma nu_gfp: "partial_order R \<Longrightarrow> R-MONO f \<Longrightarrow> (R-\<nu> f) x \<Longrightarrow> (R-gfp f) x"
  unfolding fp_defs endorel_defs rel_defs func_defs comb_defs by metis
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


subsection \<open>For Sets and Relations\<close>

definition setMu :: "SetEOp('a) \<Rightarrow> Set('a)" ("\<mu>")
  where "\<mu> \<equiv> \<Inter> \<circ> (\<subseteq>)-preFP"
definition setNu :: "SetEOp('a) \<Rightarrow> Set('a)" ("\<nu>") 
  where "\<nu> \<equiv> \<Union> \<circ> (\<subseteq>)-postFP"
definition relMu :: "(Rel('a,'b) \<Rightarrow> Rel('a,'b)) \<Rightarrow> Rel('a,'b)" ("\<mu>\<^sup>r")
  where "\<mu>\<^sup>r \<equiv> \<Inter>\<^sup>r \<circ> (\<subseteq>\<^sup>r)-preFP"
definition relNu :: "(Rel('a,'b) \<Rightarrow> Rel('a,'b)) \<Rightarrow> Rel('a,'b)" ("\<nu>\<^sup>r")
  where "\<nu>\<^sup>r \<equiv> \<Union>\<^sup>r \<circ> (\<subseteq>\<^sup>r)-postFP"

declare setMu_def[fp_defs] setNu_def[fp_defs] 
        relMu_def[fp_defs] relNu_def[fp_defs]

text \<open>For illustration: the definitions unfold as follows:\<close>
lemma "\<mu> = (\<lambda>F x. \<forall>A. (F A \<subseteq> A) \<rightarrow> A x)" unfolding fp_defs func_defs comb_defs ..
lemma "\<nu> = (\<lambda>F x. \<exists>A. (F A \<supseteq> A) \<and> A x)" unfolding fp_defs func_defs comb_defs ..
lemma "\<mu> = (\<lambda>F x. \<forall>A. (\<forall>b. F A b \<rightarrow> A b) \<rightarrow> A x)" unfolding fp_defs func_defs comb_defs ..
lemma "\<nu> = (\<lambda>F x. \<exists>A. (\<forall>b. A b \<rightarrow> F A b) \<and> A x)" unfolding fp_defs func_defs comb_defs ..

text \<open>As a corollary, in the case of sets and relations, we have that:\<close>
lemma setMu_singleton: "singleton ((\<subseteq>)-\<mu> f)" using mu_singleton partial_order_def subset_limitComplete subset_partial_order by auto
lemma setNu_singleton: "singleton ((\<subseteq>)-\<nu> f)" using nu_singleton partial_order_def subset_limitComplete subset_partial_order by auto
lemma relMu_singleton: "singleton ((\<subseteq>\<^sup>r)-\<mu> R)" using mu_singleton partial_order_def subrel_limitComplete subrel_partial_order by auto
lemma relNu_singleton: "singleton ((\<subseteq>\<^sup>r)-\<nu> R)" using nu_singleton partial_order_def subrel_limitComplete subrel_partial_order by auto

text \<open>They are clearly (unique) instances of the general variants.\<close>
lemma setMu_simp: "\<iota> \<circ> (\<subseteq>)-\<mu> = \<mu> "
  using mu_unique partial_order_def subset_partial_order biginter_glb unfolding unique_def fp_defs comb_defs by blast
lemma setNu_simp: "\<iota> \<circ> (\<subseteq>)-\<nu> = \<nu>"
  using nu_unique partial_order_def subset_partial_order bigunion_lub unfolding unique_def fp_defs comb_defs by blast
lemma relMu_simp: "\<iota> \<circ> (\<subseteq>\<^sup>r)-\<mu> = \<mu>\<^sup>r"
  using mu_unique partial_order_def subrel_partial_order biginterR_glb unfolding unique_def fp_defs comb_defs by blast
lemma relNu_simp: "\<iota> \<circ> (\<subseteq>\<^sup>r)-\<nu> = \<nu>\<^sup>r"
  using nu_unique partial_order_def subrel_partial_order bigunionR_lub unfolding unique_def fp_defs comb_defs by blast

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

declare[[show_types=true]]

text \<open>Some useful theorems.\<close>
lemma bigdistr1: "(A \<inter> \<Union>S) = \<Union>\<lparr>(\<lambda>X. A \<inter> X) S\<rparr>" 
  unfolding func_defs comb_defs by fastforce
lemma bigdistr2: "(A \<union> \<Inter>S) = \<Inter>\<lparr>(\<lambda>X. A \<union> X) S\<rparr>" 
  unfolding func_defs comb_defs by fastforce

lemma compl_bigdeMorgan1: "\<midarrow>(\<Union>S) = \<Inter>\<lparr>\<midarrow> S\<rparr>" 
  unfolding func_defs comb_defs by fastforce
lemma compl_bigdeMorgan2: "\<midarrow>(\<Inter>S) = \<Union>\<lparr>\<midarrow> S\<rparr>" 
  unfolding func_defs comb_defs by fastforce

text \<open>Check notation\<close>
lemma "(\<nu> X. \<phi>) = \<nu>(\<lambda>X. \<phi>)" ..
lemma "(\<mu> X. \<phi>) = \<mu>(\<lambda>X. \<phi>)" ..

text \<open>Check theorems\<close>
lemma "\<mu> = \<midarrow> \<circ> \<nu> \<circ> dualop" oops (*TODO: prove*)  
lemma "(\<mu> X. \<phi> X) = \<midarrow>(\<nu> X. \<phi>\<^sup>d X)"  oops (*TODO: prove*)  

end