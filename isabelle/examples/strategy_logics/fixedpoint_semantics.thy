theory fixedpoint_semantics
  imports "../../operators" "../../operators"  "HOL-Eisbach.Eisbach"
begin

text \<open>We start by implementing a custom prover for this theory (called "them" for "theory-method").
Current implementation is very brute! It consists of mindless definition-unfolding followed by
 invocation of ground HOL-provers (extensionality is applied in between, if no success at first).
 A decent implementation shall unfold definitions gradually and call custom methods at each layer.\<close>
method skip = (tactic \<open>all_tac\<close>)
method them = (unfold endorel_defs rel_defs func_defs comb_defs) ;
            (auto | skip) ; (fastforce | skip) ; (metis | skip) ;
            ((rule ext)+ | skip) ; (auto | fastforce | metis | smt)

(*Hide from the Isabelle library to avoid collisions*)
hide_const(open) Inductive.lfp Inductive.gfp 

named_theorems fp_defs

definition leastFixedPoint :: "ERel('a) \<Rightarrow> EOp('a) \<Rightarrow> Set('a)" ("_-lfp")
  where "R-lfp \<equiv> R-least \<circ> FP"
definition greatestFixedPoint :: "ERel('a) \<Rightarrow> EOp('a) \<Rightarrow> Set('a)" ("_-gfp")
  where "R-gfp \<equiv> R-greatest \<circ> FP"

declare leastFixedPoint_def[fp_defs] greatestFixedPoint_def[fp_defs]

lemma "antisymmetric R \<Longrightarrow> unique (R-lfp f)" by (simp add: fp_defs B1_comb_def antisymm_least_unique)
lemma "antisymmetric R \<Longrightarrow> limitComplete R \<Longrightarrow> R-MONO f \<Longrightarrow> \<exists>(R-lfp f)" oops (*TODO*)

(*The \<mu> resp. \<nu> operators (aka. least- resp. greatest-fixedpoint; but not here)*)
definition mu :: "ERel('a) \<Rightarrow> EOp('a) \<Rightarrow> Set('a)" ("_-\<mu>")
  where "R-\<mu> \<equiv> R-glb \<circ> (R-preFP)"
definition nu :: "ERel('a) \<Rightarrow> EOp('a) \<Rightarrow> Set('a)" ("_-\<nu>") 
  where "R-\<nu> \<equiv> R-lub \<circ> (R-postFP)"

declare mu_def[fp_defs] nu_def[fp_defs]

lemma "partial_order R \<Longrightarrow> R-MONO f \<Longrightarrow> (R-lfp f) = (R-\<mu> f)" 
  unfolding fp_defs apply (rule ext)+ apply (rule iffI) oops (*TODO*)
lemma "partial_order R \<Longrightarrow> R-MONO f \<Longrightarrow> (R-gfp f) = (R-\<nu> f)"
  unfolding fp_defs apply (rule ext)+ apply (rule iffI) oops (*TODO*)

(*In the case of sets, we conveniently have that*)
lemma "unique ((\<subseteq>)-\<mu> f)"
  by (metis B1_comb_def \<Phi>21_comb_def antisymm_greatest_unique glb_def mu_def partial_order_def  subset_partial_order)
lemma "unique ((\<subseteq>)-\<nu> f)" 
  by (metis B1_comb_def \<Phi>21_comb_def antisymm_least_unique lub_def nu_def partial_order_def subset_partial_order)

(*...which the following convenient definition*)
definition setMu :: "SetEOp('a) \<Rightarrow> Set('a)" ("\<mu>")
  where "\<mu> \<equiv> \<Inter> \<circ> (\<subseteq>)-preFP"
definition setNu :: "SetEOp('a) \<Rightarrow> Set('a)" ("\<nu>") 
  where "\<nu> \<equiv> \<Union> \<circ> (\<subseteq>)-postFP"

declare setMu_def[fp_defs] setNu_def[fp_defs]

(*For illustration: the definitions unfold as follows*)
lemma "\<mu> = (\<lambda>F x. \<forall>A. (F A \<subseteq> A) \<rightarrow> A x)" unfolding fp_defs func_defs comb_defs ..
lemma "\<mu> = (\<lambda>F x. \<forall>A. (\<forall>b. F A b \<rightarrow> A b) \<rightarrow> A x)" unfolding fp_defs func_defs comb_defs ..

(*They are clearly instances of the general variant*)
lemma "((\<subseteq>)-\<mu> f) (\<mu> f)" by (simp add: B1_comb_def biginter_glb mu_def setMu_def)
lemma "((\<subseteq>)-\<nu> f) (\<nu> f)" by (simp add: B1_comb_def bigunion_lub nu_def setNu_def)

lemma "\<iota> \<circ> (\<subseteq>)-\<mu> = \<mu>" unfolding fp_defs func_defs comb_defs oops (*TODO*)
lemma "\<iota> \<circ> (\<subseteq>)-\<nu> = \<nu>" unfolding fp_defs func_defs comb_defs oops (*TODO*)

text \<open>Note however\<close>
lemma "(\<subseteq>)-\<mu> f = (\<subseteq>)-lfp f" nitpick \<comment> \<open>counterexample found\<close> oops
text \<open>We have in fact\<close>
lemma "(\<subseteq>)-MONO f \<Longrightarrow> (\<subseteq>)-\<mu> f = (\<subseteq>)-lfp f" 
  unfolding fp_defs func_defs comb_defs endorel_defs rel_defs 
  apply (rule ext)+ oops (*TODO*)

end

