theory basic_temporal_logic
  imports "../../endorelations" "HOL-Eisbach.Eisbach"
begin

section \<open>Since and Until\<close> (*Beware: in construction*)

text \<open>We start by implementing a custom prover for this theory (called "them" for "theory-method").
Current implementation is very brute! It consists of mindless definition-unfolding followed by
 invocation of ground HOL-provers (extensionality is applied in between, if no success at first).
 A decent implementation shall unfold definitions gradually and call custom methods at each layer.\<close>
method skip = (tactic \<open>all_tac\<close>)
method them = (unfold endorel_defs rel_defs func_defs comb_defs) ;
            (auto | skip) ; (fastforce | skip) ; (metis | skip) ;
            ((rule ext)+ | skip) ; (auto | fastforce | metis | smt)

abbreviation(input) Until::"ERel('a) \<Rightarrow> SetEOp\<^sub>2('a)" ("\<U>\<^sup>_")
  where "\<U>\<^sup>R \<equiv> \<lambda>A B. \<lambda>a. \<exists>b. R\<^sup>+ a b \<and> B b \<and> interval R\<^sup>+ a b \<subseteq> A"

lemma transitiveClosure_char: "R\<^sup>+ = \<Inter>\<^sup>r(\<lambda>T. transitive T \<and> R \<subseteq>\<^sup>r T)" sorry (*TODO *)

lemma "\<U>\<^sup>R \<UU> = leftImage R" unfolding transitiveClosure_char nitpick oops (*TODO check*)

definition Untilw::"ERel('a) \<Rightarrow> SetEOp\<^sub>2('a)" ("\<W>\<^sup>_")
  where "\<W>\<^sup>R \<equiv> \<lambda>A B. \<lambda>a. \<exists>b. interval R a b \<subseteq> A"

lemma "\<U>\<^sup>R A B \<sqinter> \<U>\<^sup>R B A" nitpick oops
lemma "\<W>\<^sup>R A B \<sqinter> \<W>\<^sup>R B A" nitpick oops

(*
lemma "\<U>\<^sup>R = (\<lambda>A B. \<lambda>a. \<exists>(B \<inter> (\<lambda>x. interval R a x \<subseteq> A)))" unfolding inter_def comb_defs by simp
lemma "\<W>\<^sup>R = (\<lambda>A B. \<lambda>a. \<exists>(\<lambda>x. interval R a x \<subseteq> A))" unfolding Untilw_def comb_defs by simp
lemma "\<W>\<^sup>R = (\<lambda>A B. \<lambda>a. \<exists>x. interval R a x \<subseteq> A)" unfolding Untilw_def comb_defs by simp
lemma "\<W>\<^sup>R = (\<lambda>A B. \<lambda>a. \<exists>x. (\<supseteq>) A (interval R a x))" unfolding Untilw_def comb_defs by simp
lemma "\<W>\<^sup>R = (\<lambda>A B. \<lambda>a. (\<exists>x. (((\<supseteq>) A) \<circ> (interval R a)) x))" unfolding Untilw_def comb_defs by simp
lemma "\<W>\<^sup>R = (\<lambda>A B. \<lambda>a. \<exists>(((\<supseteq>) A) \<circ> (interval R a)))" unfolding Untilw_def comb_defs by simp
lemma "\<W>\<^sup>R = (\<lambda>A B. \<lambda>a. \<exists>(((\<supseteq>) A) \<circ> (interval R) a))" unfolding Untilw_def comb_defs by simp
lemma "\<W>\<^sup>R = (\<lambda>A B. \<lambda>a. \<^bold>B ((\<exists>(((\<supseteq>) A) \<circ> (interval R)) a)" unfolding Untilw_def comb_defs by simp
*)

(*TODO: Check properties from temporal logics textbook*)

end