section \<open>Shallow Embedding of an Epistemic Dynamic Logic\<close>

theory epistemic_logic
  imports pdl
begin



(* \<Sigma>\<^sup>+ G is the accessibility relation corresponding to the common knowledge of a group G of agents*)
definition commonAccessRel::"Set(\<pi>) \<Rightarrow> \<pi>" ("\<Sigma>\<^sup>+")
  where "\<Sigma>\<^sup>+ G \<equiv> (\<Union>\<^sup>rG)\<^sup>+"

lemma commonAccessRel_equiv: "\<exists>G \<Longrightarrow> (\<forall>r. G r \<longrightarrow> equivalence r) \<Longrightarrow> equivalence (\<Sigma>\<^sup>+ G)"
  unfolding equivalence_char commonAccessRel_def
  using tran_closure_refl tran_closure_symm tran_closure_trans bigunionR_refl bigunionR_symm
  unfolding func_defs comb_defs by metis

(*We can translate the previous to talk of agents and knowledge:*)
(*\<^bold>K(A) P stands for "Individual A knows that P"*)
abbreviation(input) Knows ("\<^bold>K{_}_") 
  where "\<^bold>K{A} P \<equiv> [A] P"

(*\<^bold>K\<^sup>E(G) stands for "Everyone in group G knows that P"*)
abbreviation(input) Eknows ("\<^bold>K\<^sup>E{_}_") 
  where "\<^bold>K\<^sup>E{G} P \<equiv> [\<Sigma> G] P"

(*\<^bold>K\<^sup>C(G) stands for "It is common knowledge in group G that P"*)
definition Cknows ("\<^bold>K\<^sup>C{_}_") 
  where "\<^bold>K\<^sup>C{G} P \<equiv> [\<Sigma>\<^sup>+ G]P"

(*Exercise: encode the "wise-muddy children" puzzle using the constructions above*)
consts muddy :: "\<pi>\<Rightarrow>\<sigma>" (* "is muddy" predicate*) 
consts children :: "\<pi>\<Rightarrow>bool" (* "is child" predicate, i.e. set of "children" *)
consts a::"\<pi>" b::"\<pi>" c::"\<pi>" (*three individual constants *)

axiomatization where 
   A0: "children a \<and> children b \<and> children c" and
   A1: "\<forall>x. children x \<longrightarrow> equivalence x" and
   (*Common knowledge: at least one of the children is muddy*)
   A2: "\<Turnstile> \<^bold>K\<^sup>C{children} (muddy a \<^bold>\<or> muddy b \<^bold>\<or> muddy c)" and
   (*Common knowledge: if x is (not) muddy then y can see this (and hence know this).*)
   A3: "children x \<and> children y \<and> x \<noteq> y \<Longrightarrow> \<Turnstile> \<^bold>K\<^sup>C{children} (muddy x \<^bold>\<rightarrow> \<^bold>K{y} (muddy x))" and 
   A4: "children x \<and> children y \<and> x \<noteq> y \<Longrightarrow> \<Turnstile> \<^bold>K\<^sup>C{children} (\<^bold>\<not>(muddy x) \<^bold>\<rightarrow> \<^bold>K{y} \<^bold>\<not>(muddy x))" and 
   (*Common knowledge: neither 'a' nor 'b' knows whether he is muddy.*)
   A5: "\<Turnstile> \<^bold>K\<^sup>C{children} (\<^bold>\<not>(\<^bold>K{a} (muddy a)) \<^bold>\<and> \<^bold>\<not>(\<^bold>K{b} (muddy b)))"

(* "Cut-lemma" required as stepping stone for automated provers*)
lemma commonAccessRelChildren_refl: "reflexive (\<Sigma>\<^sup>+ children)"
  using A0 A1 commonAccessRel_equiv equivalence_char by blast

theorem "\<Turnstile> \<^bold>K{c} (muddy c)" (*c knows he is muddy.*)
  using A0 A1 A2 A3 A4 A5
  using commonAccessRelChildren_refl reflexive_def2
  unfolding valid_def Cknows_def
  unfolding rel_defs func_defs
  unfolding comb_defs
  by metis

end
