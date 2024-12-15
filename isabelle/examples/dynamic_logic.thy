theory dynamic_logic
  imports modal_correspondence
begin

section \<open>Shallow embedding\<close>

typedecl w (*type of worlds or states*)
type_synonym \<sigma> = "Set(w)" (*type of propositions or predicates*)
type_synonym \<pi> = "ERel(w)" (*type of actions or programs*)

(*We now introduce our program-indexed family of modalities via the following definitions:*)
notation(input) downImageDual ("[_]_")
notation(input) downImage ("<_>_")

(*P holds in *at least one* state reachable (from the currest state) by executing program/action 'a'*)
lemma "<a>P = (\<lambda>w. \<exists>v. a w v \<and> P v)" unfolding downImage_def set_defs comb_defs ..
(*P holds in *every* state reachable (from the currest state) by executing program/action 'a'*)
lemma "[a]P = (\<lambda>w. \<forall>v. a w v \<rightarrow> P v)" unfolding downImageDual_def set_defs comb_defs ..

(*Diamond (resp. Box) is monotonic (resp. antimonotonic) wrt. relation ordering*)
lemma "a \<subseteq>\<^sup>r b \<longrightarrow> <a>P \<subseteq> <b>P"
  by (metis downImage_embedding subrel_setdef)
lemma "a \<subseteq>\<^sup>r b \<longrightarrow> [b]P \<subseteq> [a]P"
  apply(subst downImageDual_embedding)
  apply(unfold C21_comb_def)
  apply(unfold subrel_setdef)
  by simp


section \<open>Operations\<close>

(*We explore the (algebraic) operations on actions/programs. 
  For instance actions/programs can be combined via a sequential or choice execution.*)

(*Sequential execution 'a' followed by 'b'*)
abbreviation(input) seq_composition::"\<pi> \<Rightarrow> \<pi> \<Rightarrow> \<pi>" (infixr "\<^bold>;" 75) (*note boldface*)
  where "a \<^bold>; b \<equiv> b \<circ>\<^sup>r a"

lemma "[a\<^bold>;b]P = [a][b]P" (*sledgehammer*)
  by (simp add: B11_comb_def downImageDual_hom_comp)
lemma "<a\<^bold>;b>P = <a><b>P"
  by (simp add: B11_comb_def downImage_hom_comp)

(*Choice: execute a or b (non-deterministically)*)
abbreviation(input) choice::"\<pi> \<Rightarrow> \<pi> \<Rightarrow> \<pi>" (infixr "+" 75)
  where "a + b \<equiv> a \<union>\<^sup>r b"

(*P holds in every state reachable via execution of the action/program 'a+b' if and only if P holds 
 in every state reachable via execution of 'a' *and* also in every state reachable via execution of 'b'*)
lemma "[a+b]P = ([a]P) \<^bold>\<and> ([b]P)"
  by (simp add: \<Phi>21_comb_def downImageDual_hom_join interR_def)

(*P holds in at least one state reachable via execution of the action/program 'a+b' if and only if P holds
 in at least one state reachable via execution of 'a' *or*  in at least one state reachable via execution of 'b'*)
lemma "<a+b>P = (<a>P) \<^bold>\<or> (<b>P)"
  by (metis \<Phi>21_comb_def downImage_hom_join unionR_def)

(*Non-deterministic choice for arbitrary sets: execute any action/program among those in S*)
abbreviation(input) gen_choice::"Set(\<pi>) \<Rightarrow> \<pi>" ("\<Sigma>")
  where "\<Sigma> S \<equiv> \<Union>\<^sup>rS" 

lemma "[\<Sigma> S]P = \<Inter>\<lparr>(\<lambda>x. [x]P) S\<rparr>"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce
lemma "<\<Sigma> S>P = \<Union>\<lparr>(\<lambda>x. <x>P) S\<rparr>" 
  unfolding rel_defs set_defs func_defs comb_defs by fastforce

(*(Reflexive-)transitive closure: "repeat 'a' an undetermined number of times"*)
definition tran_closure::"\<pi> \<Rightarrow> \<pi>" ("(_\<^sup>+)" 99) (*make point-free*)
  where "a\<^sup>+ \<equiv>  \<Inter>\<^sup>r(\<lambda>R. transitive R \<and> a \<subseteq>\<^sup>r R)"
abbreviation(input) refl_tran_closure::"\<pi> \<Rightarrow> \<pi>" ("(_\<^sup>* )" [1000] 999)
  where "a\<^sup>* \<equiv> a\<^sup>+ + \<Q>"

(*Obtaining a point-free representation of transitive-closure*)
lemma "a\<^sup>+ =  \<Inter>\<^sup>r(\<lambda>R. transitive R \<and> a \<subseteq>\<^sup>r R)" unfolding tran_closure_def comb_defs by auto
lemma "tran_closure a =  \<Inter>\<^sup>r (transitive \<inter> (\<subseteq>\<^sup>r) a)" unfolding tran_closure_def set_defs comb_defs by auto
lemma "tran_closure a =  \<Inter>\<^sup>r ((\<inter>) transitive ((\<subseteq>\<^sup>r) a))" unfolding tran_closure_def set_defs comb_defs by auto
lemma "tran_closure a =  \<Inter>\<^sup>r (\<^bold>D (\<inter>) transitive (\<subseteq>\<^sup>r) a)" unfolding tran_closure_def set_defs comb_defs by auto
lemma "tran_closure a =  (\<Inter>\<^sup>r \<circ> (\<^bold>D (\<inter>) transitive (\<subseteq>\<^sup>r))) a" unfolding tran_closure_def set_defs comb_defs by auto
lemma "tran_closure = \<Inter>\<^sup>r \<circ> (\<^bold>D (\<inter>) transitive (\<subseteq>\<^sup>r))" unfolding tran_closure_def set_defs comb_defs by auto

(*Some properties of the transitive and reflexive-transitive closure: *)
lemma "a\<^sup>+ = (a\<^sup>* \<^bold>; a)"
  unfolding tran_closure_def unfolding transitive_corresp valid_def oops (*TODO: prove*)

lemma "transitive a \<longrightarrow> P \<^bold>\<and> [a]P \<subseteq> [a\<^sup>+]P"
  unfolding tran_closure_def
  unfolding transitive_corresp valid_def
  unfolding rel_defs set_defs func_defs comb_defs by blast


lemma tran_closure_refl: "reflexive R \<longrightarrow> reflexive (R\<^sup>+)"
  unfolding reflexive_def2 tran_closure_def biginterR_def2 comb_defs by (simp add: B12_comb_def \<Phi>21_comb_def impl_def subrel_def subset_def)

lemma tran_closure_symm: "symmetric R \<longrightarrow> symmetric (R\<^sup>+)"
  unfolding symmetric_def tran_closure_def transitive_reldef rel_defs set_defs func_defs comb_defs 
  sorry (*kernel reconstruction fails*)

lemma tran_closure_trans: "transitive (R\<^sup>+)"
  by (smt (verit, del_insts) biginterR_def2 tran_closure_def transitive_def2)

lemma tran_closure_equiv: "equivalence R \<longrightarrow> equivalence (R\<^sup>+)"
  by (simp add: equivalence_char tran_closure_refl tran_closure_symm tran_closure_trans)

lemma bigunionR_symm: "G \<subseteq> symmetric \<longrightarrow> symmetric (\<Union>\<^sup>rG)"
  unfolding symmetric_reldef bigunionR_def2 unfolding rel_defs set_defs comb_defs by metis
lemma bigunionR_refl: "\<exists>G \<longrightarrow> G \<subseteq> reflexive \<longrightarrow> reflexive (\<Union>\<^sup>rG)"
  unfolding reflexive_def2 bigunionR_def2 set_defs comb_defs by auto

(* \<Sigma>\<^sup>+ G is the accessibility relation corresponding to the common knowledge of a group G of agents*)
definition commonAccessRel::"Set(\<pi>) \<Rightarrow> \<pi>" ("\<Sigma>\<^sup>+")
  where "\<Sigma>\<^sup>+ G \<equiv> (\<Union>\<^sup>rG)\<^sup>+"

lemma commonAccessRel_equiv: "\<exists>G \<Longrightarrow> (\<forall>r. G r \<longrightarrow> equivalence r) \<Longrightarrow> equivalence (\<Sigma>\<^sup>+ G)"
  by (simp add: comb_defs bigunionR_refl bigunionR_symm commonAccessRel_def equivalence_char impl_def subset_def tran_closure_refl tran_closure_symm tran_closure_trans)

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
   A2: "\<lfloor>\<^bold>K\<^sup>C{children} (muddy a \<^bold>\<or> muddy b \<^bold>\<or> muddy c)\<rfloor>" and
   (*Common knowledge: if x is (not) muddy then y can see this (and hence know this).*)
   A3: "children x \<and> children y \<and> x \<noteq> y \<Longrightarrow> \<lfloor>\<^bold>K\<^sup>C{children} (muddy x \<^bold>\<rightarrow> \<^bold>K{y} (muddy x))\<rfloor>" and 
   A4: "children x \<and> children y \<and> x \<noteq> y \<Longrightarrow> \<lfloor>\<^bold>K\<^sup>C{children} (\<^bold>\<not>(muddy x) \<^bold>\<rightarrow> \<^bold>K{y} \<^bold>\<not>(muddy x))\<rfloor>" and 
   (*Common knowledge: neither 'a' nor 'b' knows whether he is muddy.*)
   A5: "\<lfloor>\<^bold>K\<^sup>C{children} (\<^bold>\<not>(\<^bold>K{a} (muddy a)) \<^bold>\<and> \<^bold>\<not>(\<^bold>K{b} (muddy b)))\<rfloor>"

(* "Cut-lemma" required as stepping stone for automated provers*)
lemma commonAccessRelChildren_refl: "reflexive (\<Sigma>\<^sup>+ children)"
  using A0 A1 commonAccessRel_equiv equivalence_char by blast

theorem "\<lfloor>\<^bold>K{c} (muddy c)\<rfloor>" (*c knows he is muddy.*)
  using A0 A1 A2 A3 A4 A5
  using commonAccessRelChildren_refl reflexive_def
  unfolding valid_def Cknows_def
  unfolding rel_defs set_defs
  unfolding comb_defs
  by metis

end
