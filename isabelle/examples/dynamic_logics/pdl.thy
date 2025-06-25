theory pdl
  imports "../../induction" "../../operators" "../../entailment"
begin

section \<open>Shallow Embedding of Propositional Dynamic Logic (PDL)\<close>  (*Beware: work in progress!*)

(*Syntactic sugar for object-logical Boolean connectives*)
notation(input) compl ("\<^bold>\<not>") and inter (infixr "\<^bold>\<and>" 54) and union (infixr "\<^bold>\<or>" 53) and impl  (infixr "\<^bold>\<rightarrow>" 51)
notation(input) emptyset ("\<^bold>\<bottom>") and universe ("\<^bold>\<top>")

(*We now introduce our program-indexed family of modalities via the following definitions:*)
notation(input) leftImage ("<_>_")
notation(input) leftDualImage ("[_]_")

(*P holds in *at least one* state reachable (from the current state) by executing program/action 'a'*)
lemma "<a>P = (\<lambda>w. \<exists>v. a w v \<and> P v)" unfolding leftImage_def func_defs comb_defs ..
(*P holds in *every* state reachable (from the current state) by executing program/action 'a'*)
lemma "[a]P = (\<lambda>w. \<forall>v. a w v \<rightarrow> P v)" unfolding leftDualImage_def func_defs comb_defs ..

(*Diamond (resp. Box) is monotonic (resp. antimonotonic) wrt. relation ordering*)
lemma "a \<subseteq>\<^sup>r b \<longrightarrow> <a>P \<subseteq> <b>P" 
  by (metis leftImage_embedding subrel_setdef)
lemma "a \<subseteq>\<^sup>r b \<longrightarrow> [b]P \<subseteq> [a]P"
  apply(subst leftDualImage_embedding)
  apply(unfold subrel_setdef)
  by simp


subsection \<open>Operations\<close>

(*We explore the (algebraic) operations on actions/programs. 
  For instance actions/programs can be combined via a sequential or choice execution.*)

(*Sequential execution 'a' followed by 'b'*)
abbreviation(input) seq_composition (infixr "\<^bold>;" 75) (*note boldface*)
  where "a \<^bold>; b \<equiv> a ;\<^sup>r b"

lemma "[a\<^bold>;b]P = [a][b]P" (*sledgehammer*)
  by (simp add: B1_comb_def leftDualImage_hom_comp)
lemma "<a\<^bold>;b>P = <a><b>P"
  by (simp add: B1_comb_def leftImage_hom_comp)

(*Choice: execute a or b (non-deterministically)*)
abbreviation(input) choice (infixr "+" 75)
  where "a + b \<equiv> a \<union>\<^sup>r b"

(*P holds in every state reachable via execution of the action/program 'a+b' if and only if P holds 
 in every state reachable via execution of 'a' *and* also in every state reachable via execution of 'b'*)
lemma "[a+b]P = ([a]P) \<^bold>\<and> ([b]P)"
  unfolding leftDualImage_hom_join interR_def inter_def comb_defs ..

(*P holds in at least one state reachable via execution of the action/program 'a+b' if and only if P holds
 in at least one state reachable via execution of 'a' *or*  in at least one state reachable via execution of 'b'*)
lemma "<a+b>P = (<a>P) \<^bold>\<or> (<b>P)"
  unfolding leftImage_def leftImage_hom_join rel_defs func_defs comb_defs by auto

(*Non-deterministic choice for arbitrary sets: execute any action/program among those in S*)
abbreviation(input) gen_choice ("\<Sigma>")
  where "\<Sigma> S \<equiv> \<Union>\<^sup>rS" 

lemma "[\<Sigma> S]P = \<Inter>\<lparr>(\<lambda>x. [x]P) S\<rparr>"
  unfolding rel_defs func_defs comb_defs by fastforce
lemma "<\<Sigma> S>P = \<Union>\<lparr>(\<lambda>x. <x>P) S\<rparr>" 
  unfolding rel_defs func_defs comb_defs by fastforce

(*Iterated execution ("Kleene star") corresponds to the (reflexive-)transitive closure of the 
 denotation of the program/action. It models "repeat an undetermined number of times". *)
term "(\<lambda>a. a\<^sup>+) :: ERel('a) \<Rightarrow> ERel('a)"
term "(\<lambda>a. a\<^sup>*) :: ERel('a) \<Rightarrow> ERel('a)"

lemma tran_closure_refl: "reflexive R \<longrightarrow> reflexive (R\<^sup>+)"
  unfolding reflexive_def2  biginterR_def2 ind_defs func_defs comb_defs rel_defs by blast

lemma tran_closure_symm: "symmetric R \<longrightarrow> symmetric (R\<^sup>+)" sorry (*kernel reconstruction fails*)
  (* unfolding symmetric_def transitiveClosure_char transitive_reldef *)

lemma tran_closure_trans: "transitive (R\<^sup>+)" sorry (*kernel reconstruction fails*)
  (* by (smt (verit, del_insts) biginterR_def2 transitiveClosure_char transitive_def2) *)

lemma tran_closure_equiv: "equivalence R \<longrightarrow> equivalence (R\<^sup>+)"
  by (simp add: equivalence_char tran_closure_refl tran_closure_symm tran_closure_trans)

lemma bigunionR_symm: "G \<subseteq> symmetric \<longrightarrow> symmetric (\<Union>\<^sup>rG)"
  unfolding symmetric_reldef bigunionR_def2 unfolding rel_defs func_defs comb_defs by metis
lemma bigunionR_refl: "\<exists>G \<longrightarrow> G \<subseteq> reflexive \<longrightarrow> reflexive (\<Union>\<^sup>rG)"
  unfolding reflexive_def2 bigunionR_def2 func_defs rel_defs comb_defs by auto

end
