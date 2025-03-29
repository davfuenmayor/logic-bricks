theory dynamic_logic
  imports "../../operators" "../../entailment"
begin

section \<open>Shallow Embedding of Propositional Dynamic Logic (PDL)\<close>

typedecl w (*type of worlds or states*)
type_synonym \<sigma> = "Set(w)" (*type of propositions or predicates*)
type_synonym \<pi> = "ERel(w)" (*type of actions or programs*)

(*Syntactic sugar for object-logical Boolean connectives*)
notation(input) compl ("\<^bold>\<not>") and inter (infixr "\<^bold>\<and>" 54) and union (infixr "\<^bold>\<or>" 53) and impl  (infixr "\<^bold>\<rightarrow>" 51)

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
abbreviation(input) seq_composition::"\<pi> \<Rightarrow> \<pi> \<Rightarrow> \<pi>" (infixr "\<^bold>;" 75) (*note boldface*)
  where "a \<^bold>; b \<equiv> b \<circ>\<^sup>r a"

lemma "[a\<^bold>;b]P = [a][b]P" (*sledgehammer*)
  by (simp add: B1_comb_def leftDualImage_hom_comp)
lemma "<a\<^bold>;b>P = <a><b>P"
  by (simp add: B1_comb_def leftImage_hom_comp)

(*Choice: execute a or b (non-deterministically)*)
abbreviation(input) choice::"\<pi> \<Rightarrow> \<pi> \<Rightarrow> \<pi>" (infixr "+" 75)
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
abbreviation(input) gen_choice::"Set(\<pi>) \<Rightarrow> \<pi>" ("\<Sigma>")
  where "\<Sigma> S \<equiv> \<Union>\<^sup>rS" 

lemma "[\<Sigma> S]P = \<Inter>\<lparr>(\<lambda>x. [x]P) S\<rparr>"
  unfolding rel_defs func_defs comb_defs by fastforce
lemma "<\<Sigma> S>P = \<Union>\<lparr>(\<lambda>x. <x>P) S\<rparr>" 
  unfolding rel_defs func_defs comb_defs by fastforce

(*Iterated execution ("Kleene star") corresponds to the (reflexive-)transitive closure of the 
 denotation of the program/action. It models "repeat an undetermined number of times". *)
term "(\<lambda>a. a\<^sup>+) :: \<pi> \<Rightarrow> \<pi>"
term "(\<lambda>a. a\<^sup>*) :: \<pi> \<Rightarrow> \<pi>"

lemma tran_closure_refl: "reflexive R \<longrightarrow> reflexive (R\<^sup>+)"
  unfolding reflexive_def2  biginterR_def2 endorel_defs func_defs comb_defs rel_defs by blast

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
