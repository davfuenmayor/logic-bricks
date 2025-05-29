section \<open>Shallow Embedding of a Logic for Program Verification\<close>

theory program_logic
  imports pdl "HOL-Eisbach.Eisbach"
begin

section \<open>Regular Programs\<close> (*Beware: work in progress!*)

text \<open>We start by implementing a custom prover for this theory (called "them" for "theory-method").
Current implementation is very brute! It consists of mindless definition-unfolding followed by
 invocation of ground HOL-provers (extensionality is applied in between, if no success at first).
 A decent implementation shall unfold definitions gradually and call custom methods at each layer.\<close>
method skip = (tactic \<open>all_tac\<close>)
method them = (unfold endorel_defs rel_defs func_defs comb_defs) ;
            (auto | skip) ; (fastforce | skip) ; (metis | skip) ;
            ((rule ext)+ | skip) ; (auto | fastforce | metis | smt)

abbreviation(input) test_expr ("_\<^bold>?") 
  where "P\<^bold>? \<equiv> test P"

abbreviation(input) skip_expr ("skip") 
  where "skip \<equiv> \<^bold>\<top>\<^bold>?"

lemma skip_simp: "skip = \<Q>" by them
lemma condtest_simp: "[P\<^bold>? \<^bold>; a]Q = P \<Rightarrow> [a]Q" by them

abbreviation(input) i_expr ("IF _ THEN _ ELSE") (*use uppercase to distinguish from HOL's "if-then-else"*)
  where "IF P THEN a ELSE b \<equiv> (P\<^bold>? \<^bold>; a) + (\<^bold>\<not>P\<^bold>? \<^bold>; b)"

abbreviation(input) while_expr ("WHILE _ DO _")
  where "WHILE P DO a \<equiv> (P\<^bold>? \<^bold>; a)\<^sup>* \<^bold>; \<^bold>\<not>P\<^bold>?"

abbreviation(input) hoare_expr ("{_} _ {_}")
  where "{P} a {Q} \<equiv> P \<subseteq> [a]Q"

(* Composition rule *)
lemma "{P} a {Q} \<and> {Q} b {S} 
      \<Longrightarrow> {P} a\<^bold>;b {S}" by them

(* Weakening rule *)
lemma "P' \<subseteq> P \<and> {P} a {Q} \<and> Q \<subseteq> Q'
      \<Longrightarrow> {P'} a {Q'}" by them

(* Conditional rule *)
lemma "{P \<^bold>\<and> Q} a {S} \<and> {\<^bold>\<not>P \<^bold>\<and> Q} b {S} 
      \<Longrightarrow> {Q} IF P THEN a ELSE b {S}" by them

(* While rule *)
lemma       "{P \<^bold>\<and> Q} a {Q} 
  \<longrightarrow> {Q} WHILE P DO a {\<^bold>\<not>P \<^bold>\<and> Q}" unfolding condtest_simp  oops (*TODO*)

end