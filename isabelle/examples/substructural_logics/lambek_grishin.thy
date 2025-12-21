section \<open>Lambek-Grishin Calculus\<close>
text \<open>This is an example shallow encoding of an object-logical system using the library.\<close>

theory lambek_grishin
imports "../../operators" "../../entailment" "HOL-Eisbach.Eisbach"
begin

text \<open>We start by implementing a custom prover for this theory (called "them" for "theory-method").
Current implementation is very brute! It consists of mindless definition-unfolding followed by
 invocation of ground HOL-provers (extensionality is applied in between, if no success at first).
 A decent implementation shall unfold definitions gradually and call custom methods at each layer.\<close>
method skip = (tactic \<open>all_tac\<close>)
method them = (unfold endorel_defs rel_defs func_defs comb_defs) ;
            (auto | skip) ; (fastforce | skip) ; (metis | skip) ;
            ((rule ext)+ | skip) ; (auto | fastforce | metis | smt)


text \<open>In the 1970s, Richard Routley (later Sylvan) and Robert Meyer developed a semantics for relevance
 logics using ternary relations ("Routley-Meyer frames") instead of the binary accessibility relations
 familiar from modal logic​ ("Kripke frames"). These ternary frames were soon recognized as applicable
 not just to relevant logics, but to a whole family of substructural logics (those in which structural 
 rules like exchange, contraction, or weakening do not hold generally. 
 We use them to encode the "Lambek-Grishin calculus" following the presentation by \<^cite>\<open>Moortgat2014\<close>.\<close>

text \<open>The "Lambek calculus" was introduced by Joachim Lambek in 1958 designed for reasoning about how 
 sequences (e.g. words) form grammatical sentences. It is a substructural logic where contraction and 
 weakening are dropped, since their presence would entail that well-formedness is unaffected by 
 arbitrary copying or deletion of material. Exchange is also dropped to take into account word order.
 He first introduced an associative version, and later generalized it into a non-associative
 version \<^cite>\<open>Lambek1961\<close> where phrase structure becomes a binary tree.
 Grishin's 1983 work extended Lambek's framework by introducing a dual family of connectives forming 
 a "dual" counterpart to Lambek's original product (aka. fusion) connective and its residual divisions.\<close>

text \<open>The logical connectives of the Lambek-Grishin Calculus thus include two binary operations: 
 "fusion" (aka. "product") resp. "fission" (aka. "sum" or "coproduct") for modelling concatenation
 resp. splitting, each with its two residuals ("on the left" and "on the right").
 We encode them as syntactic sugar on top of "generalized image" operations (for ternary relations).\<close>

abbreviation(input) fusion::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('a) \<Rightarrow> Set('b) \<Rightarrow> Set('c)" ("\<^bold>\<otimes>")
  where "\<^bold>\<otimes> R \<equiv> \<diamond>\<^sub>1\<^sub>2\<^sub>3 R"
abbreviation(input) fission::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('a) \<Rightarrow> Set('b) \<Rightarrow> Set('c)" ("\<^bold>\<oplus>")
  where "\<^bold>\<oplus> R \<equiv> \<box>\<^sub>1\<^sub>2\<^sub>3 R"
abbreviation(input) rDivision::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('a) \<Rightarrow> Set('c) \<Rightarrow> Set('b)" ("\<^bold>\<triangleright>")
  where "\<^bold>\<triangleright> R \<equiv> \<midarrow> \<ggreater> \<box>\<^sub>1\<^sub>3\<^sub>2 R" (* often denoted with symbol "\" *)
abbreviation(input) lDivision::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('b) \<Rightarrow> Set('c) \<Rightarrow> Set('a)"  ("\<^bold>\<triangleleft>")
  where "\<^bold>\<triangleleft> R \<equiv> \<midarrow> \<ggreater> \<box>\<^sub>2\<^sub>3\<^sub>1 R" (* often denoted with symbol "/" *)
abbreviation(input) rDifference::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('a) \<Rightarrow> Set('c) \<Rightarrow> Set('b)" ("\<^bold>\<guillemotright>")
  where "\<^bold>\<guillemotright> R \<equiv> \<midarrow> \<ggreater> \<diamond>\<^sub>1\<^sub>3\<^sub>2 R" (* often denoted with symbol "reversed-\<oslash>" *)
abbreviation(input) lDifference::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('b) \<Rightarrow> Set('c) \<Rightarrow> Set('a)"  ("\<^bold>\<guillemotleft>")
  where "\<^bold>\<guillemotleft> R \<equiv> \<midarrow> \<ggreater> \<diamond>\<^sub>2\<^sub>3\<^sub>1 R" (* often denoted with symbol "\<oslash>" *)

text \<open>We add some convenient "parameterized infix" syntactic sugar.\<close>
syntax "lg_fusion"::"any \<Rightarrow> any \<Rightarrow> any \<Rightarrow> logic"  ("_ \<^bold>\<otimes>\<^sup>_ _")
syntax "lg_fission"::"any \<Rightarrow> any \<Rightarrow> any \<Rightarrow> logic" ("_ \<^bold>\<oplus>\<^sup>_ _")
syntax "lg_rImplication"::"any \<Rightarrow> any \<Rightarrow> any \<Rightarrow> logic" ("_ \<^bold>\<triangleright>\<^sup>_ _")
syntax "lg_lImplication"::"any \<Rightarrow> any \<Rightarrow> any \<Rightarrow> logic" ("_ \<^bold>\<triangleleft>\<^sup>_ _")
syntax "lg_rDifference"::"any \<Rightarrow> any \<Rightarrow> any \<Rightarrow> logic" ("_ \<^bold>\<guillemotright>\<^sup>_ _")
syntax "lg_lDifference"::"any \<Rightarrow> any \<Rightarrow> any \<Rightarrow> logic" ("_ \<^bold>\<guillemotleft>\<^sup>_ _")
translations "P \<^bold>\<otimes>\<^sup>R Q" == "CONST fusion  R P Q"
translations "P \<^bold>\<oplus>\<^sup>R Q" == "CONST fission R P Q"
translations "P \<^bold>\<triangleright>\<^sup>R Q"  == "CONST rDivision R P Q"
translations "P \<^bold>\<triangleleft>\<^sup>R Q"  == "CONST lDivision R Q P"
translations "P \<^bold>\<guillemotright>\<^sup>R Q" == "CONST rDifference R P Q"
translations "P \<^bold>\<guillemotleft>\<^sup>R Q"  == "CONST lDifference R Q P"

text \<open>We have, for instance:\<close>
lemma "(A \<^bold>\<otimes>\<^sup>R B) = \<diamond>\<^sub>1\<^sub>2\<^sub>3 R A B" unfolding rel_defs func_defs comb_defs by simp
lemma "(A \<^bold>\<oplus>\<^sup>R B) = \<box>\<^sub>1\<^sub>2\<^sub>3 R A B" unfolding rel_defs func_defs comb_defs by simp
lemma "(A \<^bold>\<triangleright>\<^sup>R B) = \<box>\<^sub>1\<^sub>3\<^sub>2 R (\<midarrow>A) B" unfolding rel_defs func_defs comb_defs by simp
lemma "(A \<^bold>\<guillemotright>\<^sup>R B) = \<diamond>\<^sub>1\<^sub>3\<^sub>2 R (\<midarrow>A) B" unfolding rel_defs func_defs comb_defs by simp

text \<open>As in modal logic, we control operator's behaviour by suitably restricting the underlying relation.
 This ternary relation stands for grammatical composition or "merge". 
 Read \<open>R x y z\<close> as "the expression z is obtained by putting together the subexpressions x and y".\<close>
abbreviation "TRANS R \<equiv> \<forall>x y z u. (\<exists>s. R x y s \<and> R s z u) \<leftrightarrow> (\<exists>t. R y z t \<and> R x t u)"
abbreviation "SYMM R \<equiv> \<forall>x y u. R x y u \<leftrightarrow> R y x u"
abbreviation "REFL R \<equiv> \<forall>x. R x x x"

text \<open>Switch between the associative and non-associative versions.\<close>
lemma "A \<^bold>\<otimes>\<^sup>R (B \<^bold>\<otimes>\<^sup>R C) = (A \<^bold>\<otimes>\<^sup>R B) \<^bold>\<otimes>\<^sup>R C" nitpick \<comment> \<open>countermodel found\<close> oops
lemma "A \<^bold>\<oplus>\<^sup>R (B \<^bold>\<oplus>\<^sup>R C) = (A \<^bold>\<oplus>\<^sup>R B) \<^bold>\<oplus>\<^sup>R C" nitpick \<comment> \<open>countermodel found\<close> oops
lemma fusion_assoc:  "TRANS R \<Longrightarrow> A \<^bold>\<otimes>\<^sup>R (B \<^bold>\<otimes>\<^sup>R C) = (A \<^bold>\<otimes>\<^sup>R B) \<^bold>\<otimes>\<^sup>R C" by them
lemma fission_assoc: "TRANS R \<Longrightarrow> A \<^bold>\<oplus>\<^sup>R (B \<^bold>\<oplus>\<^sup>R C) = (A \<^bold>\<oplus>\<^sup>R B) \<^bold>\<oplus>\<^sup>R C" by them

text \<open>Similarly, we can make the fusion resp. fission operators commutative. In fact, extending the 
 associative variant with commutativity gives us Linear Logic (without exponentials).\<close>
proposition "A \<^bold>\<otimes>\<^sup>R B = B \<^bold>\<otimes>\<^sup>R A" nitpick \<comment> \<open>countermodel found\<close> oops
proposition "A \<^bold>\<oplus>\<^sup>R B = B \<^bold>\<oplus>\<^sup>R A" nitpick \<comment> \<open>countermodel found\<close> oops
lemma fusion_comm:  "SYMM R \<Longrightarrow> A \<^bold>\<otimes>\<^sup>R B = B \<^bold>\<otimes>\<^sup>R A" by them
lemma fission_comm: "SYMM R \<Longrightarrow> A \<^bold>\<oplus>\<^sup>R B = B \<^bold>\<oplus>\<^sup>R A" by them

text \<open>Note that, in spite of the suggestive notation, the implications are not converse to each other
 in general. They are so only in the commutative variant.\<close>
proposition "(A \<^bold>\<triangleright>\<^sup>R B) = (B \<^bold>\<triangleleft>\<^sup>R A)" nitpick \<comment> \<open>countermodel found\<close> oops
proposition "(A \<^bold>\<guillemotright>\<^sup>R B) = (B \<^bold>\<guillemotleft>\<^sup>R A)" nitpick \<comment> \<open>countermodel found\<close> oops
lemma division_symm:   "SYMM R \<Longrightarrow> A \<^bold>\<triangleright>\<^sup>R B = B \<^bold>\<triangleleft>\<^sup>R A" by them
lemma difference_symm: "SYMM R \<Longrightarrow> A \<^bold>\<guillemotright>\<^sup>R B = B \<^bold>\<guillemotleft>\<^sup>R A" by them

text \<open>Analogously, assumming reflexivity for R recovers the following property (which gives us contraction).\<close>
lemma "A \<^bold>\<otimes>\<^sup>R A = A" nitpick \<comment> \<open>countermodel found\<close> oops
lemma "A \<^bold>\<oplus>\<^sup>R A = A" nitpick \<comment> \<open>countermodel found\<close> oops
lemma fusion_idem:  "REFL R \<Longrightarrow>      A \<subseteq> A \<^bold>\<otimes>\<^sup>R A" by them
lemma fission_idem: "REFL R \<Longrightarrow> A \<^bold>\<oplus>\<^sup>R A \<subseteq> A"      by them
text \<open>Note, however, that\<close>
proposition "TRANS R \<Longrightarrow>  SYMM R \<Longrightarrow> REFL R \<Longrightarrow> A \<^bold>\<otimes>\<^sup>R A \<subseteq> A" nitpick \<comment> \<open>countermodel found\<close> oops
proposition "TRANS R \<Longrightarrow>  SYMM R \<Longrightarrow> REFL R \<Longrightarrow> A \<subseteq> A \<^bold>\<oplus>\<^sup>R A" nitpick \<comment> \<open>countermodel found\<close> oops

text \<open>Degree-preserving (local) entailment is encoded by using the subset ordering.\<close>
abbreviation(input) lg_entail  ("[_\<turnstile>_]") where "[A \<turnstile> B] \<equiv> A \<subseteq> B"

text \<open>These (dual) implications are adjoint to the fusion (fission) connective, capturing the idea that 
 \<open>A \<triangleright> B\<close> behaves like an implication "if A on the left, then B", since \<open>A \<otimes> (A \<triangleright> B)\<close> entails \<open>B\<close>.
 Also, right residual \<open>B \<triangleleft> A\<close> behaves like "if A on the right, then B", since \<open>(B \<triangleleft> A) \<otimes> A\<close> entails \<open>B\<close>.
 Analogous, dual interrelations hold for fission and its residuals.\<close>

lemma "[A \<^bold>\<otimes>\<^sup>R B \<turnstile> C] = [B \<turnstile> A \<^bold>\<triangleright>\<^sup>R C]" by them
lemma "[A \<^bold>\<otimes>\<^sup>R B \<turnstile> C] = [A \<turnstile> C \<^bold>\<triangleleft>\<^sup>R B]" by them
lemma "[C \<turnstile> A \<^bold>\<oplus>\<^sup>R B] = [C \<^bold>\<guillemotleft>\<^sup>R B \<turnstile> A]" by them
lemma "[C \<turnstile> A \<^bold>\<oplus>\<^sup>R B] = [A \<^bold>\<guillemotright>\<^sup>R C \<turnstile> B]" by them

text \<open>We verify some principles of the (non-associative) Lambek-Grishin calculus below.\<close>

text \<open>Application\<close>
lemma "[(A \<^bold>\<triangleleft>\<^sup>R B) \<^bold>\<otimes>\<^sup>R B \<turnstile> A]" by them
lemma "[B \<^bold>\<otimes>\<^sup>R (B \<^bold>\<triangleright>\<^sup>R A) \<turnstile> A]" by them
lemma "[A \<turnstile> B \<^bold>\<oplus>\<^sup>R (B \<^bold>\<guillemotright>\<^sup>R A)]" by them
lemma "[A \<turnstile> (A \<^bold>\<guillemotleft>\<^sup>R B) \<^bold>\<oplus>\<^sup>R B]" by them

text \<open>Co-application\<close>
lemma "[A \<turnstile> (A \<^bold>\<otimes>\<^sup>R B) \<^bold>\<triangleleft>\<^sup>R B]" by them
lemma "[A \<turnstile> B \<^bold>\<triangleright>\<^sup>R (B \<^bold>\<otimes>\<^sup>R A)]" by them
lemma "[(A \<^bold>\<oplus>\<^sup>R B) \<^bold>\<guillemotleft>\<^sup>R B \<turnstile> A]" by them
lemma "[B \<^bold>\<guillemotright>\<^sup>R (B \<^bold>\<oplus>\<^sup>R A) \<turnstile> A]" by them

text \<open>Lifting\<close>
lemma "[A \<turnstile> B \<^bold>\<triangleleft>\<^sup>R (A \<^bold>\<triangleright>\<^sup>R B)]" by them
lemma "[A \<turnstile> (B \<^bold>\<triangleleft>\<^sup>R A) \<^bold>\<triangleright>\<^sup>R B]" by them
lemma "[B \<^bold>\<guillemotleft>\<^sup>R (A \<^bold>\<guillemotright>\<^sup>R B) \<turnstile> A]" by them
lemma "[(B \<^bold>\<guillemotleft>\<^sup>R A) \<^bold>\<guillemotright>\<^sup>R B \<turnstile> A]" by them

text \<open>Monotonicity\<close>
lemma "[A \<turnstile> B] \<and> [C \<turnstile> D] \<longrightarrow> [A \<^bold>\<otimes>\<^sup>R C \<turnstile> B \<^bold>\<otimes>\<^sup>R D]" by them
lemma "[A \<turnstile> B] \<and> [C \<turnstile> D] \<longrightarrow> [A \<^bold>\<triangleleft>\<^sup>R D \<turnstile> B \<^bold>\<triangleleft>\<^sup>R C]" by them
lemma "[A \<turnstile> B] \<and> [C \<turnstile> D] \<longrightarrow> [D \<^bold>\<triangleright>\<^sup>R A \<turnstile> C \<^bold>\<triangleright>\<^sup>R B]" by them
lemma "[A \<turnstile> B] \<and> [C \<turnstile> D] \<longrightarrow> [A \<^bold>\<oplus>\<^sup>R C \<turnstile> B \<^bold>\<oplus>\<^sup>R D]" by them
lemma "[A \<turnstile> B] \<and> [C \<turnstile> D] \<longrightarrow> [A \<^bold>\<guillemotleft>\<^sup>R D \<turnstile> B \<^bold>\<guillemotleft>\<^sup>R C]" by them
lemma "[A \<turnstile> B] \<and> [C \<turnstile> D] \<longrightarrow> [D \<^bold>\<guillemotright>\<^sup>R A \<turnstile> C \<^bold>\<guillemotright>\<^sup>R B]" by them

text \<open>We can use Nitpick to visualize counterexamples to weakening.\<close>
lemma "TRANS R \<Longrightarrow> SYMM R \<Longrightarrow> REFL R \<Longrightarrow> [A \<^bold>\<otimes>\<^sup>R B \<turnstile> A]" nitpick \<comment> \<open>countermodel found\<close> oops
lemma "TRANS R \<Longrightarrow> SYMM R \<Longrightarrow> REFL R \<Longrightarrow> [B \<^bold>\<otimes>\<^sup>R A \<turnstile> A]" nitpick \<comment> \<open>countermodel found\<close> oops
lemma "TRANS R \<Longrightarrow> SYMM R \<Longrightarrow> REFL R \<Longrightarrow> [A \<turnstile> A \<^bold>\<oplus>\<^sup>R B]" nitpick \<comment> \<open>countermodel found\<close> oops
lemma "TRANS R \<Longrightarrow> SYMM R \<Longrightarrow> REFL R \<Longrightarrow> [A \<turnstile> B \<^bold>\<oplus>\<^sup>R A]" nitpick \<comment> \<open>countermodel found\<close> oops

end