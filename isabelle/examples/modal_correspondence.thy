theory modal_correspondence
imports "../operators" "../entailment"
begin

section \<open>Automating Modal Correspondences\<close>

(*Syntactic sugar for object-logical Boolean connectives*)
notation(input) compl ("\<^bold>\<not>") and inter (infixr "\<^bold>\<and>" 54) and union (infixr "\<^bold>\<or>" 53) and impl  (infixr "\<^bold>\<rightarrow>" 51)

(*Beware technicalities: we need to paraphrase residuation and embedding as metalogical equations 
 (using Isabelle/Pure quantifiers) in order for rewriting to work as expected (TODO: fix) *)
abbreviation(input) residuation ("RESID _ _")
  where "RESID \<phi> \<psi> \<equiv> (\<And>A B. (\<phi> A \<subseteq> B) = (A \<subseteq> \<psi> B))" (* \<phi> (\<psi>) is the left (right) 'residual' of \<psi> (\<phi>)*)
abbreviation(input) relEmbedding ("_,_-embedding_")
  where "R,T-embedding \<phi> \<equiv> (\<And>X Y. R X Y = T (\<phi> X) (\<phi> Y))"


subsection \<open>Traditional Operators (\<box> & \<diamond>)\<close>

notation(input) leftImage ("\<^sup>_\<^bold>\<diamond>") and leftDualImage ("\<^sup>_\<^bold>\<box>") and 
                rightImage ("\<^sup>_\<^bold>\<diamond>''") and rightDualImage ("\<^sup>_\<^bold>\<box>''")

(*Two well-known residuation conditions on modal operators (qua endorelation-based set-operations)*)
lemma residuation1: "RESID \<^sup>R\<^bold>\<diamond>' \<^sup>R\<^bold>\<box>"
  by (metis adjunction_def2 rightImage_residuation)
lemma residuation2: "RESID \<^sup>R\<^bold>\<diamond> \<^sup>R\<^bold>\<box>'"
  by (simp add: leftImage_defT residuation1 rightDualImage_defT)

(*Let's now prove several well-known modal correspondences. Observe how ATPs, via sledgehammer, 
 manage to find the right definitions in the background theory, by cleverly exploiting the deduction
 meta-theorem (DMT) as well as the algebraic properties of the relation-based set-operations.*)

lemma reflexive_corresp:  "reflexive R \<longleftrightarrow> (\<forall>P. \<Turnstile> P \<^bold>\<rightarrow> \<^sup>R\<^bold>\<diamond>P)" (*sledgehammer*)
  apply(subst DMT)
  apply(subst reflexive_def)
  apply(subst leftImage_embedding)
  apply(subst leftImage_hom_id)
  apply(subst subrel_setdef)
  apply(subst I_comb_def) ..
  
lemma reflexive_corresp': "reflexive R \<longleftrightarrow> (\<forall>P. \<Turnstile> \<^sup>R\<^bold>\<box>P \<^bold>\<rightarrow> P)"  (*sledgehammer*)
  apply(subst DMT)
  apply(subst reflexive_def)
  apply(subst leftDualImage_embedding)
  apply(subst leftDualImage_hom_id)
  apply(subst subrel_setdef)
  apply(subst I_comb_def) ..

lemma symmetric_corresp: "symmetric R \<longleftrightarrow> (\<forall>P. \<Turnstile> P \<^bold>\<rightarrow> \<^sup>R\<^bold>\<box>(\<^sup>R\<^bold>\<diamond>P))"  (*sledgehammer*)
  apply(subst DMT)
  apply(subst symmetric_reldef)
  apply(fold residuation1)
  apply(subst leftImage_defT)
  apply(subst rightImage_embedding)
  apply(subst subrel_setdef) ..

lemma symmetric_corresp': "symmetric R \<longleftrightarrow> (\<forall>P. \<Turnstile> \<^sup>R\<^bold>\<diamond>(\<^sup>R\<^bold>\<box>P) \<^bold>\<rightarrow> P)" (*sledgehammer*)
  apply(subst DMT)
  apply(subst symmetric_reldef)
  apply(unfold residuation2)
  apply(subst rightDualImage_embedding)
  apply(subst leftDualImage_defT)
  apply(subst subrel_setdef) ..

lemma transitive_corresp:  "transitive R \<longleftrightarrow> (\<forall>P. \<Turnstile> \<^sup>R\<^bold>\<diamond>(\<^sup>R\<^bold>\<diamond>P) \<^bold>\<rightarrow> \<^sup>R\<^bold>\<diamond>P)" (*sledgehammer*)
  apply(subst DMT)
  apply(subst transitive_reldef)
  apply(subst leftImage_embedding)
  apply(subst leftImage_hom_comp)
  apply(subst subrel_setdef)
  apply(subst B1_comb_def) ..

lemma transitive_corresp': "transitive R \<longleftrightarrow> (\<forall>P. \<Turnstile> \<^sup>R\<^bold>\<box>P \<^bold>\<rightarrow> \<^sup>R\<^bold>\<box>(\<^sup>R\<^bold>\<box>P))" (*sledgehammer*)
  by (metis DMT B1_comb_def leftDualImage_embedding leftDualImage_hom_comp subrel_setdef transitive_reldef)

lemma dense_corresp: "dense R \<longleftrightarrow> (\<forall>P. \<Turnstile> \<^sup>R\<^bold>\<box>(\<^sup>R\<^bold>\<box>P) \<^bold>\<rightarrow> \<^sup>R\<^bold>\<box>P)" (*sledgehammer*)
  by (metis DMT B1_comb_def dense_reldef leftDualImage_embedding leftDualImage_hom_comp subrel_setdef)
lemma dense_corresp': "dense R \<longleftrightarrow> (\<forall>P. \<Turnstile> \<^sup>R\<^bold>\<diamond>P \<^bold>\<rightarrow> \<^sup>R\<^bold>\<diamond>(\<^sup>R\<^bold>\<diamond>P))" (*sledgehammer*)
  by (metis DMT B1_comb_def dense_reldef leftImage_embedding leftImage_hom_comp subrel_setdef)

lemma euclidean_corresp: "rightEuclidean R \<longleftrightarrow> (\<forall>P. \<Turnstile> \<^sup>R\<^bold>\<diamond>P \<^bold>\<rightarrow> \<^sup>R\<^bold>\<box>(\<^sup>R\<^bold>\<diamond>P))" (*sledgehammer*)
  by (metis (no_types, lifting) DMT B1_comb_def rightEuclidean_reldef leftImage_embedding leftImage_hom_comp residuation1 rightImage_defT subrel_setdef)
lemma euclidean_corresp': "rightEuclidean R \<longleftrightarrow> (\<forall>P. \<Turnstile> \<^sup>R\<^bold>\<diamond>(\<^sup>R\<^bold>\<box>P) \<^bold>\<rightarrow> \<^sup>R\<^bold>\<box>P)" (*sledgehammer*)
  by (metis (no_types, lifting) DMT B1_comb_def rightEuclidean_reldef leftDualImage_embedding leftDualImage_hom_comp residuation2 rightDualImage_defT subrel_setdef)

(*...and so on*)


subsection \<open>Further Operators\<close>

notation(input) leftBound ("\<^sup>_\<^bold>\<Zdres>") and leftDualBound ("\<^sup>_\<^bold>\<Zndres>") and
                rightBound ("\<^sup>_\<^bold>\<Zrres>") and rightDualBound ("\<^sup>_\<^bold>\<Znrres>")

lemma irreflexive_corresp:  "irreflexive R \<longleftrightarrow> (\<forall>P. \<Turnstile> \<^sup>R\<^bold>\<Zdres>P \<^bold>\<rightarrow> \<^bold>\<not>P)" (*sledgehammer*)
  apply(subst DMT)
  apply(subst irreflexive_def)
  apply(subst leftBound_embedding)
  apply(subst leftBound_hom_id)
  apply(subst subrel_setdef) ..

lemma transitive_compl_corresp:  "transitive (R\<^sup>\<midarrow>) \<longleftrightarrow> (\<forall>P. \<Turnstile> (\<^sup>R\<^bold>\<Zdres>P \<^bold>\<rightarrow> \<^sup>R\<^bold>\<Zdres>(\<^bold>\<not>(\<^sup>R\<^bold>\<Zdres>P))))"
  unfolding transitive_compl_reldef (*sledgehammer*)
  apply(subst DMT)
  apply(subst leftBound_embedding)
  apply(subst leftBound_hom_comp)
  apply(subst subrel_setdef)
  apply(subst compDual_def) ..

(*...and so on*)

end
