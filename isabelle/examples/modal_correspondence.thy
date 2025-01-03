theory modal_correspondence
imports "../endorels_mini"
begin

section \<open>Automating modal correspondences\<close>

(*We can say of two unary operators \<phi> and \<psi> that they form a 'residuated' pair.
 We then say that \<phi> (\<psi>) is the left (right) 'residual' of \<psi> (\<phi>).*)
abbreviation(input) residuation_rule ("RESIDr _ _")
  where "RESIDr \<phi> \<psi> \<equiv> (\<And>A B. (\<phi> A \<subseteq> B) = (A \<subseteq> \<psi> B))"

(*Boolean logical connectives*)
notation(input) compl ("\<^bold>\<not>")
notation(input) inter (infixr "\<^bold>\<and>" 54) 
notation(input) union (infixr "\<^bold>\<or>" 53) 
notation(input) impl  (infixr "\<^bold>\<rightarrow>" 51)
(*Modal operators*)
notation(input) leftImage ("\<^sup>_\<^bold>\<diamond>")
notation(input) leftDualImage ("\<^sup>_\<^bold>\<box>")
notation(input) rightImage ("\<^sup>_\<^bold>\<diamond>''")
notation(input) rightDualImage ("\<^sup>_\<^bold>\<box>''")

(*Definition of modal validity: truth in all worlds*)
definition valid ("\<lfloor>_\<rfloor>")
  where "\<lfloor>F\<rfloor> \<equiv> \<forall>w. F w"

(*The following lemma is an algebraic-variant of the Deduction Theorem for modal logics.*)
lemma ADT: "\<lfloor>A \<^bold>\<rightarrow> B\<rfloor> = (A \<subseteq> B)"
  unfolding valid_def set_defs comb_defs ..

(*Two well-known residuation conditions on unary set-operations*)
lemma residuation1: "RESIDr \<^sup>R\<^bold>\<diamond>' \<^sup>R\<^bold>\<box>"
  unfolding rel_defs
  unfolding comb_defs
  unfolding set_defs
  unfolding comb_defs
  by auto
lemma residuation2: "RESIDr \<^sup>R\<^bold>\<diamond> \<^sup>R\<^bold>\<box>'"
  unfolding rel_defs
  unfolding comb_defs
  unfolding set_defs
  unfolding comb_defs
  by auto

(*Let us now prove automatically several well-known modal correspondences. 
 Observe how ATPs (via sledgehammer) manage to find the right definitions in the background theory,
 by cleverly exploiting the lemma 'ADT' and the algebraic properties of the relational set-operations.*)

lemma reflexive_corresp:  "reflexive R \<longleftrightarrow> (\<forall>P. \<lfloor>P \<^bold>\<rightarrow> \<^sup>R\<^bold>\<diamond>P\<rfloor>)" (*sledgehammer*)
  apply(subst ADT)
  apply(subst reflexive_def)
  apply(subst leftImage_embedding)
  apply(subst leftImage_hom_id)
  apply(subst subrel_setdef)
  apply(unfold comb_defs)
  ..
  
lemma reflexive_corresp': "reflexive R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^sup>R\<^bold>\<box>P \<^bold>\<rightarrow> P\<rfloor>)"
  by (metis ADT K11_comb_def leftDualImage_embedding leftDualImage_hom_id reflexive_def subrel_setdef)

lemma symmetric_corresp: "symmetric R \<longleftrightarrow> (\<forall>P. \<lfloor>P \<^bold>\<rightarrow> \<^sup>R\<^bold>\<box>(\<^sup>R\<^bold>\<diamond>P)\<rfloor>)" (*sledgehammer*)
  apply(subst ADT)
  apply(subst symmetric_reldef)
  apply(fold residuation1)
  apply(subst leftImage_defT)
  apply(subst rightImage_embedding)
  apply(subst subrel_setdef)
  ..

lemma symmetric_corresp': "symmetric R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^sup>R\<^bold>\<diamond>(\<^sup>R\<^bold>\<box>P) \<^bold>\<rightarrow> P\<rfloor>)"
  apply(subst ADT)
  apply(subst symmetric_reldef)
  apply(unfold residuation2)
  apply(subst rightDualImage_embedding)
  apply(subst leftDualImage_defT)
  apply(subst subrel_setdef)
  ..

lemma transitive_corresp:  "transitive R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^sup>R\<^bold>\<diamond>(\<^sup>R\<^bold>\<diamond>P) \<^bold>\<rightarrow> \<^sup>R\<^bold>\<diamond>P\<rfloor>)" (*sledgehammer*)
  apply(subst ADT)
  apply(subst transitive_def)
  apply(unfold comb_defs)
  apply(subst leftImage_embedding)
  apply(subst leftImage_hom_comp)
  apply(subst subrel_setdef)
  apply(unfold comb_defs)
  ..

lemma transitive_corresp': "transitive R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^sup>R\<^bold>\<box>P \<^bold>\<rightarrow> \<^sup>R\<^bold>\<box>(\<^sup>R\<^bold>\<box>P)\<rfloor>)" (*sledgehammer*)
  by (metis ADT B11_comb_def leftDualImage_embedding leftDualImage_hom_comp subrel_setdef transitive_reldef)

lemma dense_corresp: "dense R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^sup>R\<^bold>\<box>(\<^sup>R\<^bold>\<box>P) \<^bold>\<rightarrow> \<^sup>R\<^bold>\<box>P\<rfloor>)" (*sledgehammer*)
  by (metis ADT B11_comb_def dense_reldef leftDualImage_embedding leftDualImage_hom_comp subrel_setdef)
lemma dense_corresp': "dense R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^sup>R\<^bold>\<diamond>P \<^bold>\<rightarrow> \<^sup>R\<^bold>\<diamond>(\<^sup>R\<^bold>\<diamond>P)\<rfloor>)" (*sledgehammer*)
  by (metis ADT B11_comb_def dense_reldef leftImage_embedding leftImage_hom_comp subrel_setdef)

lemma euclidean_corresp: "euclidean R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^sup>R\<^bold>\<diamond>P \<^bold>\<rightarrow> \<^sup>R\<^bold>\<box>(\<^sup>R\<^bold>\<diamond>P)\<rfloor>)" (*sledgehammer*)
  by (metis (no_types, lifting) ADT B11_comb_def euclidean_reldef leftImage_embedding leftImage_hom_comp residuation1 rightImage_defT subrel_setdef)
lemma euclidean_corresp': "euclidean R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^sup>R\<^bold>\<diamond>(\<^sup>R\<^bold>\<box>P) \<^bold>\<rightarrow> \<^sup>R\<^bold>\<box>P\<rfloor>)" (*sledgehammer*)
  by (metis (no_types, lifting) ADT B11_comb_def euclidean_reldef leftDualImage_embedding leftDualImage_hom_comp residuation2 rightDualImage_defT subrel_setdef)


end
