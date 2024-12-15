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
notation(input) downImage ("\<^sup>_\<^bold>\<diamond>")
notation(input) downImageDual ("\<^sup>_\<^bold>\<box>")
notation(input) upImage ("\<^sup>_\<^bold>\<diamond>''")
notation(input) upImageDual ("\<^sup>_\<^bold>\<box>''")

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
 by cleverly exploiting the lemma 'ADT' and the 'XY_reldef' family of (definitional) lemmata.*)

lemma reflexive_corresp:  "reflexive R \<longleftrightarrow> (\<forall>P. \<lfloor>P \<^bold>\<rightarrow> \<^sup>R\<^bold>\<diamond>P\<rfloor>)" (*sledgehammer*)
  apply(subst ADT)
  apply(subst reflexive_def)
  apply(subst downImage_embedding)
  apply(subst downImage_hom_id)
  apply(subst subrel_def)
  apply(unfold comb_defs) 
  ..
  
lemma reflexive_corresp': "reflexive R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^sup>R\<^bold>\<box>P \<^bold>\<rightarrow> P\<rfloor>)" (*sledgehammer*)
  by (metis ADT C21_comb_def K11_comb_def downImageDual_embedding downImageDual_hom_id reflexive_def subrel_setdef)

lemma symmetric_corresp: "symmetric R \<longleftrightarrow> (\<forall>P. \<lfloor>P \<^bold>\<rightarrow> \<^sup>R\<^bold>\<box>(\<^sup>R\<^bold>\<diamond>P)\<rfloor>)" (*sledgehammer*)
  apply(subst ADT)
  apply(subst symmetric_reldef)
  apply(fold residuation1)
  apply(subst downImage_defT)
  apply(subst upImage_embedding)
  apply(subst subrel_setdef)
  ..

lemma symmetric_corresp': "symmetric R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^sup>R\<^bold>\<diamond>(\<^sup>R\<^bold>\<box>P) \<^bold>\<rightarrow> P\<rfloor>)" 
  apply(subst ADT)
  apply(subst symmetric_reldef)
  apply(unfold residuation2)
  apply(subst upImageDual_defT)
  apply(subst downImageDual_embedding)
  apply(unfold C21_comb_def)
  apply(subst subrel_setdef)
  oops (*TODO finish*)

lemma transitive_corresp:  "transitive R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^sup>R\<^bold>\<diamond>(\<^sup>R\<^bold>\<diamond>P) \<^bold>\<rightarrow> \<^sup>R\<^bold>\<diamond>P\<rfloor>)" (*sledgehammer*)
  apply(subst ADT)
  apply(subst transitive_def)
  apply(unfold comb_defs)
  apply(subst downImage_embedding)
  apply(subst downImage_hom_comp)
  apply(subst subrel_def)
  apply(unfold comb_defs)
  ..

lemma transitive_corresp': "transitive R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^sup>R\<^bold>\<box>P \<^bold>\<rightarrow> \<^sup>R\<^bold>\<box>(\<^sup>R\<^bold>\<box>P)\<rfloor>)" (*sledgehammer*)
  by (metis ADT B11_comb_def C21_comb_def downImageDual_embedding downImageDual_hom_comp subrel_setdef transitive_reldef)

lemma dense_corresp: "dense R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^sup>R\<^bold>\<box>(\<^sup>R\<^bold>\<box>P) \<^bold>\<rightarrow> \<^sup>R\<^bold>\<box>P\<rfloor>)" (*sledgehammer*)
  by (metis ADT B11_comb_def C21_comb_def dense_reldef downImageDual_embedding downImageDual_hom_comp subrel_setdef)
lemma dense_corresp': "dense R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^sup>R\<^bold>\<diamond>P \<^bold>\<rightarrow> \<^sup>R\<^bold>\<diamond>(\<^sup>R\<^bold>\<diamond>P)\<rfloor>)" (*sledgehammer*)
  by (metis ADT B11_comb_def dense_reldef downImage_embedding downImage_hom_comp subrel_setdef)

lemma euclidean_corresp: "euclidean R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^sup>R\<^bold>\<diamond>P \<^bold>\<rightarrow> \<^sup>R\<^bold>\<box>(\<^sup>R\<^bold>\<diamond>P)\<rfloor>)" (*sledgehammer*)
  by (metis (no_types, lifting) ADT B11_comb_def downImage_embedding downImage_hom_comp euclidean_reldef residuation1 subrel_setdef upImage_defT)
lemma euclidean_corresp': "euclidean R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^sup>R\<^bold>\<diamond>(\<^sup>R\<^bold>\<box>P) \<^bold>\<rightarrow> \<^sup>R\<^bold>\<box>P\<rfloor>)" (*sledgehammer*)
  by (metis (no_types, opaque_lifting) ADT B11_comb_def C21_comb_def downImageDual_embedding downImageDual_hom_comp euclidean_reldef residuation2 subrel_setdef upImageDual_defT)


end
