theory "basic_quantifiers"
imports "../../endorelations"
begin




section \<open>Quantifiers\<close>

subsection \<open>Unrestricted Quantifiers\<close>

subsubsection \<open>Existential\<close>

notation rightRange ("\<^bold>\<exists>") and leftRange ("\<^bold>\<exists>''")
term "\<^bold>\<exists> :: Rel('a,'b) \<Rightarrow> Set('b)"
term "\<^bold>\<exists>':: Rel('a,'b) \<Rightarrow> Set('a)"
lemma "\<^bold>\<exists> \<rho> = (\<lambda>w. \<exists>x. \<rho> x w)"  unfolding rel_defs comb_defs ..
lemma "\<^bold>\<exists>'\<rho> = (\<lambda>x. \<exists>w. \<rho> x w)"  unfolding rel_defs comb_defs ..

lemma "\<^bold>\<exists> =  \<Union> \<circ> range" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<exists> \<rho> = \<Union>(range \<rho>)" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<exists>'\<rho> = \<Union>(range \<rho>\<^sup>\<smile>)" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<exists>' = \<Union> \<circ> (range \<circ> \<^bold>C)" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<exists>' = (\<Union> \<circ> range) \<circ> \<^bold>C" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<exists>' = \<^bold>\<exists> \<circ> \<^bold>C" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<exists>' = \<^bold>B\<exists>" unfolding rel_defs comb_defs ..

lemma "\<^bold>\<exists>\<rho> = \<^bold>\<exists>' \<rho>\<^sup>\<smile>" unfolding rel_defs comb_defs ..
lemma "\<^bold>\<exists> = \<^bold>\<exists>' \<circ> \<^bold>C" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<exists> = \<^bold>B\<exists> \<circ> \<^bold>C" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<exists> = \<^bold>B (\<^bold>B\<exists>) \<^bold>C" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<exists> = \<^bold>B\<^sub>2 \<exists> \<^bold>C" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<exists> = \<exists> \<circ>\<^sub>2 \<^bold>C" unfolding rel_defs func_defs comb_defs by metis

lemma "\<exists>\<^sup>2 =  \<^bold>\<exists>'\<^bold>\<exists>'" unfolding rel_defs comb_defs ..
lemma "\<exists>\<^sup>2 =  \<^bold>B\<exists>(\<^bold>B\<exists>)" unfolding comb_defs ..


subsubsection \<open>Universal\<close>

notation rightDualRange ("\<^bold>\<forall>") and leftDualRange ("\<^bold>\<forall>''")
term "\<^bold>\<forall> :: Rel('a,'b) \<Rightarrow> Set('b)"
term "\<^bold>\<forall>' :: Rel('a,'b) \<Rightarrow> Set('a)"
lemma "\<^bold>\<forall> \<rho> = (\<lambda>w. \<forall>x. \<rho> x w)"  unfolding rel_defs comb_defs ..
lemma "\<^bold>\<forall>'\<rho> = (\<lambda>x. \<forall>w. \<rho> x w)"  unfolding rel_defs comb_defs ..

lemma "\<^bold>\<forall> = \<Inter> \<circ> range" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<forall> \<rho> = \<Inter>(range \<rho>)" unfolding rel_defs comb_defs unfolding func_defs comb_defs by metis
lemma "\<^bold>\<forall>'\<rho> = \<Inter>(range \<rho>\<^sup>\<smile>)" unfolding rel_defs func_defs unfolding comb_defs by metis
lemma "\<^bold>\<forall>' = \<Inter> \<circ> (range \<circ> \<^bold>C)" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<forall>' = (\<Inter> \<circ> range) \<circ> \<^bold>C" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<forall>' = \<^bold>\<forall> \<circ> \<^bold>C" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<forall>' = \<^bold>B\<forall>" unfolding rel_defs comb_defs ..

lemma "\<^bold>\<forall>\<rho> = \<^bold>\<forall>' \<rho>\<^sup>\<smile>" unfolding rel_defs comb_defs ..
lemma "\<^bold>\<forall> = \<^bold>\<forall>' \<circ> \<^bold>C" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<forall> = \<^bold>B\<forall> \<circ> \<^bold>C" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<forall> = \<^bold>B (\<^bold>B\<forall>) \<^bold>C" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<forall> = \<^bold>B\<^sub>2 \<forall> \<^bold>C" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<forall> = \<forall> \<circ>\<^sub>2 \<^bold>C" unfolding rel_defs func_defs comb_defs by metis

lemma "\<forall>\<^sup>2 =  \<^bold>\<forall>' \<^bold>\<forall>'" unfolding rel_defs comb_defs ..
lemma "\<forall>\<^sup>2 =  \<^bold>B\<forall>(\<^bold>B\<forall>)" unfolding comb_defs ..


subsection \<open>Predicates and Properties as Relations\<close>

(*In intensional contexts, properties/predicates are encoded as relations *)
term "(P::'w\<Rightarrow>Set('e))::Rel('w,'e)" (* (intensional) property*)
term "(P::'e\<Rightarrow>Set('w))::Rel('e,'w)" (* (intensional) predicate*)

lemma "leftRange R = \<midarrow>(leftDualRange R\<^sup>\<midarrow>)" unfolding rel_defs func_defs comb_defs by simp
lemma "leftRange = \<midarrow> \<circ> leftDualRange \<circ> \<midarrow>\<^sup>r" unfolding rel_defs func_defs comb_defs by simp
lemma "rightRange = \<midarrow> \<circ> leftDualRange \<circ> \<sim>" unfolding rel_defs func_defs comb_defs by simp
lemma "rightDualRange = \<midarrow> \<circ> leftRange \<circ> \<sim>" unfolding rel_defs func_defs comb_defs by simp
lemma "rightDualRange = leftDualRange \<circ> \<^bold>C" unfolding rel_defs func_defs comb_defs by simp

lemma "\<exists>A = \<midarrow>\<forall>(\<midarrow>A)" unfolding func_defs comb_defs by simp
lemma "\<^bold>\<exists>A = \<midarrow>(\<^bold>\<forall>(\<midarrow>\<^sup>rA))" unfolding rel_defs func_defs comb_defs by simp
lemma "\<^bold>\<exists>'A = \<midarrow>(\<^bold>\<forall>'(\<midarrow>\<^sup>rA))" unfolding rel_defs func_defs comb_defs by simp


subsection \<open>Constant-domain restrictions\<close>

subsubsection \<open>Existential\<close>

(*Restricted constant-domain quantifiers *)
abbreviation(input) mexists_const::"Set('a) \<Rightarrow> Rel('a,'b) \<Rightarrow> Set('b)" ("\<^bold>\<exists>[_]_") 
  where "mexists_const \<equiv> \<^bold>C rightImage"
abbreviation(input) mexists_const'::"Set('b) \<Rightarrow> Rel('a,'b) \<Rightarrow> Set('a)" ("\<^bold>\<exists>''[_]_") 
  where "mexists_const' \<equiv> \<^bold>C leftImage"
abbreviation(input) mforall_const::"Set('a) \<Rightarrow> Rel('a,'b) \<Rightarrow> Set('b)" ("\<^bold>\<forall>[_]_") 
  where "mforall_const \<equiv> \<^bold>C rightBound"
abbreviation(input) mforall_const'::"Set('b) \<Rightarrow> Rel('a,'b) \<Rightarrow> Set('a)" ("\<^bold>\<forall>''[_]_") 
  where "mforall_const' \<equiv> \<^bold>C leftBound"

lemma "\<^bold>\<exists>[A]\<rho> = (\<lambda>b. \<exists>a. A a \<and> \<rho> a b)" unfolding rel_defs func_defs comb_defs by auto
lemma "\<^bold>\<exists>'[B]\<rho> = (\<lambda>a. \<exists>b. B b \<and> \<rho> a b)" unfolding rel_defs func_defs comb_defs by auto
lemma "\<^bold>\<forall>[A]\<rho> = (\<lambda>b. \<forall>a. A a \<rightarrow> \<rho> a b)" unfolding rel_defs func_defs comb_defs by auto
lemma "\<^bold>\<forall>'[B]\<rho> = (\<lambda>a. \<forall>b. B b \<rightarrow> \<rho> a b)" unfolding rel_defs func_defs comb_defs by auto

lemma "mexists_const D \<rho> = mexists_const' D \<rho>\<^sup>\<smile>" unfolding rel_defs comb_defs ..
lemma "mforall_const D \<rho> = mforall_const' D \<rho>\<^sup>\<smile>" unfolding rel_defs comb_defs ..

lemma "\<^bold>\<exists>[D]\<rho> = \<Union>\<lparr>\<rho> D\<rparr>" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<exists>'[D]\<rho> = \<Union>\<lparr>\<rho>\<^sup>\<smile> D\<rparr>" unfolding rel_defs func_defs comb_defs by metis

lemma "\<^bold>\<forall>[D]\<rho> = \<Inter>\<lparr>\<rho> D\<rparr>" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<forall>'[D]\<rho> = \<Inter>\<lparr>\<rho>\<^sup>\<smile> D\<rparr>" unfolding rel_defs func_defs comb_defs by metis

lemma "mexists_const = \<^bold>C rightImage" unfolding rel_defs func_defs comb_defs by auto
lemma "\<^bold>\<exists>[D]\<rho> = (\<Union> \<circ>\<^sub>2 image) \<rho> D" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<exists>'[D]\<rho> = (\<Union> \<circ>\<^sub>2 (image \<circ> \<^bold>C)) \<rho> D" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<exists>'[D]\<rho> = ((\<Union> \<circ>\<^sub>2 image) \<circ> \<^bold>C) \<rho> D" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<exists>'[D]\<rho> = (\<Union> \<circ>\<^sub>2 image) \<rho>\<^sup>\<smile> D" unfolding rel_defs func_defs comb_defs by metis
lemma "mexists_const' = \<^bold>C leftImage" unfolding rel_defs func_defs comb_defs by auto

lemma "mforall_const = \<^bold>C rightBound" unfolding rel_defs func_defs comb_defs by auto
lemma "\<^bold>\<forall>[D]\<rho> = (\<Inter> \<circ>\<^sub>2 image) \<rho> D" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<forall>'[D]\<rho> = (\<Inter> \<circ>\<^sub>2 (image \<circ> \<^bold>C)) \<rho> D" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<forall>'[D]\<rho> = (\<Inter> \<circ>\<^sub>2 image \<circ> \<^bold>C) \<rho> D" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<forall>'[D]\<rho> = ((\<Inter> \<circ>\<^sub>2 image) \<circ> \<^bold>C) \<rho> D" unfolding rel_defs func_defs comb_defs by metis
lemma "\<^bold>\<forall>'[D]\<rho> = (\<Inter> \<circ>\<^sub>2 image) \<rho>\<^sup>\<smile> D" unfolding rel_defs func_defs comb_defs by metis
lemma "mforall_const' = \<^bold>C leftBound" unfolding rel_defs func_defs comb_defs by auto

declare[[show_types=true]]
lemma "\<^bold>\<forall>(\<rho>\<circ>\<psi>) = \<^bold>\<forall>[range \<psi>] \<rho>" unfolding rel_defs func_defs comb_defs by auto
lemma "\<^bold>\<exists>(\<rho>\<circ>\<psi>) = \<^bold>\<exists>[range \<psi>] \<rho>" unfolding rel_defs func_defs comb_defs by auto

lemma "\<^bold>\<forall>'(\<rho>\<^sup>\<smile>\<circ>\<psi>)\<^sup>\<smile> = \<^bold>\<forall>'[range \<psi>] \<rho>" unfolding rel_defs func_defs comb_defs by auto
lemma "\<^bold>\<exists>'(\<rho>\<^sup>\<smile>\<circ>\<psi>)\<^sup>\<smile> = \<^bold>\<exists>'[range \<psi>] \<rho>" unfolding rel_defs func_defs comb_defs by auto

end