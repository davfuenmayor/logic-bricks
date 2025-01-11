theory sets (*  A basic theory of sets  *)
  imports logic_base
begin

section \<open>Sets\<close>

named_theorems set_defs  (*container for set-related definitions*)
named_theorems set_simps  (*container for set-related simplification rules*)

subsection \<open>Algebraic structure\<close>

(*We introduce below some operations on sets which endow them with a Boolean algebra structure.*)
definition univ::"Set('a)" ("\<UU>")
  where "\<UU> \<equiv> \<^bold>K True" (* the universal set *)
definition empty::"Set('a)" ("\<emptyset>")
  where "\<emptyset> \<equiv> \<^bold>K False" (* the empty set *)
definition compl::"EOp(Set('a))" ("\<midarrow>")
  where \<open>\<midarrow> \<equiv> \<^bold>B(\<not>)\<close> (* set complement *)
definition inter::"EOp\<^sub>2(Set('a))" (infixr "\<inter>" 54) 
  where "(\<inter>) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1(\<and>)" (* set intersection *)
definition union::"EOp\<^sub>2(Set('a))" (infixr "\<union>" 53) 
  where "(\<union>) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1(\<or>)" (* set union *)
definition diff::"EOp\<^sub>2(Set('a))" (infixl "\<setminus>" 51) 
  where "(\<setminus>) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1(\<leftharpoondown>)" (* set difference *)
definition impl::"EOp\<^sub>2(Set('a))" (infixr "\<Rightarrow>" 51) 
  where "(\<Rightarrow>) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1(\<rightarrow>)" (* set implication *)
definition dimpl::"EOp\<^sub>2(Set('a))" (infix "\<Leftrightarrow>" 51) 
  where "(\<Leftrightarrow>) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1(\<leftrightarrow>)" (* set double-implication *)
definition sdiff::"EOp\<^sub>2(Set('a))" (infix "\<triangle>" 51) 
  where "(\<triangle>) \<equiv>  \<^bold>\<Phi>\<^sub>2\<^sub>1(\<rightleftharpoons>)" (* set symmetric-difference (aka. xor) *)

abbreviation(input) lpmi::"EOp\<^sub>2(Set('a))" (infixl "\<Leftarrow>" 51) (*for convenience*)
  where "A \<Leftarrow> B \<equiv> B \<Rightarrow> A"

(*Let's put set-related definitions in the "set_defs" bag *)
declare univ_def[set_defs] empty_def[set_defs] 
        compl_def[set_defs] inter_def[set_defs] union_def[set_defs]
        impl_def[set_defs] dimpl_def[set_defs] diff_def[set_defs] sdiff_def[set_defs] 

(*Point-based definitions*)
lemma "\<UU> = (\<lambda>x. True)" unfolding set_defs comb_defs ..
lemma "\<emptyset> = (\<lambda>x. False)" unfolding set_defs comb_defs ..
lemma "\<midarrow>A = (\<lambda>x. \<not>A x)" unfolding set_defs comb_defs ..
lemma "A \<inter> B = (\<lambda>x. A x \<and> B x)" unfolding set_defs comb_defs ..
lemma "A \<union> B = (\<lambda>x. A x \<or> B x)" unfolding set_defs comb_defs ..
lemma "A \<setminus> B = (\<lambda>x. A x \<leftharpoondown> B x)" unfolding set_defs comb_defs ..
lemma "A \<Rightarrow> B = (\<lambda>x. A x \<rightarrow> B x)" unfolding set_defs comb_defs ..
lemma "A \<Leftarrow> B = (\<lambda>x. A x \<leftarrow> B x)" unfolding set_defs comb_defs ..
lemma "A \<Leftrightarrow> B = (\<lambda>x. A x \<leftrightarrow> B x)" unfolding set_defs comb_defs ..
lemma "A \<triangle> B = (\<lambda>x. A x \<rightleftharpoons> B x)" unfolding set_defs comb_defs ..

(*Union and intersection can be generalized to operate on arbitrary sets of sets (aka. 'infinitary' operations)*)
definition biginter::"EOp\<^sub>G(Set('a))" ("\<Inter>")
  where "\<Inter> \<equiv> \<forall> \<circ>\<^sub>2 (\<^bold>B\<^sub>2\<^sub>1\<^sub>1 (\<Rightarrow>) \<^bold>I \<^bold>T)"
definition bigunion::"EOp\<^sub>G(Set('a))" ("\<Union>")
  where "\<Union> \<equiv> \<exists> \<circ>\<^sub>2 (\<^bold>B\<^sub>2\<^sub>1\<^sub>1 (\<inter>) \<^bold>I \<^bold>T)"

lemma "\<Inter>S x = (\<forall>A. S A \<rightarrow> A x)" unfolding biginter_def set_defs comb_defs ..
lemma "\<Union>S x = (\<exists>A. S A \<and> A x)" unfolding bigunion_def set_defs comb_defs ..

declare biginter_def[set_defs] bigunion_def[set_defs]


subsubsection \<open>Ordering (subset/superset), overlapping and covering\<close>

(*The algebra of sets is ordered by the standard subset (endo)relation, as defined below.*)
definition subset::"ERel(Set('a))" (infixr "\<subseteq>" 51) 
  where "(\<subseteq>) \<equiv> \<forall> \<circ>\<^sub>2 (\<Rightarrow>)"

declare subset_def[set_defs] 

lemma "A \<subseteq> B = \<forall>(A \<Rightarrow> B)" unfolding set_defs comb_defs ..
lemma "A \<subseteq> B = (\<forall>x. A x \<rightarrow> B x)" unfolding set_defs comb_defs ..

(*Subset is antisymmetric, as expected*)
lemma subset_antisymm: "R \<subseteq> T \<Longrightarrow> T \<subseteq> R \<Longrightarrow> R = T" unfolding set_defs comb_defs by auto


(*Let us add the following convenient abbreviations for the reversed versions of (proper) subset*)
abbreviation(input) superset::"ERel(Set('a))" (infixr "\<supseteq>" 51)
  where "A \<supseteq> B \<equiv> B \<subseteq> A" 

(* The powerset operation corresponds to the (partial) application of superset *)
notation superset ("\<wp>")
lemma "\<wp>A = (\<lambda>B. B \<subseteq> A)" unfolding comb_defs ..

(*Two sets are said to 'overlap' (or 'intersect') if their intersection is non-empty*)
definition overlap::"ERel(Set('a))" (infix "\<sqinter>" 52)
  where "(\<sqinter>) \<equiv> \<exists> \<circ>\<^sub>2 (\<inter>)"
(*dually, two sets form a 'cover' if every element belongs to one or the other *)
definition cover::"ERel(Set('a))" (infix "\<squnion>" 53)
  where "(\<squnion>) \<equiv> \<forall> \<circ>\<^sub>2 (\<union>)"
(*Two sets are said to be 'incompatible' if their intersection is empty*)
definition incompat::"ERel(Set('a))" (infix "\<bottom>" 52)
  where "(\<bottom>) \<equiv> \<nexists> \<circ>\<^sub>2 (\<inter>)"

declare incompat_def[set_defs] overlap_def[set_defs] cover_def[set_defs] 

lemma "A \<sqinter> B = \<exists>(A \<inter> B)" unfolding set_defs comb_defs ..
lemma "A \<squnion> B = \<forall>(A \<union> B)" unfolding set_defs comb_defs ..
lemma "A \<bottom> B = \<nexists>(A \<inter> B)" unfolding set_defs comb_defs ..

definition psubset::"ERel(Set('a))" (infixr "\<subset>" 51) (*proper subset*)
  where "(\<subset>) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>2 (\<leftharpoondown>) (\<subseteq>) (\<supseteq>)"

declare psubset_def[set_defs]

lemma "A \<subset> B = (A \<subseteq> B \<leftharpoondown> (B \<subseteq> A))" unfolding set_defs comb_defs ..
lemma "A \<subset> B = (A \<subseteq> B \<and> (B \<sqinter> (\<midarrow>A)))" unfolding set_defs comb_defs by simp

abbreviation(input) psuperset::"ERel(Set('a))" (infixr "\<supset>" 51) (*proper superset*)
  where "A \<supset> B \<equiv> B \<subset> A" 

(*We say of a set of sets that it 'overlaps' (or 'intersects') if there exists a 'shared' element.*)
abbreviation(input) bigoverlap::"Set(Set(Set('a)))" ("\<Sqinter>")
  where "\<Sqinter> \<equiv> \<exists> \<circ> \<Inter>"
(*dually, a set of sets forms a 'cover' if every element is contained in at least one of the sets.*)
abbreviation(input) bigcover::"Set(Set(Set('a)))" ("\<Squnion>")
  where "\<Squnion> \<equiv> \<forall> \<circ> \<Union>"

lemma "\<Sqinter>S = \<exists>(\<Inter>S)" unfolding set_defs comb_defs ..
lemma "\<Squnion>S = \<forall>(\<Union>S)" unfolding set_defs comb_defs ..

(*The following provide convenient simplification rules*)
lemma All_simp1:"(\<subseteq>) \<UU> = \<forall>" 
  unfolding set_defs unfolding comb_defs by simp
lemma Ex_simp1: "(\<supseteq>) \<emptyset> = \<nexists>" 
  unfolding set_defs unfolding comb_defs by simp

declare All_simp1[set_simps] Ex_simp1[set_simps] 

(*Subset, overlap and cover are interrelated as expected*)
lemma "A \<subseteq> B = \<midarrow>A \<squnion> B" unfolding set_defs comb_defs by simp
lemma "A \<subseteq> B = A \<bottom> \<midarrow>B" unfolding set_defs comb_defs by simp
lemma "\<not>(A \<subseteq> B) = A \<sqinter> \<midarrow>B" unfolding set_defs comb_defs by simp
lemma "\<not>(A \<subseteq> B) = A \<sqinter> \<midarrow>B" unfolding set_defs comb_defs by simp
lemma "A \<supseteq> B = A \<squnion> \<midarrow>B" unfolding set_defs comb_defs by auto
lemma "A \<supseteq> B = \<midarrow>A \<bottom> B" unfolding set_defs comb_defs by auto
lemma "\<not>(A \<supseteq> B) = \<midarrow>A \<sqinter> B" unfolding set_defs comb_defs by auto
lemma "\<not>(A \<supseteq> B) = \<midarrow>A \<sqinter> B" unfolding set_defs comb_defs by auto
lemma "A \<squnion> B = \<midarrow>A \<subseteq> B" unfolding set_defs comb_defs by auto
lemma "A \<bottom> B = A \<subseteq> \<midarrow>B" unfolding set_defs comb_defs by simp
lemma "A \<sqinter> B = (\<not>(A \<subseteq> \<midarrow>B))" unfolding set_defs comb_defs by simp


subsection \<open>Constructing sets\<close>

subsubsection \<open>Singletons, cosingletons and finitely-generated sets\<close>

abbreviation(input) insert :: "'a \<Rightarrow> Set('a) \<Rightarrow> Set('a)"
  where "insert a S \<equiv> \<Q> a \<union> S"
abbreviation(input) remove :: "'a \<Rightarrow> Set('a) \<Rightarrow> Set('a)"
  where "remove a S \<equiv> \<D> a \<inter> S"

(*The previous functions in terms of combinators*)
lemma "insert = (\<^bold>B\<^sub>2\<^sub>1\<^sub>0 (\<union>) \<Q>)\<Zcat>" unfolding comb_defs ..
lemma "remove = (\<^bold>B\<^sub>2\<^sub>1\<^sub>0 (\<inter>) \<D>)\<Zcat>" unfolding comb_defs ..

syntax
  "_finiteSet" :: "args \<Rightarrow> Set('a)"   ("{(_)}")
  "_finiteCoset" :: "args \<Rightarrow> Set('a)" ("\<lbrace>(_)\<rbrace>")
translations
  "{x, xs}" \<rightleftharpoons> "CONST insert x (_finiteSet xs)"
  "\<lbrace>x, xs\<rbrace>" \<rightleftharpoons> "CONST remove x (_finiteCoset xs)"
  "{x}" \<rightharpoonup> "\<Q> x"  (*aka. 'singleton' *)
  "\<lbrace>x\<rbrace>" \<rightharpoonup> "\<D> x"  (*aka. 'cosingleton' *)

(*Checks*)
lemma "{a} = \<Q> a" ..
lemma "{a,b} = {a} \<union> {b}" ..
lemma "{a,b,c} = {a} \<union> {b,c}" ..
lemma "{a,b,c} = {a} \<union> {b} \<union> {c}" ..
lemma "\<lbrace>a\<rbrace> = \<D> a" ..
lemma "\<lbrace>a,b\<rbrace> = \<lbrace>a\<rbrace> \<inter> \<lbrace>b\<rbrace>" ..
lemma "\<lbrace>a,b,c\<rbrace> = \<lbrace>a\<rbrace> \<inter> \<lbrace>b,c\<rbrace>" ..
lemma "\<lbrace>a,b,c\<rbrace> = \<lbrace>a\<rbrace> \<inter> \<lbrace>b\<rbrace> \<inter> \<lbrace>c\<rbrace>" ..
lemma "\<lbrace>{a,b,c}, {d,e}\<rbrace> = \<lbrace>{a} \<union> {b} \<union> {c}\<rbrace> \<inter> \<lbrace>{d} \<union> {e}\<rbrace>" ..

(*Sets and cosets are related via set-complement as expected*)
lemma "\<lbrace>a\<rbrace> = \<midarrow>{a}" 
  unfolding set_defs comb_defs ..
lemma "\<lbrace>a,b\<rbrace> = \<midarrow>{a,b}" 
  unfolding set_defs comb_defs by simp
lemma "\<lbrace>a,b,c\<rbrace> = \<midarrow>{a,b,c}" 
  unfolding set_defs comb_defs by simp


subsubsection \<open>Basic spaces\<close>

(*We refer to sets of sets as "spaces". In fact, quantifiers are particular kinds of spaces.*)

term "\<forall>::Set(Set('a))" (* \<forall>A means that the set A contains all alements*)
term "\<exists>::Set(Set('a))" (* \<exists>A means that A contains at least one element, i.e. A is nonempty*)
term "\<nexists>::Set(Set('a))" (* \<nexists>A means that A does not contain any element, i.e. A is empty*)

(*Thus we introduce the following convenient lemmas (useful as simplification rules)*)
lemma All_simp2:"{\<UU>} = \<forall>" (* \<forall> is the space that contains only the universe*)
  unfolding set_defs comb_defs by auto
lemma Ex_simp2: "\<lbrace>\<emptyset>\<rbrace> = \<exists>" (* \<exists> is the space that contains all but the empty set*)
  unfolding Ex_def set_defs comb_defs by auto 
lemma Ex_simp3: "{\<emptyset>} = \<nexists>" (* \<nexists> is the space that contains only the empty set*)
  unfolding Ex_def set_defs comb_defs by auto 

declare All_simp2[set_simps] Ex_simp2[set_simps]

(*Further convenient instances of spaces (their combinator-based definitions are postponed)*)
definition unique::"Set(Set('a))" ("\<exists>\<^sub>\<le>\<^sub>1") (*\<exists>\<^sub>\<le>\<^sub>1 contains the sets with at most one element (and which may be empty)*)
  where \<open>\<exists>\<^sub>\<le>\<^sub>1A \<equiv> \<forall>x y. A x \<and> A y \<rightarrow> x = y\<close> 
definition singleton::"Set(Set('a))" ("\<exists>\<^sub>1")  (*\<exists>\<^sub>1 contains the singletons (sets with one single element)*)
  where \<open>\<exists>\<^sub>1A \<equiv> \<exists>x. A x \<and> (\<forall>y. A y \<rightarrow> x = y)\<close>
definition doubleton::"Set(Set('a))" ("\<exists>\<^sub>2") (*\<exists>\<^sub>2 contains the doubletons (sets with two (different) elements)*)
  where \<open>\<exists>\<^sub>2A \<equiv> \<exists>x y. x \<noteq> y \<and> A x \<and> A y \<and> (\<forall>z. A z \<rightarrow> (z = x \<or> z = y))\<close>
definition upair::"Set(Set('a))" ("\<exists>\<^sub>\<le>\<^sub>2") (*\<exists>\<^sub>\<le>\<^sub>2 contains the unordered pairs (sets with at most 2 elements)*)
  where \<open>\<exists>\<^sub>\<le>\<^sub>2A \<equiv> \<exists>x y. A x \<and> A y \<and> (\<forall>z. A z \<rightarrow> (z = x \<or> z = y))\<close>

declare unique_def[set_defs] singleton_def[set_defs] 
        doubleton_def[set_defs] upair_def[set_defs] 

lemma unique_def2: "\<exists>\<^sub>\<le>\<^sub>1 = \<nexists> \<union> \<exists>\<^sub>1" unfolding set_defs comb_defs by auto
lemma singleton_def2: "\<exists>\<^sub>1 = \<exists> \<inter> \<exists>\<^sub>\<le>\<^sub>1" unfolding set_defs comb_defs by metis
lemma doubleton_def2: "\<exists>\<^sub>2 = \<exists>\<^sub>\<le>\<^sub>2 \<setminus> \<exists>\<^sub>1" unfolding set_defs comb_defs by blast
lemma upair_def2: "\<exists>\<^sub>\<le>\<^sub>2 = \<exists>\<^sub>1 \<union> \<exists>\<^sub>2" unfolding set_defs comb_defs by blast

end