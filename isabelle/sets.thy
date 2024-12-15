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
definition inter::"EOp\<^sub>2(Set('a))" (infixl "\<inter>" 54) 
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
  where "\<Inter> \<equiv> \<forall> \<circ>\<^sub>2 (\<^bold>B\<^sub>2\<^sub>1\<^sub>0 (\<Leftarrow>) \<^bold>T)"
definition bigunion::"EOp\<^sub>G(Set('a))" ("\<Union>")
  where "\<Union> \<equiv> \<exists> \<circ>\<^sub>2 (\<^bold>B\<^sub>2\<^sub>1\<^sub>0 ((\<inter>)\<^sup>t) \<^bold>T)" (*TODO: redefine without transposition*)

lemma "\<Inter>S x = (\<forall>A. S A \<rightarrow> A x)" unfolding biginter_def set_defs comb_defs ..
lemma "\<Union>S x = (\<exists>A. S A \<and> A x)" unfolding bigunion_def set_defs comb_defs ..

declare biginter_def[set_defs] bigunion_def[set_defs]


subsubsection \<open>Ordering (subset/superset), Overlapping and Covering\<close>

(*The algebra of sets is ordered by the standard subset (endo)relation, as defined below.*)
definition subset::"ERel(Set('a))" (infixr "\<subseteq>" 51) 
  where "(\<subseteq>) \<equiv> \<forall> \<circ>\<^sub>2 (\<Rightarrow>)"
definition psubset::"ERel(Set('a))" (infixr "\<subset>" 51) (*proper subset*)
  where "(\<subset>) \<equiv> (\<and>) \<circ>\<^sub>2 \<langle> (\<subseteq>) , (\<exists> \<circ>\<^sub>2 ((\<setminus>)\<^sup>t)) \<rangle>"

declare subset_def[set_defs] psubset_def[set_defs]

lemma "A \<subseteq> B = (\<forall>x. A x \<rightarrow> B x)" unfolding set_defs comb_defs ..
lemma "A \<subset> B = (A \<subseteq> B \<and> \<exists>(B \<setminus> A))" unfolding set_defs comb_defs ..

(*Let us add the following convenient abbreviations for the reversed versions of (proper) subset*)
abbreviation(input) superset::"ERel(Set('a))" (infixr "\<supseteq>" 51)
  where "(\<supseteq>) \<equiv> (\<subseteq>)\<^sup>t" 
abbreviation(input) psuperset::"ERel(Set('a))" (infixr "\<supset>" 51) (*proper superset*)
  where "(\<supset>) \<equiv> (\<subset>)\<^sup>t" 

(* The powerset operation corresponds to the (partial) application of superset *)
notation superset ("\<wp>")

(*As expected*)
lemma "(A \<supseteq> B) = (B \<subseteq> A)" unfolding comb_defs ..
lemma "(A \<supset> B) = (B \<subset> A)" unfolding comb_defs ..
lemma "\<wp>A = (\<lambda>B. B \<subseteq> A)" unfolding comb_defs ..


(*Characterizing properties of bigunion and biginter*)
lemma biginter_prop: "S A \<longrightarrow> \<Inter>S \<subseteq> A" 
  unfolding set_defs comb_defs by auto
lemma bigunion_prop: "S A \<longrightarrow> A \<subseteq> \<Union>S" 
  unfolding set_defs comb_defs by auto

(*Two sets are said to 'overlap' (or 'intersect') if their intersection is non-empty*)
abbreviation(input) overlap::"ERel(Set('a))" (infixr "\<sqinter>" 52)
  where "(\<sqinter>) \<equiv> \<exists> \<circ>\<^sub>2 (\<inter>)"
(*dually, two sets form a 'cover' if every element belongs to one or the other *)
abbreviation(input) cover::"ERel(Set('a))" (infixr "\<squnion>" 53)
  where "(\<squnion>) \<equiv> \<forall> \<circ>\<^sub>2 (\<union>)"

lemma "A \<sqinter> B = \<exists>(A \<inter> B)" unfolding set_defs comb_defs ..
lemma "A \<squnion> B = \<forall>(A \<union> B)" unfolding set_defs comb_defs ..

(*Two sets are said to be 'disjoint' if their intersection is empty*)
abbreviation(input) disj::"ERel(Set('a))" (infixr "\<bottom>" 52)
  where "(\<bottom>) \<equiv> \<not> \<circ>\<^sub>2 (\<sqinter>)"

lemma "A \<bottom> B = \<nexists>(A \<inter> B)" unfolding set_defs comb_defs ..

(*We say of a set of sets that it 'overlaps' (or 'intersects') if there exists a 'shared' element.*)
abbreviation(input) bigoverlap::"Set(Set(Set('a)))" ("\<Sqinter>")
  where "\<Sqinter> \<equiv> \<exists> \<circ> \<Inter>"
(*dually, a set of sets forms a 'cover' if every element is contained in at least one of the sets.*)
abbreviation(input) bigcover::"Set(Set(Set('a)))" ("\<Squnion>")
  where "\<Squnion> \<equiv> \<forall> \<circ> \<Union>"

lemma "\<Sqinter>S = \<exists>(\<Inter>S)" unfolding set_defs comb_defs ..
lemma "\<Squnion>S = \<forall>(\<Union>S)" unfolding set_defs comb_defs ..


subsection \<open>Constructing sets\<close>

(*Finite unordered tuples (up to size 4) *)
abbreviation(input) mk_upair::"'a \<Rightarrow> 'a \<Rightarrow> Set('a)" ("{_,_}")
  where \<open>{a,b} \<equiv> {a} \<union> {b}\<close>
abbreviation(input) mk_utriple::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> Set('a)" ("{_,_,_}")
  where \<open>{a,b,c} \<equiv> {a,b} \<union> {c}\<close>
abbreviation(input) mk_uquadruple::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> Set('a)" ("{_,_,_,_}")
  where \<open>{a,b,c,d} \<equiv> {a,b,c} \<union> {d}\<close>

(*Cofinite unordered (co)tuples (up to size |\<UU>| - 4) *)
abbreviation(input) mk_coupair::"'a \<Rightarrow> 'a \<Rightarrow> Set('a)" ("\<lbrace>_,_\<rbrace>")
  where \<open>\<lbrace>a,b\<rbrace> \<equiv> \<lbrace>a\<rbrace> \<inter> \<lbrace>b\<rbrace>\<close>
abbreviation(input) mk_coutriple::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> Set('a)" ("\<lbrace>_,_,_\<rbrace>")
  where \<open>\<lbrace>a,b,c\<rbrace> \<equiv> \<lbrace>a,b\<rbrace> \<inter> \<lbrace>c\<rbrace>\<close>
abbreviation(input) mk_couquadruple::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> Set('a)" ("\<lbrace>_,_,_,_\<rbrace>")
  where \<open>\<lbrace>a,b,c,d\<rbrace> \<equiv> \<lbrace>a,b,c\<rbrace> \<inter> \<lbrace>d\<rbrace>\<close>

(*Tuples and co-tuples are related via set-complement as expected*)
lemma "\<lbrace>a\<rbrace> = \<midarrow>{a}" 
  unfolding set_defs comb_defs ..
lemma "\<lbrace>a,b\<rbrace> = \<midarrow>{a,b}" 
  unfolding set_defs comb_defs by simp
lemma "\<lbrace>a,b,c\<rbrace> = \<midarrow>{a,b,c}" 
  unfolding set_defs comb_defs by simp
lemma "\<lbrace>a,b,c,d\<rbrace> = \<midarrow>{a,b,c,d}" 
  unfolding set_defs comb_defs by simp

(*Convenient lemmata (added as simplification rules)*)
lemma upair_simp: \<open>{a,b} = (\<lambda>x. x = a \<or> x = b)\<close> 
  unfolding set_defs comb_defs by auto
lemma utriple_simp: \<open>{a,b,c} = (\<lambda>x. x = a \<or> x = b \<or> x = c)\<close> 
  unfolding set_defs comb_defs by auto
lemma uquadruple_simp: \<open>{a,b,c,d} = (\<lambda>x. x = a \<or> x = b \<or> x = c \<or> x = d)\<close> 
  unfolding set_defs comb_defs by auto

lemma coupair_simp: \<open>\<lbrace>a,b\<rbrace> = (\<lambda>x. x \<noteq> a \<and> x \<noteq> b)\<close> 
  unfolding set_defs comb_defs by auto
lemma coutriple_simp: \<open>\<lbrace>a,b,c\<rbrace> = (\<lambda>x. x \<noteq> a \<and> x \<noteq> b \<and> x \<noteq> c)\<close> 
  unfolding set_defs comb_defs by auto
lemma couquadruple_simp: \<open>\<lbrace>a,b,c,d\<rbrace> = (\<lambda>x. x \<noteq> a \<and> x \<noteq> b \<and> x \<noteq> c \<and> x \<noteq> d)\<close> 
  unfolding set_defs comb_defs by auto

declare upair_simp[set_simps] utriple_simp[set_simps] uquadruple_simp[set_simps]
declare coupair_simp[set_simps] coutriple_simp[set_simps] couquadruple_simp[set_simps]


subsection \<open>Basic properties/predicates on sets\<close> (*TODO: make point-free*)

(*Recalling HOL quantification, we note that "\<forall>A" means that the set A contains all alements*)
lemma "\<forall>A = (\<forall>x. A x)" ..
(*Analogously, "\<exists>A" means: A contains at least one element, i.e. A is nonempty*)
lemma "\<exists>A = (\<exists>x. A x)" ..

(*Quantifiers are particular kinds of spaces (sets of sets) *)
term "\<forall>::Set(Set('a))"
term "\<exists>::Set(Set('a))"
lemma All_simp:"\<forall> = {\<UU>}" (* \<forall> contains only the universe*)
  unfolding set_defs comb_defs by auto 
lemma Ex_simp: "\<exists> = \<lbrace>\<emptyset>\<rbrace>" (* \<exists> contains all but the empty set*)
  unfolding Ex_def set_defs comb_defs by auto 

declare All_simp[set_simps] Ex_simp[set_simps] (* make them simplification rules (TODO: orient)*)

(*Further special kinds of spaces (sets of sets) are: *)
definition unique::"Set(Set('a))" ("\<exists>\<^sub>\<le>\<^sub>1") (*\<exists>\<^sub>\<le>\<^sub>1 contains the sets with at most one element (and which may be empty)*)
  where \<open>\<exists>\<^sub>\<le>\<^sub>1A \<equiv> \<forall>x y. A x \<and> A y \<rightarrow> x = y\<close> 
definition singleton::"Set(Set('a))" ("\<exists>\<^sub>1")  (*\<exists>\<^sub>1 contains the singletons (sets with one single element)*)
  where \<open>\<exists>\<^sub>1A \<equiv> \<exists>x. A x \<and> (\<forall>y. A y \<rightarrow> x = y)\<close>
definition doubleton::"Set(Set('a))" ("\<exists>\<^sub>2") (*\<exists>\<^sub>2 contains the doubletons (sets with two (different) elements)*)
  where \<open>\<exists>\<^sub>2A \<equiv> \<exists>x y. x \<noteq> y \<and> A x \<and> A y \<and> (\<forall>z. A z \<rightarrow> (z = x \<or> z = y))\<close>
definition upair::"Set(Set('a))" ("\<exists>\<^sub>\<le>\<^sub>2") (*\<exists>\<^sub>\<le>\<^sub>2 contains the unordered pairs (sets with at most 2 elements)*)
  where \<open>\<exists>\<^sub>\<le>\<^sub>2A \<equiv> \<exists>x y. A x \<and> A y \<and> (\<forall>z. A z \<rightarrow> (z = x \<or> z = y))\<close>
definition utriple::"Set(Set('a))" ("\<exists>\<^sub>\<le>\<^sub>3") (*\<exists>\<^sub>\<le>\<^sub>3 contains the unordered triples (sets with at most 3 elements)*)
  where \<open>\<exists>\<^sub>\<le>\<^sub>3A \<equiv> \<exists>x y z. A x \<and> A y \<and> A z \<and> (\<forall>u. A u \<rightarrow> (u = x \<or> u = y \<or> u = z))\<close>
definition uquadruple::"Set(Set('a))" ("\<exists>\<^sub>\<le>\<^sub>4") (*\<exists>\<^sub>\<le>\<^sub>4 contains the unordered quadruples*)
  where \<open>\<exists>\<^sub>\<le>\<^sub>4A \<equiv> \<exists>x y z u. A x \<and> A y \<and> A z \<and> A u \<and> (\<forall>w. A w \<rightarrow> (w = x \<or> w = y \<or> w = z \<or> w = u))\<close>

declare unique_def[set_defs] singleton_def[set_defs] doubleton_def[set_defs] 
  upair_def[set_defs] utriple_def[set_defs] uquadruple_def[set_defs]

lemma singleton_def2: "\<exists>\<^sub>1A = (\<exists>A \<and> \<exists>\<^sub>\<le>\<^sub>1A)"
  unfolding set_defs by auto
lemma singleton_def3: "\<exists>\<^sub>1A = (\<exists>a. A = {a})"
  unfolding singleton_def2 unfolding set_defs by auto

lemma doubleton_def2: "\<exists>\<^sub>2A = (\<exists>\<^sub>\<le>\<^sub>2A \<and> \<not>\<exists>\<^sub>1A)"
  unfolding set_defs by auto
lemma doubleton_def3: "\<exists>\<^sub>2A = (\<exists>a b. a \<noteq> b \<and> A = {a,b})"
  unfolding set_defs unfolding comb_defs by auto

lemma upair_def2: "\<exists>\<^sub>\<le>\<^sub>2A = (\<exists>\<^sub>1A \<or> \<exists>\<^sub>2A)" 
  unfolding set_defs by auto
lemma upair_def3: "\<exists>\<^sub>\<le>\<^sub>2A = (\<exists>a b. A = {a,b})" 
  unfolding set_defs unfolding comb_defs by auto

(*Sets are the bigunions of their contained singletons resp. unordered pairs*)
lemma singleton_gen: "S = \<Union>(\<wp>S \<inter> \<exists>\<^sub>1)" 
  unfolding singleton_def3 set_defs comb_defs by metis
lemma upair_gen: "S = \<Union>(\<wp>S \<inter> \<exists>\<^sub>\<le>\<^sub>2)"
  unfolding upair_def2 singleton_def3 doubleton_def3 unfolding set_defs comb_defs by metis

lemma singleton_prop: "(\<forall>D. D \<subseteq> S \<rightarrow> \<exists>\<^sub>1D \<rightarrow> P D) = (\<forall>x. S x \<rightarrow> P {x})"
  unfolding singleton_def3 unfolding set_defs comb_defs by (metis (full_types))
lemma doubleton_prop: "(\<forall>D. D \<subseteq> S \<rightarrow> \<exists>\<^sub>2D \<rightarrow> P D) = (\<forall>x y. S x \<and> S y \<rightarrow> x \<noteq> y \<rightarrow> P {x,y})"
  unfolding doubleton_def3 unfolding set_defs comb_defs by (smt (verit))
lemma upair_prop: "(\<forall>D. D \<subseteq> S \<rightarrow> \<exists>\<^sub>\<le>\<^sub>2D \<rightarrow> P D) = (\<forall>x y. S x \<and> S y \<rightarrow> P {x,y})" 
  unfolding upair_def3 upair_simp unfolding set_defs comb_defs by (smt (verit, best))


subsection \<open>Closure under operations\<close>

(*The set S is closed under the given unary (endo)operation*)
definition closedUnderOp::"EOp('a) \<Rightarrow> Set('a) \<Rightarrow> o"
  where "closedUnderOp \<phi> \<equiv> \<lambda>S. \<forall>a. S a \<longrightarrow> S (\<phi> a)"
(*The set S is closed under the given binary (endo)operation*)
definition closedUnderBinOp::"EOp\<^sub>2('a) \<Rightarrow> Set('a) \<Rightarrow> o"
  where "closedUnderBinOp \<phi> \<equiv> \<lambda>S. \<forall>a b. S a \<and> S b \<longrightarrow> S (\<phi> a b)"
(*The set S is closed under the given generalized (endo)operation*)
definition closedUnderGenOp::"EOp\<^sub>G('a) \<Rightarrow> Set('a) \<Rightarrow> o"
  where "closedUnderGenOp \<phi> \<equiv> \<lambda>S. \<forall>D. D \<subseteq> S \<longrightarrow> S (\<phi> D)"

(*The same notation can be used for the three cases above in unambiguous contexts*)
notation closedUnderOp ("closedUnder")
notation closedUnderBinOp ("closedUnder")
notation closedUnderGenOp ("closedUnder")

(*Moreover, we can state that a set S is closed under a given (endo)operation on its subsets*)
definition closedUnderSetOp::"EOp(Set('a)) \<Rightarrow> Set('a) \<Rightarrow> o" ("closedUnderSetOp")
  where "closedUnderSetOp \<phi> \<equiv> \<lambda>S. \<forall>D. D \<subseteq> S \<longrightarrow> (\<phi> D) \<subseteq> S"
(*Oftentimes, we need to restrict the quantification domain to S-subsets that satisfy a property P*)
definition closedUnderSetOp_restr::"Set(Set('a)) \<Rightarrow> EOp(Set('a)) \<Rightarrow> Set('a) \<Rightarrow> o" ("closedUnderSetOp|(_)")
  where "closedUnderSetOp|P \<phi> \<equiv> \<lambda>S. \<forall>D. D \<subseteq> S \<longrightarrow> P D \<longrightarrow> (\<phi> D) \<subseteq> S"

declare closedUnderOp_def[set_defs] closedUnderBinOp_def[set_defs] closedUnderGenOp_def[set_defs]
        closedUnderSetOp_def[set_defs] closedUnderSetOp_restr_def[set_defs]

(*It is common to restrict the quantification domain to non-empty sets. Following lemmata apply:*)
lemma "closedUnderSetOp \<phi> S \<longrightarrow> closedUnderSetOp|\<exists> \<phi> S" 
  unfolding set_defs by simp

(*Note, however that*)
lemma "\<exists>S \<Longrightarrow> (closedUnderSetOp|\<exists> \<phi> S) \<longrightarrow> closedUnderSetOp \<phi> S" nitpick oops (*counterexample*)

(*It holds, indeed, that*)
abbreviation "MONO \<phi> \<equiv> \<forall>A B. A \<subseteq> B \<longrightarrow> \<phi> A \<subseteq> \<phi> B"
lemma closedUnderSetOp_nonEmpty: "MONO \<phi> \<Longrightarrow> \<exists>S \<Longrightarrow> closedUnderSetOp|\<exists> \<phi> S = closedUnderSetOp \<phi> S" 
  unfolding set_defs comb_defs by blast

end