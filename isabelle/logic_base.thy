theory logic_base (* base theory for logic-based developments *)
   imports combinators types
begin

(******************** config technicalities ******************)
declare[[smt_timeout=30]]
(* declare[[show_types]] *)
declare[[syntax_ambiguity_warning=false]]
sledgehammer_params[max_facts=100,isar_proof=false,abduce=0,falsify=false,
    provers=cvc4 cvc5 verit z3 e spass vampire zipperposition remote_leo3]
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, max_potential=0,max_genuine=1, format=3] (*default Nitpick settings*)
(*************************************************************)

section \<open>Base\<close>

subsection \<open>Boolean connectives\<close>

subsubsection \<open>Boolean operations\<close>

notation HOL.implies (infixr "\<rightarrow>" 25) (* convenient alternative notation*)
notation HOL.iff (infixr "\<leftrightarrow>" 25) (* convenient alternative notation*)

(*Add convenient logical connectives*)
abbreviation(input) seilpmi (infixl "\<leftarrow>" 25) (* reversed implication *)
  where "A \<leftarrow> B \<equiv> B \<rightarrow> A"
abbreviation(input) excludes (infixl "\<leftharpoondown>" 25) (*aka. co-implication*)
  where "A \<leftharpoondown> B \<equiv> A \<and> \<not>B"
abbreviation(input) sedulcxe (infixr "\<rightharpoonup>" 25) (*aka. dual-implication*)
  where "A \<rightharpoonup> B \<equiv> B \<leftharpoondown> A"
abbreviation(input) xor (infix "\<rightleftharpoons>" 25) (*aka. symmetric difference*)
  where "A \<rightleftharpoons> B \<equiv> A \<noteq> B"
abbreviation(input) nand (infix "\<up>" 35) (*aka. Sheffer stroke*)
  where "A \<up> B \<equiv> \<not>(A \<and> B)"
abbreviation(input) nor (infix "\<down>" 30) (*aka. Peirce arrow or Quine dagger*)
  where "A \<down> B \<equiv> \<not>(A \<or> B)"

(*Check relationships*)
lemma disj_impl: "(A \<or> B) = ((A \<rightarrow> B) \<rightarrow> B)" by auto
lemma conj_excl: "(A \<and> B) = ((A \<rightharpoonup> B) \<rightharpoonup> B)" by auto
lemma xor_excl: "(A \<rightleftharpoons> B) = (A \<leftharpoondown> B) \<or> (A \<rightharpoonup> B)" by auto

(*Reintroduces notation for negation to allow for conveniently referring to it as '\<not>' *)
notation(input) HOL.Not ("\<not>" 40)
notation(output) HOL.Not ("\<not>_" [40] 40)


subsubsection \<open>Boolean ordering\<close>

notation(input) HOL.implies (infixr "\<le>" 50) (* convenient alternative notation*)


subsection \<open>Description(-like) operators\<close>

(*Add (binder) notation for definite descriptions (incl. binder notation)*)
notation HOL.The ("\<iota>") and HOL.The (binder "\<iota>" 10)

(*Add (binder) notation for indefinite descriptions (aka. Hilbert's epsilon or choice operator)*)
notation Hilbert_Choice.Eps ("\<epsilon>") and Hilbert_Choice.Eps (binder "\<epsilon>" 10)

(*Introduce a convenient 'dual' to Hilbert's epsilon operator (adds variable-binding notation)*)
definition Delta ("\<delta>")
  where "\<delta> \<equiv> \<lambda>A. \<epsilon> (\<lambda>x. \<not>A x)"

notation Delta (binder "\<delta>" 10) 

(*Sanity checks*)
lemma "(\<iota> x. A x) = (THE x. A x)" ..
lemma "(\<epsilon> x. A x) = (SOME x. A x)" ..
lemma "(\<delta> x. A x) = (SOME x. \<not>A x)" unfolding Delta_def ..


subsection \<open>Quantifiers\<close>

(*We introduce (pedagogically convenient) notation for HOL logical constants*)
notation HOL.All ("\<forall>") 
notation HOL.Ex  ("\<exists>")

abbreviation NotEx ("\<nexists>") (*for convenience*)
  where "\<nexists>A \<equiv> \<not>\<exists>A"

(*Quantifiers are in fact definable from \<epsilon> and \<delta> using the \<^bold>O combinator (Smullyan's 'owl')*)
lemma Ex_def2: "\<exists> = \<^bold>O \<epsilon>" unfolding comb_defs by (metis (full_types))
lemma All_def2: "\<forall> = \<^bold>O \<delta>"  unfolding Delta_def comb_defs by (meson someI_ex)

lemma "\<exists>\<phi> = \<phi>(\<epsilon> x. \<phi> x)" unfolding Ex_def2 comb_defs ..
lemma "\<forall>\<phi> = \<phi>(\<epsilon> x. \<not>\<phi> x)" unfolding Delta_def All_def2 comb_defs ..


subsection \<open>Equality and disequality\<close>

(*Convenient combinator-like symbols \<Q> resp. \<D> to be used instead of (=) resp. (\<noteq>)*)
notation HOL.eq ("\<Q>") and HOL.not_equal ("\<D>")

(*Removes the (=) resp. (\<noteq>) symbols from output (we want to see \<Q>/{_} resp. \<D>/\<lbrace>_\<rbrace> instead) *)
no_notation(output)
  HOL.eq (infix "=" 50) and HOL.not_equal (infix "\<noteq>" 50)
notation (output)
  HOL.eq  ("(_ =/ _)" [51, 51] 50) and HOL.not_equal  ("(_ \<noteq>/ _)" [51, 51] 50)


subsection \<open>Hiding symbols and notation from the Isabelle library\<close>

(*We hide many symbols and notation from the Isabelle library (which we don't use) to avoid collisions.*)
hide_const(open) Set.subset Set.subset_eq Set.supset Set.supset_eq 
                 Set.union Set.inter 
                 Set.range Set.image Set.vimage  
                 Set.is_empty Set.member Set.is_singleton
                 Relation.converse Relation.Range Relation.total 
                 Complete_Lattices.Inter Complete_Lattices.Union 
                 Hilbert_Choice.bijection Transitive_Closure.reflcl
                 Orderings.top_class.top Orderings.bot_class.bot
                 Orderings.ord_class.less_eq Orderings.ord_class.less
                 Orderings.ord_class.greater_eq Orderings.ord_class.greater
                 BNF_Def.convol 
                 Product_Type.prod Product_Type.Pair Product_Type.Pair_Rep Product_Type.Times
                 Fields.inverse_class.inverse_divide
                 Transitive_Closure.trancl Transitive_Closure.rtrancl
                 Lattices.sup_class.sup Lattices.inf_class.inf
                 (* Fun.comp Fun.fun_upd *)

no_notation (*so we can use those symbols for our own purposes*)
  Set.subset  ("'(\<subset>')") and Set.subset  ("(_/ \<subset> _)" [51, 51] 50) and
  Set.subset_eq  ("'(\<subseteq>')") and Set.subset_eq  ("(_/ \<subseteq> _)" [51, 51] 50) and
  Set.supset  ("'(\<supset>')") and Set.supset  ("(_/ \<supset> _)" [51, 51] 50) and
  Set.supset_eq  ("'(\<supseteq>')") and Set.supset_eq  ("(_/ \<supseteq> _)" [51, 51] 50) and
  Set.union (infixl "\<union>" 65) and Set.inter (infixl "\<inter>" 70) and
  Set.member  ("'(:')") and Set.member  ("(_/ : _)" [51, 51] 50) and
  Complete_Lattices.Inter ("\<Inter>") and Complete_Lattices.Union ("\<Union>") and
  Relation.converse ("(_\<inverse>)" [1000] 999) and
  Transitive_Closure.reflcl ("(_\<^sup>=)" [1000] 999) and
  Orderings.top_class.top ("\<top>") and
  Orderings.bot_class.bot ("\<bottom>") and
  Orderings.less_eq ("'(\<le>')") and Orderings.less  ("'(<')") and
  Orderings.less_eq ("(_/ \<le> _)" [51, 51] 50) and Orderings.less ("(_/ < _)" [51, 51] 50) and
  Orderings.greater_eq  (infix "\<ge>" 50) and Orderings.greater (infix ">" 50) and  
  BNF_Def.convol ("\<langle>(_,/ _)\<rangle>") and
  Product_Type.Pair ("(_,/ _)" [21, 20] 20) and Product_Type.Times (infixr "\<times>" 80) and
  Fields.inverse_class.inverse_divide (infixl "'/" 70) and
  Transitive_Closure.trancl ("(_\<^sup>+)" [1000] 999) and Transitive_Closure.rtrancl ("(_\<^sup>*)" [1000] 999) and
  Lattices.sup_class.sup (infixl "\<squnion>" 65) and Lattices.inf_class.inf (infixl "\<sqinter>" 70) and
  Fun.comp (infixl "\<circ>" 55) and Fun.comp (infixl "o" 55)
no_syntax
  "_Finset" :: "args \<Rightarrow> 'a set" ("{(_)}")

subsection \<open>Notation tests\<close>

term "\<epsilon>"
term "\<delta>"
term "\<iota>"
term "\<epsilon> A"
term "\<delta> A"
term "\<iota> A"
term "\<epsilon> x. A x"
term "\<delta> x. A x"
term "\<iota> x. A x"
term "\<lambda>x. \<not>x"
term "\<not>a"
term "\<not>a \<or> b"
term "\<not>f a \<or> \<not>\<not>f a"
term "\<not>(f a \<or> h)"
term "\<not>"
term "(\<not>) \<circ> A"
term "A \<circ> (\<not>)"
term "\<Q>"
term "\<D>"
term "\<Q> a"
term "\<D> a"
term "(=)"
term "(\<noteq>)"
term "a = b"
term "a \<noteq> b"
term "(=)a"
term "(\<noteq>)a"
term "\<lambda>x. a = x"
term "\<lambda>x. a \<noteq> x"
term "\<lambda>x. x = a" (*symmetry of equality is not automatically considered*)
term "\<lambda>x. x \<noteq> a" (*symmetry of disequality is not automatically considered*)

end