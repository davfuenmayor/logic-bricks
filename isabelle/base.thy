theory base (* base theory for logic-based developments in Isabelle/HOL*)
   imports combinators
begin

section \<open>Customized configuration and notation for Isabelle/HOL\<close>

subsection \<open>Tool configuration\<close>

declare[[smt_timeout=30]]
(* declare[[show_types]] *)
declare[[syntax_ambiguity_warning=false]]
sledgehammer_params[max_facts=100,isar_proof=false]
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, max_potential=0,max_genuine=1, format=3] (*default Nitpick settings*)

subsection \<open>Custom type notation\<close>

(*Classical HOL systems come with a built-in boolean type, for which we introduce convenient notation alias*)
type_notation bool ("o")

(*The creation of a functional type (starting with a type 'a) can be seen from two complementary perspectives:
 Environmentalization (aka. indexation or contextualization) and valuation (e.g. classification, coloring, etc.) *)
type_synonym ('e,'a)Env = "'e \<Rightarrow> 'a" ("_-Env'(_')" [1000])
type_synonym ('v,'a)Val = "'a \<Rightarrow> 'v" ("_-Val'(_')" [1000])

(*Starting with the boolean type, we immediately obtain endopairs resp. sets via indexation resp. valuation*)
type_synonym ('a)EPair = "o-Env('a)" ("EPair'(_')")  (*an endopair is encoded as a boolean-index *)
type_synonym ('a)Set = "o-Val('a)" ("Set'(_')")  (*a set is encoded as a boolean-valuation (boolean classifier)*)

term "((S :: Set('a)):: 'a-Env(o)) :: 'a \<Rightarrow> o"
term "((P :: EPair('a)):: 'a-Val(o)) :: o \<Rightarrow> 'a"

(*Valuations can be made binary (useful e.g. for classifying pairs of objects or encoding their 'distance')*)
type_synonym ('v,'a,'b)Val2 = "'a \<Rightarrow> 'b \<Rightarrow> 'v" ("_-Val\<^sub>2'(_,_')" [1000])

(*Binary valuations can also be seen as indexed (unary) valuations*)
term "((G :: 'v-Val\<^sub>2('a,'b)) :: 'a-Env('v-Val('b))) :: 'a \<Rightarrow> 'b \<Rightarrow> 'v"

(*In fact (heterogeneous) relations correspond to o-valued binary functions/valuations*)
type_synonym ('a,'b)Rel = "o-Val\<^sub>2('a,'b)" ("Rel'(_,_')")
(*They can also be seen as set-valued functions/valuations or as indexed (families of) sets*)
term "(((R :: Rel('a,'b)) :: Set('b)-Val('a)) :: 'a-Env(Set('b))) :: 'a \<Rightarrow> 'b \<Rightarrow> o"

(*Ternary relations are seen as set-valued binary valuations (partial & non-deterministic binary functions)*)
type_synonym ('a,'b,'c)Rel3 = "Set('c)-Val\<^sub>2('a,'b)" ("Rel\<^sub>3'(_,_,_')")
(*They can also be seen as indexed binary relations (e.g. an indexed family of programs or (a group of) agents)*)
term "((R::Rel\<^sub>3('a,'b,'c)) :: 'a-Env(Rel('b,'c))) :: 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> o"

(*In general, we can encode n+1-ary relations as indexed n-ary relations*)
type_synonym ('a,'b,'c,'d)Rel4 = "'a-Env(Rel\<^sub>3('b,'c,'d))" ("Rel\<^sub>4'(_,_,_,_')")

(*Convenient notation for the particular case where the relata have all the same type*)
type_synonym ('a)ERel = "Rel('a,'a)" ("ERel'(_')") (* (binary) endorelations*)
type_synonym ('a)ERel\<^sub>3 = "Rel\<^sub>3('a,'a,'a)" ("ERel\<^sub>3'(_')") (*ternary endorelations*)
type_synonym ('a)ERel\<^sub>4 = "Rel\<^sub>4('a,'a,'a,'a)" ("ERel\<^sub>4'(_')") (*quaternary endorelations*)

term "(R :: ERel('a)) :: 'a \<Rightarrow> 'a \<Rightarrow> o"
term "(R :: ERel\<^sub>3('a)) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> o"
term "(R :: ERel\<^sub>4('a)) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> o"


(*As a convenient mathematical abstraction, we introduce the notion of "operation".
In mathematical phraseology, operations are said to "operate" on (one or more) "operands".
Operations can be seen as (curried) functions whose arguments have all the same type.*)

(*Unary case: (endo)operations just correspond to (endo)functions*)
type_synonym ('a,'b)Op1 = "'a \<Rightarrow> 'b" ("Op'(_,_')")
type_synonym ('a)EOp1 = "Op('a,'a)" ("EOp'(_')") (* same as: 'a \<Rightarrow> 'a *)

(*Binary case: (endo)bi-operations correspond to curried (endo)bi-functions*)
type_synonym ('a,'b)Op2 = "'a \<Rightarrow> 'a \<Rightarrow> 'b" ("Op\<^sub>2'(_,_')")
type_synonym ('a)EOp2 = "Op\<^sub>2('a,'a)" ("EOp\<^sub>2'(_')") (* same as: 'a \<Rightarrow> ('a \<Rightarrow> 'a) *)

(*Arbitrary case: generalized (endo)operations correspond to (endo)functions on sets*)
type_synonym ('a,'b)OpG = "Op(Set('a),'b)" ("Op\<^sub>G'(_,_')")
type_synonym ('a)EOpG = "Op\<^sub>G('a,'a)" ("EOp\<^sub>G'(_')") (* same as: Set('a) \<Rightarrow> 'a *)

(*** Operations on sets ***)
(*Convenient type aliases for (endo)operations on sets*)
type_synonym ('a,'b)SetOp = "Op(Set('a),Set('b))" ("SetOp'(_,_')")
type_synonym ('a)SetEOp = "SetOp('a,'a)" ("SetEOp'(_')") (* same as: Set('a) \<Rightarrow> Set('a) *)
(*Binary case: (endo)bi-operations correspond to curried (endo)bi-functions*)
type_synonym ('a,'b)SetOp2 = "Set('a) \<Rightarrow> Set('a) \<Rightarrow> Set('b)" ("SetOp\<^sub>2'(_,_')")
type_synonym ('a)SetEOp2 = "SetOp\<^sub>2('a,'a)" ("SetEOp\<^sub>2'(_')") (*same as: Set('a) \<Rightarrow> Set('a) \<Rightarrow> Set('a) *)

(*** Continuations (with result type 'r) take inputs of type 'a ***)
(* Unary case:  *)
type_synonym ('a,'r)Cont1 = "'r-Val(Op('a,'r))" ("Cont'(_,_')") (*same as: ('a \<Rightarrow> 'r) \<Rightarrow> 'r *)
(* Binary case:  *)
type_synonym ('a,'r)Cont2 = "'r-Val(Op\<^sub>2('a,'r))" ("Cont\<^sub>2'(_,_')") (*same as: ('a \<Rightarrow> 'a \<Rightarrow> 'r) \<Rightarrow> 'r *)


subsection \<open>Custom term notation\<close>

(*Convenient combinator-like symbols \<Q> resp. \<D> to be used instead of (=) resp. (\<noteq>)*)
notation HOL.eq ("\<Q>") and HOL.not_equal ("\<D>")

(*Removes the (=) resp. (\<noteq>) symbols from output (we want to see \<Q>/{_} resp. \<D>/\<lbrace>_\<rbrace> instead) *)
no_notation(output)
  HOL.eq (infix "=" 50) and HOL.not_equal (infix "\<noteq>" 50)
notation (output)
  HOL.eq  ("(_ =/ _)" [51, 51] 50) and HOL.not_equal  ("(_ \<noteq>/ _)" [51, 51] 50)

(*Alternative (more concise) notation for boolean constants*)
notation HOL.True ("\<T>") and HOL.False ("\<F>")

(*Add (binder) notation for indefinite descriptions (aka. Hilbert's epsilon or choice operator)*)
notation Hilbert_Choice.Eps ("\<epsilon>") and Hilbert_Choice.Eps (binder "\<epsilon>" 10)

(*Introduce a convenient 'dual' to Hilbert's epsilon operator (adds variable-binding notation)*)
definition Delta ("\<delta>")
  where "\<delta> \<equiv> \<lambda>A. \<epsilon> (\<lambda>x. \<not>A x)"

notation Delta (binder "\<delta>" 10) 

(*Sanity checks*)
lemma "(\<epsilon> x. A x) = (SOME x. A x)" ..
lemma "(\<delta> x. A x) = (SOME x. \<not>A x)" unfolding Delta_def ..

(*Add (binder) notation for definite descriptions (incl. binder notation)*)
notation HOL.The ("\<iota>") and HOL.The (binder "\<iota>" 10)

lemma "(\<iota> x. A x) = (THE x. A x)" ..

(*We introduce (pedagogically convenient) notation for HOL logical constants*)
notation HOL.All ("\<forall>") 
notation HOL.Ex  ("\<exists>")
abbreviation Empty ("\<nexists>")
  where "\<nexists>A \<equiv> \<not>\<exists>A"                           

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
                 Orderings.ord_class.min Orderings.ord_class.max
                 BNF_Def.convol 
                 Product_Type.prod Product_Type.Pair Product_Type.Pair_Rep Product_Type.Times
                 Transitive_Closure.trancl Transitive_Closure.rtrancl
                 Lattices.sup_class.sup Lattices.inf_class.inf
                 (* Fun.comp Fun.fun_upd *)

unbundle no set_enumeration_syntax
(* no_syntax "_Finset" :: "args \<Rightarrow> 'a set" ("{(_)}") *)

unbundle no member_ASCII_syntax
(*no_notation Set.member  ("'(:')") and Set.member  ("(_/ : _)" [51, 51] 50) and *)

no_notation
  Set.subset  (\<open>'(\<subset>')\<close>) and
  Set.subset  (\<open>(\<open>notation=\<open>infix \<subset>\<close>\<close>_/ \<subset> _)\<close> [51, 51] 50) and
  Set.subset_eq  (\<open>'(\<subseteq>')\<close>) and
  Set.subset_eq  (\<open>(\<open>notation=\<open>infix \<subseteq>\<close>\<close>_/ \<subseteq> _)\<close> [51, 51] 50)
(*no_notation Set.subset  ("'(\<subset>')") and Set.subset  ("(_/ \<subset> _)" [51, 51] 50) and *)
  (* Set.subset_eq  ("'(\<subseteq>')") and Set.subset_eq  ("(_/ \<subseteq> _)" [51, 51] 50) *)

no_notation
  Set.supset  (\<open>'(\<supset>')\<close>) and
  Set.supset  (\<open>(\<open>notation=\<open>infix \<supset>\<close>\<close>_/ \<supset> _)\<close> [51, 51] 50) and
  Set.supset_eq  (\<open>'(\<supseteq>')\<close>) and
  Set.supset_eq  (\<open>(\<open>notation=\<open>infix \<supseteq>\<close>\<close>_/ \<supseteq> _)\<close> [51, 51] 50)

no_notation
  Set.union (infixl "\<union>" 65) and Set.inter (infixl "\<inter>" 70) and
  Complete_Lattices.Inter ("\<Inter>") and Complete_Lattices.Union ("\<Union>")

unbundle no converse_syntax
(* no_notation  Relation.converse ("(_\<inverse>)" [1000] 999) and *)
unbundle no rtrancl_syntax
(* no_notation Transitive_Closure.rtrancl ("(_\<^sup>* )" [1000] 999) *)
unbundle no trancl_syntax
(* no_notation Transitive_Closure.trancl ("(_\<^sup>+)" [1000] 999) *)
unbundle no reflcl_syntax
(* no_notation Transitive_Closure.reflcl ("(_\<^sup>=)" [1000] 999) *)

no_notation BNF_Def.convol (\<open>(\<open>indent=1 notation=\<open>mixfix convol\<close>\<close>\<langle>_,/ _\<rangle>)\<close>)
(* no_notation BNF_Def.convol ("\<langle>(_,/ _)\<rangle>") *)

no_notation
  Orderings.top_class.top ("\<top>") and
  Orderings.bot_class.bot ("\<bottom>") and
  Lattices.sup_class.sup (infixl "\<squnion>" 65) and Lattices.inf_class.inf (infixl "\<sqinter>" 70) 

no_notation Product_Type.Pair (\<open>(\<open>notation=\<open>infix \<times>\<close>\<close>_ \<times>/ _)\<close> [21, 20] 20) 
(*no_notation Product_Type.Pair ("(_,/ _)" [21, 20] 20)  *)

no_notation Product_Type.Times (infixr "\<times>" 80)
no_notation Fun.comp (infixl "\<circ>" 55) and Fun.comp (infixl "o" 55)


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
term "\<nexists> x. A x"
term "\<lambda>x. \<not>x"
term "\<not>a"
term "\<not>a \<or> b"
term "\<not>(a \<or> b)"
term "\<not>f a \<or> \<not>\<not>f a"
term "\<not>(f a \<or> h)"
term "\<not>"
term "(\<not>) A"
term "A (\<not>)"
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