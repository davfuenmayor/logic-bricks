theory base (* base theory for logic-based developments in Isabelle/HOL*)
   imports combinators
begin

section \<open>Customized configuration and notation for Isabelle/HOL\<close>
(*<*)
subsection \<open>Tool Configuration\<close>

declare[[smt_timeout=30]]
(* declare[[show_types]] *)
declare[[syntax_ambiguity_warning=false]]
sledgehammer_params[max_facts=100,isar_proof=false]
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, max_potential=0,max_genuine=1, format=3] (*default Nitpick settings*)
(*>*)

subsection \<open>Custom Type Notation\<close>

subsubsection \<open>Basic Types\<close>

text \<open>Classical HOL systems come with a built-in boolean type, for which we introduce convenient notation alias.\<close>
type_notation bool ("o")

text \<open>The creation of a functional type (starting with a type \<open>'a\<close>) can be seen from two complementary perspectives:
 Environmentalization (aka. indexation or contextualization) and valuation (e.g. classification, coloring, etc.).\<close>
type_synonym ('e,'a)Env = "'e \<Rightarrow> 'a" ("_-Env'(_')" [1000])
type_synonym ('v,'a)Val = "'a \<Rightarrow> 'v" ("_-Val'(_')" [1000])


subsubsection \<open>Pairs and Sets\<close>

text \<open>Starting with the boolean type, we immediately obtain endopairs resp. sets via indexation resp. valuation.\<close>
type_synonym ('a)EPair = "o-Env('a)" ("EPair'(_')")  \<comment> \<open>an endopair is encoded as a boolean-index\<close>
type_synonym ('a)Set = "o-Val('a)" ("Set'(_')")  \<comment> \<open>a set is encoded as a boolean-valuation (boolean classifier)\<close>

term "((P :: EPair('a)):: 'a-Val(o)) :: o \<Rightarrow> 'a"
term "((S :: Set('a)):: 'a-Env(o)) :: 'a \<Rightarrow> o"

text \<open>Sets of endopairs correspond to (directed) graphs (which are isomorphic to relations via currying).\<close>
type_synonym ('a)Graph = "Set(EPair('a))" ("Graph'(_')")
term "(G :: Graph('a)) :: (o \<Rightarrow> 'a) \<Rightarrow> o"

text \<open>Spaces (sets of sets) are the playground of mathematicians, so they deserve a special type notation.\<close>
type_synonym ('a)Space = "Set(Set('a))" ("Space'(_')")
term "(S :: Space('a)) :: ('a \<Rightarrow> o) \<Rightarrow> o"


subsubsection \<open>Relations\<close>

text \<open>Valuations can be made binary (useful e.g. for classifying pairs of objects or encoding their "distance").\<close>
type_synonym ('v,'a,'b)Val2 = "'a \<Rightarrow> 'b \<Rightarrow> 'v" ("_-Val\<^sub>2'(_,_')" [1000])

text \<open>Binary valuations can also be seen as indexed (unary) valuations.\<close>
term "((F :: 'v-Val\<^sub>2('a,'b)) :: 'a-Env('v-Val('b))) :: 'a \<Rightarrow> 'b \<Rightarrow> 'v"

text \<open>In fact (heterogeneous) relations correspond to o-valued binary functions/valuations.\<close>
type_synonym ('a,'b)Rel = "o-Val\<^sub>2('a,'b)" ("Rel'(_,_')")

text \<open>They can also be seen as set-valued functions/valuations or as indexed (families of) sets.\<close>
term "(((R :: Rel('a,'b)) :: Set('b)-Val('a)) :: 'a-Env(Set('b))) :: 'a \<Rightarrow> 'b \<Rightarrow> o"

text \<open>Ternary relations are seen as set-valued binary valuations (partial and non-deterministic binary functions).\<close>
type_synonym ('a,'b,'c)Rel3 = "Set('c)-Val\<^sub>2('a,'b)" ("Rel\<^sub>3'(_,_,_')")

text \<open>They can also be seen as indexed binary relations (e.g. an indexed family of programs or (a group of) agents).\<close>
term "((R::Rel\<^sub>3('a,'b,'c)) :: 'a-Env(Rel('b,'c))) :: 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> o"

text \<open>In general, we can encode n+1-ary relations as indexed n-ary relations.\<close>
type_synonym ('a,'b,'c,'d)Rel4 = "'a-Env(Rel\<^sub>3('b,'c,'d))" ("Rel\<^sub>4'(_,_,_,_')")

text \<open>Convenient notation for the particular case where the relata have all the same type.\<close>
type_synonym ('a)ERel = "Rel('a,'a)" ("ERel'(_')") \<comment> \<open>(binary) endorelations\<close>
type_synonym ('a)ERel\<^sub>3 = "Rel\<^sub>3('a,'a,'a)" ("ERel\<^sub>3'(_')") \<comment> \<open>ternary endorelations\<close>
type_synonym ('a)ERel\<^sub>4 = "Rel\<^sub>4('a,'a,'a,'a)" ("ERel\<^sub>4'(_')") \<comment> \<open>quaternary endorelations\<close>

term "(R :: ERel('a)) :: 'a \<Rightarrow> 'a \<Rightarrow> o"
term "(R :: ERel\<^sub>3('a)) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> o"
term "(R :: ERel\<^sub>4('a)) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> o"


subsubsection \<open>Operations\<close>

text \<open>As a convenient mathematical abstraction, we introduce the notion of "operation".
In mathematical phraseology, operations are said to "operate" on (one or more) "operands".
Operations can be seen as (curried) functions whose arguments have all the same type.\<close>

text \<open>Unary case: (endo)operations just correspond to (endo)functions.\<close>
type_synonym ('a,'b)Op1 = "'a \<Rightarrow> 'b" ("Op'(_,_')")
type_synonym ('a)EOp1 = "Op('a,'a)" ("EOp'(_')") \<comment> \<open>same as: \<open>'a \<Rightarrow> 'a\<close> \<close>

text \<open>Binary case: (endo)bi-operations correspond to curried (endo)bi-functions.\<close>
type_synonym ('a,'b)Op2 = "'a \<Rightarrow> 'a \<Rightarrow> 'b" ("Op\<^sub>2'(_,_')")
type_synonym ('a)EOp2 = "Op\<^sub>2('a,'a)" ("EOp\<^sub>2'(_')") \<comment> \<open>same as: \<open>'a \<Rightarrow> ('a \<Rightarrow> 'a)\<close>\<close>

text \<open>Arbitrary case: generalized (endo)operations correspond to (endo)functions on sets.\<close>
type_synonym ('a,'b)OpG = "Op(Set('a),'b)" ("Op\<^sub>G'(_,_')")
type_synonym ('a)EOpG = "Op\<^sub>G('a,'a)" ("EOp\<^sub>G'(_')") \<comment> \<open>same as: \<open>Set('a) \<Rightarrow> 'a\<close>\<close>

text \<open>Convenient type aliases for (endo)operations on sets.\<close>
type_synonym ('a,'b)SetOp = "Op(Set('a),Set('b))" ("SetOp'(_,_')")
type_synonym ('a)SetEOp = "SetOp('a,'a)" ("SetEOp'(_')") \<comment> \<open>same as: \<open>Set('a) \<Rightarrow> Set('a)\<close>\<close>

text \<open>Binary case: (endo)bi-operations correspond to curried (endo)bi-functions\<close>
type_synonym ('a,'b)SetOp2 = "Set('a) \<Rightarrow> Set('a) \<Rightarrow> Set('b)" ("SetOp\<^sub>2'(_,_')")
type_synonym ('a)SetEOp2 = "SetOp\<^sub>2('a,'a)" ("SetEOp\<^sub>2'(_')") \<comment> \<open>same as: \<open>Set('a) \<Rightarrow> Set('a) \<Rightarrow> Set('a)\<close>\<close>


subsubsection \<open>Products of Boolean Types\<close>

text \<open>Now consider the following equivalent type notations.\<close>
term "((S :: Set(o)) :: EPair(o)) :: o \<Rightarrow> o"
term "((R :: ERel(o)) :: EOp\<^sub>2(o)) :: o \<Rightarrow> (o \<Rightarrow> o)"
term "(((S :: Space(o)) :: Graph(o)) :: EOp\<^sub>G(o)) :: (o \<Rightarrow> o) \<Rightarrow> o"

text \<open>We can make good sense of them by considering a new type having four inhabitants.\<close>
type_synonym four = "o \<Rightarrow> o" ("oo")
term "((P :: oo) :: EPair(o)) :: Set(o)"

text \<open>Using the new type we can seamlessly define types for (endo)quadruples and 4-valued sets.\<close>
type_synonym ('a)EQuad = "oo \<Rightarrow> 'a" ("EQuad'(_')")
type_synonym ('a)Set4 = "'a \<Rightarrow> oo" ("Set4'(_')")

text \<open>The following two types have each 16 elements (we show a bijection between their elements later on).\<close>
type_synonym sixteen  = "o \<Rightarrow> oo" ("ooo")   \<comment> \<open>\<open>4^2 = (2^2)^2\<close>\<close>
type_synonym sixteen' = "oo \<Rightarrow> o" ("ooo''") \<comment> \<open>\<open>2^4 = 2^(2^2)\<close>\<close>

text \<open>So we can have that the following type notations are in fact identical (not just isomorphic).\<close>
term "(((S :: Set(o)) :: EPair(o)) :: o \<Rightarrow> o) :: oo"
term "(((((R :: ERel(o)) :: EOp\<^sub>2(o)) :: EPair(oo)) :: Set4(o)) :: o \<Rightarrow> o \<Rightarrow> o) :: ooo"
term "((((((S :: Space(o)) :: Graph(o)) :: EOp\<^sub>G(o)) :: Set(oo)) :: EQuad(o)) :: (o \<Rightarrow> o) \<Rightarrow> o) :: ooo'"

text \<open>We can continue producing types (we stop giving them special notation after the magic number 64).\<close>
type_synonym sixtyfour = "oo \<Rightarrow> oo" ("oooo") \<comment> \<open>\<open>4^4 = (2^2)^(2^2) = 64\<close>\<close>
type_synonym n256   = "o \<Rightarrow> ooo" \<comment> \<open>\<open>16^2 = 256\<close>\<close>
type_synonym n65536 = "oo \<Rightarrow> ooo" \<comment> \<open>\<open>16^4 = 65536\<close>\<close>
type_synonym n65536' = "ooo \<Rightarrow> o" \<comment> \<open>\<open>2^16 = 65536\<close>\<close>
type_synonym n4294967296 = "ooo \<Rightarrow> oo" \<comment> \<open>\<open>4^16 = 4294967296\<close>\<close>
\<comment> \<open>and so on...\<close>


text \<open>Continuations (with result type \<open>'r\<close>) take inputs of type \<open>'a\<close>\<close>
text \<open>Unary case:\<close>
type_synonym ('a,'r)Cont1 = "'r-Val(Op('a,'r))" ("Cont'(_,_')") \<comment> \<open>same as: \<open>('a \<Rightarrow> 'r) \<Rightarrow> 'r\<close>\<close>
text \<open>Binary case:\<close>
type_synonym ('a,'r)Cont2 = "'r-Val(Op\<^sub>2('a,'r))" ("Cont\<^sub>2'(_,_')") \<comment> \<open>same as: \<open>('a \<Rightarrow> 'a \<Rightarrow> 'r) \<Rightarrow> 'r\<close>\<close>


subsection \<open>Custom Term Notation\<close>

text \<open>Convenient combinator-like symbols \<open>\<Q>\<close> resp. \<open>\<D>\<close> to be used instead of \<open>(=)\<close> resp. \<open>(\<noteq>)\<close>.\<close>
notation HOL.eq ("\<Q>") and HOL.not_equal ("\<D>")

(*<*)
(* Removes the (=) resp. (\<noteq>) symbols from output (we want to see \<Q>/{_} resp. \<D>/\<lbrace>_\<rbrace> instead) *)
no_notation(output)
  HOL.eq (infix "=" 50) and HOL.not_equal (infix "\<noteq>" 50)
notation (output)
  HOL.eq  ("(_ =/ _)" [51, 51] 50) and HOL.not_equal  ("(_ \<noteq>/ _)" [51, 51] 50)
(*>*)

text \<open>Alternative (more concise) notation for boolean constants.\<close>
notation HOL.True ("\<T>") and HOL.False ("\<F>")

text \<open>Add (binder) notation for indefinite descriptions (aka. Hilbert's epsilon or choice operator).\<close>
notation Hilbert_Choice.Eps ("\<epsilon>") and Hilbert_Choice.Eps (binder "\<epsilon>" 10)

text \<open>Introduce a convenient "dual" to Hilbert's epsilon operator (adds variable-binding notation).\<close>
definition Delta ("\<delta>")
  where "\<delta> \<equiv> \<lambda>A. \<epsilon> (\<lambda>x. \<not>A x)"
notation Delta (binder "\<delta>" 10) 

text \<open>Add (binder) notation for definite descriptions (incl. binder notation).\<close>
notation HOL.The ("\<iota>") and HOL.The (binder "\<iota>" 10)

(*<*)(*Sanity checks*)
lemma "(\<epsilon> x. A x) = (SOME x. A x)" ..
lemma "(\<delta> x. A x) = (SOME x. \<not>A x)" unfolding Delta_def ..
lemma "(\<iota> x. A x) = (THE x. A x)" ..
(*>*)

text \<open>We introduce (pedagogically convenient) notation for HOL logical constants.\<close>
notation HOL.All ("\<forall>") 
notation HOL.Ex  ("\<exists>")
abbreviation Empty ("\<nexists>")
  where "\<nexists>A \<equiv> \<not>\<exists>A"                           

notation HOL.implies (infixr "\<rightarrow>" 25)  \<comment> \<open>convenient alternative notation\<close>
notation HOL.iff (infixr "\<leftrightarrow>" 25) \<comment> \<open>convenient alternative notation\<close>

text \<open>Add convenient logical connectives.\<close>
abbreviation(input) seilpmi (infixl "\<leftarrow>" 25) \<comment> \<open>reversed implication\<close>
  where "A \<leftarrow> B \<equiv> B \<rightarrow> A"
abbreviation(input) excludes (infixl "\<leftharpoondown>" 25) \<comment> \<open>aka. co-implication\<close>
  where "A \<leftharpoondown> B \<equiv> A \<and> \<not>B"
abbreviation(input) sedulcxe (infixr "\<rightharpoonup>" 25) \<comment> \<open>aka. dual-implication\<close>
  where "A \<rightharpoonup> B \<equiv> B \<leftharpoondown> A"
abbreviation(input) xor (infix "\<rightleftharpoons>" 25) \<comment> \<open>aka. symmetric difference\<close>
  where "A \<rightleftharpoons> B \<equiv> A \<noteq> B"
abbreviation(input) nand (infix "\<up>" 35) \<comment> \<open>aka. Sheffer stroke\<close>
  where "A \<up> B \<equiv> \<not>(A \<and> B)"
abbreviation(input) nor (infix "\<down>" 30) \<comment> \<open>aka. Peirce arrow or Quine dagger\<close>
  where "A \<down> B \<equiv> \<not>(A \<or> B)"

text \<open>Check relationships\<close>
lemma disj_impl: "(A \<or> B) = ((A \<rightarrow> B) \<rightarrow> B)" by auto
lemma conj_excl: "(A \<and> B) = ((A \<rightharpoonup> B) \<rightharpoonup> B)" by auto
lemma xor_excl: "(A \<rightleftharpoons> B) = (A \<leftharpoondown> B) \<or> (A \<rightharpoonup> B)" by auto

(*<*)(*Reintroduces notation for negation to allow for conveniently referring to it as '\<not>' *)
notation(input) HOL.Not ("\<not>" 40)
notation(output) HOL.Not ("\<not>_" [40] 40)


subsection \<open>Hiding Symbols and Notation from the Isabelle Library\<close>

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


subsection \<open>Notation Tests\<close>

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

(*>*)

end