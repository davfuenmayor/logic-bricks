theory types (* Notation for type constructors *)
imports Main
begin

section \<open>Type Constructors\<close>

(*The creation of a functional type (starting with a type 'a) can be seen from two complementary 
 perspectives: Valuation (classification) and environmentalization (contextualization/indexation)*)
type_synonym ('v,'a)Val = "'a \<Rightarrow> 'v" ("_-Val'(_')" [1000])
type_synonym ('e,'a)Env = "'e \<Rightarrow> 'a" ("_-Env'(_')" [1000])


subsection \<open>Sets and Relations\<close>

(*Notation aliasing for type bool*)
type_notation bool ("o") 

(*Sets and pairs as unary type constructors*)
type_synonym ('a)Set = "o-Val('a)" ("Set'(_')")  (*a set is encoded as a 2-valuation (boolean classifier)*)
type_synonym ('a)Pair = "o-Env('a)" ("Pair'(_')")  (*a pair is encoded as a 2-index *)

term "(S :: Set('a)) :: 'a \<Rightarrow> o"
term "(P :: Pair('a)) :: o \<Rightarrow> 'a"

(*(Endo)relations between objects (of the same type) as binary type constructors *)
type_synonym ('a,'b)Rel = "Set('b)-Val('a)" ("Rel'(_,_')") (*relations encoded as set-valued functions*)
type_synonym ('a)ERel = "Rel('a,'a)" ("ERel'(_')") (*endorelations are a special case*)

term "(R :: Rel('a,'b)) :: 'a-Env(Set('b))" (*relations can also be seen as indexed families of sets*)

term "(R :: Rel('a,'b)) :: 'a \<Rightarrow> 'b \<Rightarrow> o"
term "(R :: ERel('a)) :: 'a \<Rightarrow> 'a \<Rightarrow> o"


subsection \<open>Operations\<close>

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


end