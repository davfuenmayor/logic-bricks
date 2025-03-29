section \<open>Functions and Sets\<close>
text \<open>We introduce several convenient definitions and lemmata for working with functions and sets.\<close>

theory func_sets (* A basic theory of sets and functions*)
imports connectives
begin

named_theorems func_defs

subsection \<open>Basic Functional Notions\<close>

subsubsection \<open>Monoid Structure\<close>

text \<open>Functions feature a monoidal structure. The identity function is a nullary operation 
 (i.e. a "constant"). It corresponds to the \<open>\<^bold>I\<close> combinator. Function composition is the main binary
  operation between functions and corresponds to the \<open>\<^bold>B\<close> combinator.\<close>

\<comment> \<open>Recalling\<close>
lemma "f \<circ> g \<circ> h = (\<lambda>x. f (g (h x)))" unfolding comb_defs ..
lemma "f ; g ; h = (\<lambda>x. h( g (f x)))" unfolding comb_defs ..

text \<open>Composition and identity satisfy the monoid conditions.\<close>
lemma "(f \<circ> g) \<circ> h = f \<circ> (g \<circ> h)" unfolding comb_defs ..    \<comment> \<open>associativity\<close>
lemma "\<^bold>I \<circ> f = f" unfolding comb_defs ..                   \<comment> \<open>identity 1\<close>
lemma "f \<circ> \<^bold>I = f" unfolding comb_defs ..                   \<comment> \<open>identity 2\<close>


subsubsection \<open>Fixed-Points\<close>

text \<open>The set of pre- resp. post-fixed-points of an endofunction \<open>f\<close> wrt an endorelation \<open>R\<close>, are those points
 sent by \<open>f\<close> backwards resp. forward wrt \<open>R\<close>. Note that if \<open>R\<close> is symmetric then both notions coincide.\<close>
definition preFixedPoint::"ERel('a) \<Rightarrow> EOp('a) \<Rightarrow> Set('a)" ("_-preFP")
  where "preFixedPoint \<equiv> \<^bold>\<Sigma>"
definition postFixedPoint::"ERel('a) \<Rightarrow> EOp('a) \<Rightarrow> Set('a)" ("_-postFP")
  where "postFixedPoint \<equiv> \<^bold>S"

declare preFixedPoint_def[func_defs] postFixedPoint_def[func_defs]

lemma "R-preFP f = (\<lambda>A. R (f A) A)" unfolding func_defs comb_defs ..
lemma "R-postFP f = (\<lambda>A. R A (f A))" unfolding func_defs comb_defs ..

text \<open>The set of weak pre-/post-fixed-points of endooperation wrt. an endorelation.\<close>
definition weakPreFixedPoint::"ERel('a) \<Rightarrow> EOp('a) \<Rightarrow> Set('a)" ("_-wPreFP")
  where "weakPreFixedPoint  \<equiv> \<^bold>L \<^bold>\<Phi>\<^sub>2\<^sub>2 (\<^bold>W \<^bold>B) \<^bold>A"
definition weakPostFixedPoint::"ERel('a) \<Rightarrow> EOp('a) \<Rightarrow> Set('a)" ("_-wPostFP")
  where "weakPostFixedPoint \<equiv> \<^bold>L \<^bold>\<Phi>\<^sub>2\<^sub>2 \<^bold>A (\<^bold>W \<^bold>B)"

declare weakPreFixedPoint_def[func_defs] weakPostFixedPoint_def[func_defs]

lemma "R-wPreFP \<phi> = (\<lambda>A. R (\<phi>(\<phi> A)) (\<phi> A))" unfolding func_defs comb_defs ..
lemma "R-wPostFP \<phi> = (\<lambda>A. R (\<phi> A) (\<phi> (\<phi> A)))" unfolding func_defs comb_defs ..


text \<open>The (non-)fixed-points of an endofunction are just the pre/post-fixed points wrt (dis)equality.\<close>
definition fixedPoint::"('a \<Rightarrow> 'a) \<Rightarrow> Set('a)" ("FP")
  where "FP  \<equiv> \<Q>-postFP"
definition nonFixedPoint::"('a \<Rightarrow> 'a) \<Rightarrow> Set('a)" ("nFP")
  where "nFP \<equiv> \<D>-postFP"

declare fixedPoint_def[func_defs] nonFixedPoint_def[func_defs]

lemma "FP f x = (x = f x)" unfolding func_defs comb_defs ..
lemma "nFP f x = (x \<noteq> f x)" unfolding func_defs comb_defs ..

lemma fixedPoint_defT: "FP = \<Q>-preFP" unfolding func_defs comb_defs by metis
lemma nonFixedPoint_defT: "nFP = \<D>-preFP" unfolding func_defs comb_defs by metis


text \<open>An endooperation can be said to be (weakly) expansive resp. contractive wrt an endorelation
 when all of its points are (weak) pre-fixed-points resp. (weak) post-fixed-points.\<close>
definition expansive::"ERel('a) \<Rightarrow> Set(EOp('a))" ("_-EXPN")
  where "R-EXPN \<equiv> \<forall> \<circ> R-postFP"
definition contractive::"ERel('a) \<Rightarrow> Set(EOp('a))" ("_-CNTR")
  where "R-CNTR \<equiv> \<forall> \<circ> R-preFP"
definition weaklyExpansive::"ERel('a) \<Rightarrow> Set(EOp('a))" ("_-wEXPN")
  where "R-wEXPN \<equiv> \<forall> \<circ> R-wPostFP"
definition weaklyContractive::"ERel('a) \<Rightarrow> Set(EOp('a))" ("_-wCNTR")
  where "R-wCNTR \<equiv> \<forall> \<circ> R-wPreFP"

declare expansive_def[func_defs] contractive_def[func_defs] 
        weaklyExpansive_def[func_defs] weaklyContractive_def[func_defs]

lemma "R-EXPN f = (\<forall>A. R A (f A))" unfolding func_defs comb_defs ..
lemma "R-CNTR f = (\<forall>A. R (f A) A)" unfolding func_defs comb_defs ..
lemma "R-wEXPN f = (\<forall>A. R (f A) (f (f A)))" unfolding func_defs comb_defs ..
lemma "R-wCNTR f = (\<forall>A. R (f (f A)) (f A))" unfolding func_defs comb_defs ..


subsubsection \<open>Type-lifting - General Case: Environment (aka. Reader) Monad\<close>

text \<open>We can conceive of functional types of the form \<open>'a \<Rightarrow> 'b\<close> as arising via an "environmentalization", 
 or "indexation" of the type \<open>'b\<close> by the type \<open>'a\<close>, i.e. as \<open>'a-Env('b)\<close> using our type notation. 
 This type constructor comes with a monad structure (and is thus an applicative and a functor too).\<close>
abbreviation(input) unit_env::"'a \<Rightarrow> 'e-Env('a)"
  where "unit_env  \<equiv> \<^bold>K"
abbreviation(input) fmap_env::"('a \<Rightarrow> 'b) \<Rightarrow> 'e-Env('a) \<Rightarrow> 'e-Env('b)"
  where "fmap_env  \<equiv> \<^bold>B"
abbreviation(input) join_env::"'e-Env('e-Env('a)) \<Rightarrow> 'e-Env('a)"
  where "join_env  \<equiv> \<^bold>W"
abbreviation(input) ap_env::"'e-Env('a \<Rightarrow> 'b) \<Rightarrow> 'e-Env('a) \<Rightarrow> 'e-Env('b)"
  where "ap_env    \<equiv> \<^bold>S"
abbreviation(input) rbind_env::"('a \<Rightarrow> 'e-Env('b)) \<Rightarrow> 'e-Env('a) \<Rightarrow> 'e-Env('b)"
  where "rbind_env \<equiv> \<^bold>\<Sigma>" \<comment> \<open>reversed-bind\<close>

text \<open>We define the customary bind operation as "flipped" rbind (which seems more intuitive).\<close>
abbreviation(input) bind_env::"'e-Env('a) \<Rightarrow> ('a \<Rightarrow> 'e-Env('b)) \<Rightarrow> 'e-Env('b)"
  where "bind_env \<equiv> \<^bold>C rbind_env"
text \<open>But we could have also given it a direct alternative definition.\<close>
lemma "bind_env = \<^bold>W \<circ>\<^sub>2 (\<^bold>C \<^bold>B)" unfolding comb_defs ..

text \<open>Some properties of monads in general\<close>
lemma "rbind_env = join_env \<circ>\<^sub>2 fmap_env" unfolding comb_defs ..
lemma "join_env = rbind_env \<^bold>I" unfolding comb_defs ..
\<comment> \<open>...and so on\<close>

text \<open>Some properties of this particular monad\<close>
lemma "ap_env = rbind_env \<circ> \<^bold>C" unfolding comb_defs ..
\<comment> \<open>...and so on\<close>

text \<open>The so-called "monad laws". They guarantee that monad-related term operations compose reliably.\<close>
abbreviation(input) "monadLaw1 unit bind \<equiv> \<forall>f a. (bind (unit a) f) = (f a)" \<comment> \<open>left identity\<close>
abbreviation(input) "monadLaw2 unit bind \<equiv> \<forall>A. (bind A unit) = A" \<comment> \<open>right identity\<close>
abbreviation(input) "monadLaw3  bind \<equiv> \<forall>A f g. (bind A (\<lambda>a. bind (f a) g)) = bind (bind A f) g" \<comment> \<open>associativity\<close>

text \<open>Verifies compliance with the monad laws.\<close>
lemma "monadLaw1 unit_env bind_env" unfolding comb_defs by simp
lemma "monadLaw2 unit_env bind_env" unfolding comb_defs by simp
lemma "monadLaw3 bind_env" unfolding comb_defs by simp


subsubsection \<open>Type-lifting - Digression: On Higher Arities\<close>

text \<open>Note that \<open>\<^bold>\<Phi>\<^sub>m\<^sub>n\<close> combinators can be used to index (or "environmentalize") a given m-ary function n-times.\<close>
term "(\<^bold>\<Phi>\<^sub>0\<^sub>1 (f::'a)) :: 'e-Env('a)"
term "(\<^bold>\<Phi>\<^sub>1\<^sub>1 (f::'a \<Rightarrow> 'b)) :: 'e-Env('a) \<Rightarrow> 'e-Env('b)"
term "(\<^bold>\<Phi>\<^sub>1\<^sub>2 (f::'a \<Rightarrow> 'b)) :: 'e\<^sub>2-Env('e\<^sub>1-Env('a)) \<Rightarrow> 'e\<^sub>2-Env('e\<^sub>1-Env('b))"
\<comment> \<open>...and so on\<close>
term "(\<^bold>\<Phi>\<^sub>2\<^sub>1 (g::'a \<Rightarrow> 'b \<Rightarrow> 'c)) :: 'e-Env('a) \<Rightarrow> 'e-Env('b) \<Rightarrow> 'e-Env('c)"
term "(\<^bold>\<Phi>\<^sub>2\<^sub>2 (g::'a \<Rightarrow> 'b \<Rightarrow> 'c)) :: 'e\<^sub>2-Env('e\<^sub>1-Env('a)) \<Rightarrow> 'e\<^sub>2-Env('e\<^sub>1-Env('b)) \<Rightarrow> 'e\<^sub>2-Env('e\<^sub>1-Env('c))"
\<comment> \<open>...and so on\<close>

text \<open>Hence the \<open>\<^bold>\<Phi>\<^sub>m\<^sub>n\<close> combinators can play the role of (n-times iterated) functorial "lifters".\<close>
lemma "(unit_env::'a \<Rightarrow> 'e-Env('a)) = \<^bold>\<Phi>\<^sub>0\<^sub>1" unfolding comb_defs .. 
lemma "(fmap_env::('a \<Rightarrow> 'b) \<Rightarrow> ('e-Env('a) \<Rightarrow> 'e-Env('b))) = \<^bold>\<Phi>\<^sub>1\<^sub>1" unfolding comb_defs ..
abbreviation(input) fmap2_env::"('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('e-Env('a) \<Rightarrow> 'e-Env('b) \<Rightarrow> 'e-Env('c))"
  where "fmap2_env \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1" \<comment> \<open>cf. Haskell's \<open>liftA2\<close>\<close>
\<comment> \<open>...and so on\<close>

text \<open>In the same spirit, we can employ the combinator families \<open>\<^bold>S\<^sub>m\<^sub>n\<close> resp. \<open>\<^bold>\<Sigma>\<^sub>m\<^sub>n\<close> as (n-times iterated) 
 m-ary applicative resp. monadic "lifters".\<close>
abbreviation(input) ap2_env::"'e-Env('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('e-Env('a) \<Rightarrow> 'e-Env('b) \<Rightarrow> 'e-Env('c))"
  where "ap2_env    \<equiv> \<^bold>S\<^sub>2\<^sub>1"
abbreviation(input) rbind2_env::"('a \<Rightarrow> 'b \<Rightarrow> 'e-Env('c)) \<Rightarrow> ('e-Env('a) \<Rightarrow> 'e-Env('b) \<Rightarrow> 'e-Env('c))"
  where "rbind2_env  \<equiv> \<^bold>\<Sigma>\<^sub>2\<^sub>1"
\<comment> \<open>...and so on\<close>

subsubsection \<open>Type-lifting - Base Case: Identity Monad\<close>

text \<open>Finally, we consider the (degenerate) base case arising from an identity type constructor\<close>
abbreviation(input) unit_id::"'a \<Rightarrow> 'a"
  where "unit_id \<equiv> \<^bold>I"
abbreviation(input) fmap_id::"('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"
  where "fmap_id \<equiv> \<^bold>A"
abbreviation(input) fmap2_id::"('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'b)"
  where "fmap2_id \<equiv> \<^bold>A\<^sub>2"
abbreviation(input) join_id::"'a \<Rightarrow> 'a"
  where "join_id \<equiv> \<^bold>I"
abbreviation(input) ap_id::"('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"
  where "ap_id \<equiv> \<^bold>A"
abbreviation(input) rbind_id::"('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"
  where "rbind_id \<equiv> \<^bold>A"
abbreviation(input) bind_id::"'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b"
  where "bind_id \<equiv> \<^bold>T"

lemma "monadLaw1 unit_id bind_id" unfolding comb_defs by simp
lemma "monadLaw2 unit_id bind_id" unfolding comb_defs by simp
lemma "monadLaw3 bind_id" unfolding comb_defs by simp


subsubsection \<open>Type-lifting - Relations\<close>

text \<open>Relations can be seen (and thus type-lifted) from two equivalent perspectives: 
 \<^enum> As unary functions (with set codomain), or equivalently, as indexed families of sets.
 \<^enum> As binary functions (with a boolean codomain).\<close>
term "(R :: Rel('a,'b)) :: 'a-Env(Set('b))"
term "(R :: Rel('a,'b)) :: 'a \<Rightarrow> 'b \<Rightarrow> o"

text \<open>Note that when "lifting" relations as binary functions (via \<open>\<^bold>\<Phi>\<^sub>2\<^sub>1\<close>) what we obtain is not quite a relation.\<close>
term "\<^bold>\<Phi>\<^sub>2\<^sub>1 (R :: Rel('a,'b)) :: 'e-Env('a) \<Rightarrow> 'e-Env('b) \<Rightarrow> Set('e)"

text \<open>We introduce two convenient ways to lift a given relation to obtain its "indexed" counterpart.\<close>
definition relLiftEx :: "Rel('a,'b) \<Rightarrow> Rel('c-Env('a),'c-Env('b))" ("\<^bold>\<Phi>\<^sub>\<exists>")  \<comment> \<open>existential lifting\<close>
  where "\<^bold>\<Phi>\<^sub>\<exists> \<equiv> \<exists> \<circ>\<^sub>3 \<^bold>\<Phi>\<^sub>2\<^sub>1" 
definition relLiftAll :: "Rel('a,'b) \<Rightarrow> Rel('c-Env('a),'c-Env('b))" ("\<^bold>\<Phi>\<^sub>\<forall>") \<comment> \<open>universal lifting\<close>
  where "\<^bold>\<Phi>\<^sub>\<forall> \<equiv> \<forall> \<circ>\<^sub>3 \<^bold>\<Phi>\<^sub>2\<^sub>1"

declare relLiftEx_def[func_defs] relLiftAll_def[func_defs]


subsection \<open>Basic Set Notions\<close>

subsubsection \<open>Set-Operations\<close>

text \<open>Note that sets of As can be faithfully encoded as A-indexed booleans (aka. "characteristic functions").\<close>
term "(S :: Set('a)) :: 'a-Env(o)"

text \<open>Thus the usual set operations arise via "indexation" of HOL's boolean connectives (via \<open>\<^bold>\<Phi>\<^sub>m\<^sub>1\<close> combinators). 
 This explains, among others, why sets come with a Boolean algebra structure (cf. Stone representation).\<close>
definition universe::"Set('a)" ("\<UU>")
  where "\<UU> \<equiv> \<^bold>\<Phi>\<^sub>0\<^sub>1 \<T>" \<comment> \<open>the universal set: the nullary connective/constant \<open>\<T>\<close> lifted once\<close>
definition emptyset::"Set('a)" ("\<emptyset>")
  where "\<emptyset> \<equiv> \<^bold>\<Phi>\<^sub>0\<^sub>1 \<F>" \<comment> \<open>the empty set: the nullary connective/constant \<open>\<F>\<close> lifted once\<close>
definition compl::"EOp(Set('a))" ("\<midarrow>")
  where \<open>\<midarrow> \<equiv> \<^bold>\<Phi>\<^sub>1\<^sub>1(\<not>)\<close> text \<open>set complement: the unary \<open>\<not>\<close> connective lifted once\<close>
definition inter::"EOp\<^sub>2(Set('a))" (infixr "\<inter>" 54) 
  where "(\<inter>) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1(\<and>)" \<comment> \<open>set intersection: the binary \<open>\<and>\<close> connective lifted once\<close>
definition union::"EOp\<^sub>2(Set('a))" (infixr "\<union>" 53) 
  where "(\<union>) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1(\<or>)" \<comment> \<open>set union\<close>
definition diff::"EOp\<^sub>2(Set('a))" (infixl "\<setminus>" 51) 
  where "(\<setminus>) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1(\<leftharpoondown>)" \<comment> \<open>set difference\<close>
definition impl::"EOp\<^sub>2(Set('a))" (infixr "\<Rightarrow>" 51) 
  where "(\<Rightarrow>) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1(\<rightarrow>)" \<comment> \<open>set implication\<close>
definition dimpl::"EOp\<^sub>2(Set('a))" (infix "\<Leftrightarrow>" 51) 
  where "(\<Leftrightarrow>) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1(\<leftrightarrow>)" \<comment> \<open>set double-implication\<close>
definition sdiff::"EOp\<^sub>2(Set('a))" (infix "\<triangle>" 51) 
  where "(\<triangle>) \<equiv>  \<^bold>\<Phi>\<^sub>2\<^sub>1(\<rightleftharpoons>)" \<comment> \<open>set symmetric-difference (aka. xor)\<close>

text \<open>Reversed implication as convenient syntactic sugar.\<close>
abbreviation(input) lpmi::"EOp\<^sub>2(Set('a))" (infixl "\<Leftarrow>" 51)
  where "A \<Leftarrow> B \<equiv> B \<Rightarrow> A"

declare universe_def[func_defs] emptyset_def[func_defs] 
        compl_def[func_defs] inter_def[func_defs] union_def[func_defs]
        impl_def[func_defs] dimpl_def[func_defs] diff_def[func_defs] sdiff_def[func_defs] 

text \<open>Double-check point-based definitions.\<close>
lemma "\<UU> = (\<lambda>x. \<T>)" unfolding func_defs comb_defs ..
lemma "\<emptyset> = (\<lambda>x. \<F>)" unfolding func_defs comb_defs ..
lemma "\<midarrow>A = (\<lambda>x. \<not>A x)" unfolding func_defs comb_defs ..
lemma "A \<inter> B = (\<lambda>x. A x \<and> B x)" unfolding func_defs comb_defs ..
lemma "A \<union> B = (\<lambda>x. A x \<or> B x)" unfolding func_defs comb_defs ..
lemma "A \<setminus> B = (\<lambda>x. A x \<leftharpoondown> B x)" unfolding func_defs comb_defs ..
lemma "A \<Rightarrow> B = (\<lambda>x. A x \<rightarrow> B x)" unfolding func_defs comb_defs ..
lemma "A \<Leftarrow> B = (\<lambda>x. A x \<leftarrow> B x)" unfolding func_defs comb_defs ..
lemma "A \<Leftrightarrow> B = (\<lambda>x. A x \<leftrightarrow> B x)" unfolding func_defs comb_defs ..
lemma "A \<triangle> B = (\<lambda>x. A x \<rightleftharpoons> B x)" unfolding func_defs comb_defs ..

text \<open>Double-check some well known properties.\<close>
lemma compl_involutive: "\<midarrow>(\<midarrow>S) = S" unfolding func_defs comb_defs by simp
lemma compl_deMorgan1: "\<midarrow>(\<midarrow>A \<union> \<midarrow>B) = (A \<inter> B)" unfolding func_defs comb_defs by simp
lemma compl_deMorgan2: "\<midarrow>(\<midarrow>A \<inter> \<midarrow>B) = (A \<union> B)" unfolding func_defs comb_defs by simp
lemma compl_fixedpoint: "nFP = \<midarrow> \<circ> FP" unfolding func_defs comb_defs ..
lemma "nFP f = \<midarrow>(FP f)" unfolding func_defs comb_defs ..


subsubsection \<open>Dual-composition of Unary Set-Operations\<close>

text \<open>Clearly, functional composition can be seamlessly applied to set-operations too.\<close>
lemma fixes F::"Set('b) \<Rightarrow> Set('c)" and G::"Set('a) \<Rightarrow> Set('b)"
  shows "F \<circ> G = (\<lambda>x. F (G x))" unfolding comb_defs ..

text \<open>Moreover, we can conveniently introduce a dual for the (functional) composition of set-operations.\<close>
definition compDual::"SetOp('a,'b) \<Rightarrow> SetOp('c,'a) \<Rightarrow> SetOp('c,'b)" (infixl "\<bullet>" 55)
  where "(\<bullet>) \<equiv> \<lambda>f g. \<lambda>x. f (\<midarrow>(g x))"
abbreviation(input) compDual_t (infixr ":" 55)
  where "f : g \<equiv> g \<bullet> f"

declare compDual_def[func_defs]

lemma compDuality1: "(f \<bullet> g) = \<midarrow> \<circ> ((\<midarrow> \<circ> f) \<circ> (\<midarrow> \<circ> g))" 
  unfolding func_defs comb_defs by simp
lemma compDuality2: "(f \<bullet> g) = (f \<circ> (\<midarrow> \<circ> g))" 
  unfolding func_defs comb_defs by simp
lemma compDuality3: "(f \<circ> g) = (f \<bullet> (\<midarrow> \<circ> g))" 
  unfolding func_defs comb_defs by simp


subsubsection \<open>Set Orderings\<close>

text \<open>In the previous section we applied a kind of "functional lifting" to the boolean HOL operations in
 order to encode the corresponding operations on sets. Here we encode sets' (lattice) order structure
 via a "relational lifting" of the ordering of HOL's truth-values.\<close>

text \<open>We start by noting that HOL's binary boolean operations can also be seen as (endo)relations.\<close>
term "(\<and>) :: ERel(o)"
term "(\<or>) :: ERel(o)"
term "(\<rightarrow>) :: ERel(o)" \<comment> \<open>the customary ordering on truth-values (where \<open>\<F> \<rightarrow> \<T>\<close>)\<close>

text \<open>The algebra of sets is thus naturally ordered via the subset endorelation (via 'relational lifting').\<close>
definition subset::"ERel(Set('a))" (infixr "\<subseteq>" 51) 
  where "(\<subseteq>) \<equiv> \<^bold>\<Phi>\<^sub>\<forall> (\<rightarrow>)"

declare subset_def[func_defs]

lemma "A \<subseteq> B = (\<forall>x. A x \<rightarrow> B x)" unfolding func_defs comb_defs ..
lemma "A \<subseteq> B = \<forall>(A \<Rightarrow> B)" unfolding func_defs comb_defs ..

lemma subset_setdef:   "(\<subseteq>) = \<forall> \<circ>\<^sub>2 (\<Rightarrow>)" unfolding func_defs comb_defs ..

abbreviation(input) superset::"ERel(Set('a))" (infixr "\<supseteq>" 51)
  where "B \<supseteq> A \<equiv> A \<subseteq> B"

text \<open>The powerset operation corresponds in fact to (partial application of) superset relation.\<close>
abbreviation(input) powerset::"Set('a) \<Rightarrow> Set(Set('a))" ("\<wp>")
  where "\<wp> \<equiv> (\<supseteq>)"

lemma "\<wp>A = (\<lambda>B. B \<subseteq> A)" unfolding func_defs comb_defs by auto

text \<open>Alternative characterizations of the sub/super-set orderings in terms of fixed-points.\<close>
lemma subset_defFP:   "(\<subseteq>) = FP \<circ> (\<union>)" unfolding func_defs comb_defs by metis
lemma superset_defFP: "(\<supseteq>) = FP \<circ> (\<inter>)" unfolding func_defs comb_defs by metis
lemma "(A \<subseteq> B) = (B = A \<union> B)" unfolding func_defs comb_defs by metis
lemma "(B \<supseteq> A) = (A = B \<inter> A)" unfolding func_defs comb_defs by metis

text \<open>Subset is antisymmetric.\<close>
lemma subset_antisym: "R \<subseteq> T \<Longrightarrow> R \<supseteq> T \<Longrightarrow> R = T" unfolding func_defs comb_defs by auto

text \<open>In the same spirit, we conveniently provide the following related endorelations:\<close>

text \<open>Two sets are said to "overlap" (or "intersect") if their intersection is non-empty.\<close>
definition overlap::"ERel(Set('a))" (infix "\<sqinter>" 52)
  where "(\<sqinter>) \<equiv> \<^bold>\<Phi>\<^sub>\<exists> (\<and>)"
text \<open>dually, two sets form a "cover" if every element belongs to one or the other.\<close>
definition cover::"ERel(Set('a))" (infix "\<squnion>" 53)
  where "(\<squnion>) \<equiv> \<^bold>\<Phi>\<^sub>\<forall> (\<or>)"

declare overlap_def[func_defs] cover_def[func_defs] 

text \<open>Convenient notation: Two sets are said to be "incompatible" if they don't overlap.\<close>
abbreviation(input) incompat::"ERel(Set('a))" (infix "\<bottom>" 52)
  where "(\<bottom>) \<equiv> (\<not>) \<circ>\<^sub>2 (\<sqinter>)"

lemma cover_setdef:   "(\<squnion>) = \<forall> \<circ>\<^sub>2 (\<union>)" unfolding func_defs comb_defs ..
lemma overlap_setdef: "(\<sqinter>) = \<exists> \<circ>\<^sub>2 (\<inter>)" unfolding func_defs comb_defs ..
lemma "A \<squnion> B = \<forall>(A \<union> B)" unfolding func_defs comb_defs ..
lemma "A \<sqinter> B = \<exists>(A \<inter> B)" unfolding func_defs comb_defs ..
lemma "A \<bottom> B = \<nexists>(A \<inter> B)" unfolding func_defs comb_defs ..

text \<open>Subset, overlap and cover are interrelated as expected.\<close>
lemma "A \<subseteq> B = \<midarrow>A \<squnion> B" unfolding func_defs comb_defs by simp
lemma "A \<subseteq> B = A \<bottom> \<midarrow>B" unfolding func_defs comb_defs by simp
lemma "\<not>(A \<subseteq> B) = A \<sqinter> \<midarrow>B" unfolding func_defs comb_defs by simp
lemma "\<not>(A \<subseteq> B) = A \<sqinter> \<midarrow>B" unfolding func_defs comb_defs by simp
lemma "A \<squnion> B = \<midarrow>A \<subseteq> B" unfolding func_defs comb_defs by auto
lemma "A \<sqinter> B = (\<not>(A \<subseteq> \<midarrow>B))" unfolding func_defs comb_defs by simp
lemma "A \<bottom> B = A \<subseteq> \<midarrow>B" unfolding func_defs comb_defs by simp


subsubsection \<open>Constructing Sets\<close>

abbreviation(input) insert :: "'a \<Rightarrow> Set('a) \<Rightarrow> Set('a)"
  where "insert a S \<equiv> \<Q> a \<union> S"
abbreviation(input) remove :: "'a \<Rightarrow> Set('a) \<Rightarrow> Set('a)"
  where "remove a S \<equiv> \<D> a \<inter> S"

text \<open>The previous functions in terms of combinators.\<close>
lemma "insert = \<^bold>C (\<^bold>B\<^sub>1\<^sub>0 (\<union>) \<Q>)" unfolding comb_defs ..
lemma "remove = \<^bold>C (\<^bold>B\<^sub>1\<^sub>0 (\<inter>) \<D>)" unfolding comb_defs ..

syntax
  "_finiteSet" :: "args \<Rightarrow> Set('a)"   ("{(_)}")
  "_finiteCoset" :: "args \<Rightarrow> Set('a)" ("\<lbrace>(_)\<rbrace>")
translations
  "{x, xs}" \<rightleftharpoons> "CONST insert x (_finiteSet xs)"
  "\<lbrace>x, xs\<rbrace>" \<rightleftharpoons> "CONST remove x (_finiteCoset xs)"
  "{x}" \<rightharpoonup> "\<Q> x"  \<comment> \<open>aka. "singleton"\<close>
  "\<lbrace>x\<rbrace>" \<rightharpoonup> "\<D> x"  \<comment> \<open>aka. "cosingleton")\<close>

text \<open>Some syntax checks.\<close>
lemma "{a} = \<Q> a" ..
lemma "{a,b} = {a} \<union> {b}" ..
lemma "{a,b,c} = {a} \<union> {b,c}" ..
lemma "{a,b,c} = {a} \<union> {b} \<union> {c}" ..
lemma "\<lbrace>a\<rbrace> = \<D> a" ..
lemma "\<lbrace>a,b\<rbrace> = \<lbrace>a\<rbrace> \<inter> \<lbrace>b\<rbrace>" ..
lemma "\<lbrace>a,b,c\<rbrace> = \<lbrace>a\<rbrace> \<inter> \<lbrace>b,c\<rbrace>" ..
lemma "\<lbrace>a,b,c\<rbrace> = \<lbrace>a\<rbrace> \<inter> \<lbrace>b\<rbrace> \<inter> \<lbrace>c\<rbrace>" ..
lemma "\<lbrace>{a,b,c}, {d,e}\<rbrace> = \<lbrace>{a} \<union> {b} \<union> {c}\<rbrace> \<inter> \<lbrace>{d} \<union> {e}\<rbrace>" ..

text \<open>Sets and cosets are related via set-complement as expected.\<close>
lemma "\<lbrace>a\<rbrace> = \<midarrow>{a}" 
  unfolding func_defs comb_defs ..
lemma "\<lbrace>a,b\<rbrace> = \<midarrow>{a,b}" 
  unfolding func_defs comb_defs by simp
lemma "\<lbrace>a,b,c\<rbrace> = \<midarrow>{a,b,c}" 
  unfolding func_defs comb_defs by simp

text \<open>HOL quantifiers can be seen as sets of sets (or equivalently as "properties" of sets).\<close>
term "\<forall>::Set(Set('a))" \<comment> \<open>\<open>\<forall>A\<close> means that the set A contains all elements\<close>
term "\<exists>::Set(Set('a))" \<comment> \<open>\<open>\<exists>A\<close> means that A contains at least one element, i.e. A is nonempty\<close>
term "\<nexists>::Set(Set('a))" \<comment> \<open>\<open>\<exists>A\<close> means that A is empty\<close>

text \<open>We conveniently add a couple more.\<close>
definition unique::"Set(Set('a))" 
  where \<open>unique A \<equiv> \<forall>x y. A x \<and> A y \<rightarrow> x = y\<close> \<comment> \<open>A contains at most one element (it may be empty)\<close>
definition singleton::"Set(Set('a))" ("\<exists>!") 
  where \<open>\<exists>!A \<equiv> \<exists>x. A x \<and> (\<forall>y. A y \<rightarrow> x = y)\<close>  \<comment> \<open>A contains exactly one element\<close>

declare unique_def[func_defs] singleton_def[func_defs]


subsubsection \<open>Infinitary Set-Operations\<close>

text \<open>Union and intersection can be generalized to operate on arbitrary sets of sets (aka. "infinitary" operations).\<close>
definition biginter::"EOp\<^sub>G(Set('a))" ("\<Inter>")
  where "\<Inter> \<equiv> \<forall> \<circ>\<^sub>2 (\<^bold>B\<^sub>1\<^sub>1 (\<Rightarrow>) \<^bold>I \<^bold>T)"
definition bigunion::"EOp\<^sub>G(Set('a))" ("\<Union>")
  where "\<Union> \<equiv> \<exists> \<circ>\<^sub>2 (\<^bold>B\<^sub>1\<^sub>1 (\<inter>) \<^bold>I \<^bold>T)"

lemma "\<Inter>S x = (\<forall>A. S A \<rightarrow> A x)" unfolding biginter_def func_defs comb_defs ..
lemma "\<Union>S x = (\<exists>A. S A \<and> A x)" unfolding bigunion_def func_defs comb_defs ..

declare biginter_def[func_defs] bigunion_def[func_defs]


text \<open>We say of a set of sets that it "overlaps" (or "intersects") if there exists a shared element.\<close>
abbreviation(input) bigoverlap::"Set(Set(Set('a)))" ("\<Sqinter>")
  where "\<Sqinter> \<equiv> \<exists> \<circ> \<Inter>"
text \<open>Dually, a set of sets forms a "cover" if every element is contained in at least one of the sets.\<close>
abbreviation(input) bigcover::"Set(Set(Set('a)))" ("\<Squnion>")
  where "\<Squnion> \<equiv> \<forall> \<circ> \<Union>"

lemma "\<Sqinter>S = \<exists>(\<Inter>S)" unfolding func_defs comb_defs ..
lemma "\<Squnion>S = \<forall>(\<Union>S)" unfolding func_defs comb_defs ..


subsection \<open>Function Transformations\<close>

subsubsection \<open>Inverse and Range\<close>

text \<open>The inverse of a function \<open>f\<close> is the relation that assigns to each object \<open>b\<close> in its codomain 
 the set of elements in its domain mapped to \<open>b\<close> (i.e. the preimage of \<open>b\<close> under \<open>f\<close>).\<close>
definition inverse::"('a \<Rightarrow> 'b) \<Rightarrow> Rel('b,'a)"
  where "inverse \<equiv> \<^bold>B\<^sub>1\<^sub>0 \<Q>"

lemma "inverse f b = (\<lambda>a. f a = b)" unfolding inverse_def comb_defs ..

declare inverse_def[func_defs]

text \<open>An alternative combinator-based definition (by commutativity of \<open>\<Q>\<close>).\<close>
lemma inverse_def2: "inverse = \<^bold>C (\<^bold>D \<Q>)" unfolding func_defs comb_defs by auto

text \<open>We introduce some convenient superscript notation.\<close>
notation(input) inverse ("_\<inverse>")  notation(output) inverse ("'(_')\<inverse>")

text \<open>The related notion of inverse-function of a (bijective) function can be written as:\<close>
term "(\<iota> \<circ> f\<inverse>) ::('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)" \<comment> \<open>Beware: well-behaved for bijective functions only!\<close>

text \<open>Given a function \<open>f\<close> we can obtain its range as the set of those objects \<open>b\<close> in the codomain that 
 are the image of some object \<open>a\<close> (i.e. have a non-empty preimage) under the function \<open>f\<close>.\<close>
definition range::"('a \<Rightarrow> 'b) \<Rightarrow> Set('b)"
  where "range \<equiv> \<exists> \<circ>\<^sub>2 inverse"

declare range_def[func_defs]

lemma "range f = \<exists> \<circ> f\<inverse>" unfolding func_defs comb_defs ..
lemma "range f b = (\<exists>a. f a = b)" unfolding func_defs comb_defs ..


text \<open>More generally, the inverse of an n-ary function \<open>f\<close> is the n+1-ary relation that relates to each 
 object \<open>c\<close> in f's codomain those ("curried" tuples of) elements in the domain are become mapped to \<open>c\<close>
 under \<open>f\<close> (i.e. the "preimage" of \<open>c\<close> under \<open>f\<close>). We use this to define the range of an n-ary function too.\<close>
definition inverse2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow>  Rel\<^sub>3('c,'a,'b)" ("inverse\<^sub>2")
  where "inverse\<^sub>2 \<equiv> \<^bold>B\<^sub>2\<^sub>0 \<Q>"
definition inverse3 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow>  Rel\<^sub>4('d,'a,'b,'c)" ("inverse\<^sub>3")
  where "inverse\<^sub>3 \<equiv> \<^bold>B\<^sub>3\<^sub>0 \<Q>"
\<comment> \<open>... \<open>inverse\<^sub>n \<equiv> \<^bold>B\<^sub>n\<^sub>0 \<Q>\<close>\<close>

definition range2::"('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> Set('c)" ("range\<^sub>2")
  where "range\<^sub>2 \<equiv> \<exists>\<^sup>2 \<circ>\<^sub>2 inverse\<^sub>2"
definition range3::"('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> Set('d)" ("range\<^sub>3")
  where "range\<^sub>3 \<equiv> \<exists>\<^sup>3 \<circ>\<^sub>2 inverse\<^sub>3"
\<comment> \<open>... \<open>range\<^sub>n \<equiv> \<exists>\<^sup>n \<circ>\<^sub>2 inverse\<^sub>n\<close>\<close>

declare inverse2_def[func_defs] inverse3_def[func_defs] range2_def[func_defs] range3_def[func_defs]

lemma "inverse\<^sub>2 f c = (\<lambda>a b. f a b = c)" unfolding func_defs comb_defs ..
lemma "inverse\<^sub>3 f d = (\<lambda>a b c. f a b c = d)" unfolding func_defs comb_defs ..
\<comment> \<open>...\<open>inverse\<^sub>n f x = (\<lambda>a\<^sub>1 ...a\<^sub>n. f a\<^sub>1 ... a\<^sub>n = x)\<close>\<close>

lemma "range\<^sub>2 f c = (\<exists>a b. f a b = c)" unfolding func_defs comb_defs ..
lemma "range\<^sub>3 f d = (\<exists>a b c. f a b c = d)" unfolding func_defs comb_defs ..
\<comment> \<open>...\<open>range\<^sub>n f x = (\<exists>a\<^sub>1 ...a\<^sub>n. f a\<^sub>1 ... a\<^sub>n = x)\<close>\<close>


subsubsection \<open>Kernel of a Function\<close>

text \<open>The "kernel" of a function relates those elements in its domain that get assigned the same value.\<close>
definition kernel::"('a \<Rightarrow> 'b) \<Rightarrow> ERel('a)"
  where "kernel \<equiv> \<^bold>\<Psi>\<^sub>2 \<Q>"

lemma "kernel f = (\<lambda>x y. f x = f y)" unfolding kernel_def comb_defs ..

declare kernel_def[func_defs]

text \<open>We add convenient superscript notation.\<close>
notation(input) kernel ("_\<^sup>=")  notation(output) kernel ("'(_')\<^sup>=")


subsubsection \<open>Pullback and Equalizer of a Pair of Functions\<close>

text \<open>The pullback (aka. fiber product) of two functions \<open>f\<close> and \<open>g\<close> (sharing the same codomain), 
 relates those pairs of elements that get assigned the same value by \<open>f\<close> and \<open>g\<close> respectively.\<close>
definition pullback :: "('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> Rel('a,'b)"
  where "pullback \<equiv> \<^bold>B\<^sub>1\<^sub>1 \<Q>"

lemma "pullback f g = (\<lambda>x y. f x = g y)" unfolding pullback_def comb_defs ..

declare pullback_def[func_defs]

text \<open>Pullback can be said to be "symmetric" in the following sense.\<close>
lemma pullback_symm: "pullback = \<^bold>C\<^sub>2\<^sub>1\<^sub>4\<^sub>3 pullback" unfolding func_defs comb_defs by metis
lemma pullback_symm': "pullback f g x y = pullback g f y x" apply (subst pullback_symm) unfolding comb_defs ..
lemma "pullback = \<^bold>C \<circ>\<^sub>2 (\<^bold>C pullback)" apply (subst pullback_symm) unfolding comb_defs ..

text \<open>Inverse and kernel of a function can be easily stated in terms of pullback.\<close>
lemma "inverse = pullback \<^bold>I" unfolding func_defs comb_defs by auto
lemma "kernel = \<^bold>W pullback" unfolding func_defs comb_defs ..

text \<open>The equalizer of two functions \<open>f\<close> and \<open>g\<close> (sharing the same domain and codomain) is the set of 
 elements in their (common) domain that get assigned the same value by both \<open>f\<close> and \<open>g\<close>.\<close>
definition equalizer :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> Set('a)"
  where "equalizer \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 \<Q>"

lemma "equalizer f g = (\<lambda>x. f x = g x)" unfolding equalizer_def comb_defs ..

declare equalizer_def[func_defs]

text \<open>In fact, the equalizer of two functions can be stated in terms of pullback.\<close>
lemma "equalizer = \<^bold>W \<circ>\<^sub>2 pullback" unfolding func_defs comb_defs ..

text \<open>Note that we can swap the roles of "points" and "functions" in the above definitions using permutators.\<close>
lemma "\<^bold>R equalizer x = (\<lambda>f g. f x = g x)" unfolding func_defs comb_defs ..
lemma "\<^bold>C\<^sub>2 pullback x y = (\<lambda>f g. f x = g y)" unfolding func_defs comb_defs ..


subsubsection \<open>Pushout and Coequalizer of a Pair of Functions\<close>

text \<open>The pushout (aka. fiber coproduct) of two functions \<open>f\<close> and \<open>g\<close> (sharing the same domain), relates
 pairs of elements (in their codomains) whose preimages under \<open>f\<close> resp. \<open>g\<close> intersect.\<close>
definition pushout :: "('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> Rel('a,'b)" 
  where "pushout \<equiv> \<^bold>B\<^sub>2\<^sub>2 (\<sqinter>) inverse inverse" (*beware polymorphism: 'inverse' appears twice with different types*)

lemma "pushout f g = (\<lambda>x y. f\<inverse> x \<sqinter> g\<inverse> y)" unfolding pushout_def comb_defs ..

declare pushout_def[func_defs]

text \<open>Pushout can be said to be "symmetric" in the following sense.\<close>
lemma pushout_symm: "pushout = \<^bold>C\<^sub>2\<^sub>1\<^sub>4\<^sub>3 pushout" unfolding func_defs comb_defs by metis
lemma pushout_symm': "pushout f g x y = pushout g f y x" apply (subst pushout_symm) unfolding comb_defs ..
lemma "pushout = \<^bold>C \<circ>\<^sub>2 (\<^bold>C pushout)" apply (subst pushout_symm) unfolding comb_defs ..

text \<open>The equations below don't work as definitions since they unduly restrict types ("inverse" appears only once).\<close>
lemma "pushout = \<^bold>W (\<^bold>B\<^sub>2\<^sub>2 (\<sqinter>)) inverse" unfolding func_defs comb_defs .. 
lemma "pushout = \<^bold>\<Psi>\<^sub>2 (\<^bold>B\<^sub>1\<^sub>1 (\<sqinter>)) inverse" unfolding func_defs comb_defs .. 

text \<open>The coequalizer of two functions \<open>f\<close> and \<open>g\<close> (sharing the same domain and codomain) is the set of 
 elements in their (common) codomain whose preimage under \<open>f\<close> resp. \<open>g\<close> intersect.\<close>
definition coequalizer :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> Set('b)"
  where "coequalizer \<equiv> \<^bold>W \<circ>\<^sub>2 (\<^bold>\<Psi>\<^sub>2 (\<^bold>B\<^sub>1\<^sub>1 (\<sqinter>)) inverse)" 

lemma "coequalizer f g = \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<sqinter>) (f\<inverse>) (g\<inverse>)" unfolding coequalizer_def comb_defs ..
lemma "coequalizer f g = (\<lambda>x. (f\<inverse>) x \<sqinter> (g\<inverse>) x)" unfolding coequalizer_def comb_defs ..

declare coequalizer_def[func_defs]

text \<open>The coequalizer of two functions can be stated in terms of pushout.\<close>
lemma "coequalizer = \<^bold>W \<circ>\<^sub>2 pushout" unfolding func_defs comb_defs ..


subsubsection \<open>Image and Preimage\<close>

text \<open>We can "lift" functions to act on sets via the image operator. The term \<open>image f\<close> denotes a
 set-operation that takes a set \<open>A\<close> and returns the set of elements whose \<open>f\<close>-preimage intersects \<open>A\<close>.\<close>
definition image::"('a \<Rightarrow> 'b) \<Rightarrow> SetOp('a,'b)"
  where "image \<equiv> \<^bold>C (\<^bold>B\<^sub>2\<^sub>0 (\<sqinter>) inverse)"

lemma "image f A = (\<lambda>b. f\<inverse> b \<sqinter> A)" unfolding image_def comb_defs ..
lemma "image f A b = (\<exists>x. f\<inverse> b x \<and> A x)" unfolding image_def func_defs comb_defs ..

text \<open>Analogously, the term \<open>preimage f\<close> denotes a set-operation that takes a set \<open>B\<close> and returns the 
  set of those elements which \<open>f\<close> maps to some element in \<open>B\<close>.\<close>
definition preimage::"('a \<Rightarrow> 'b) \<Rightarrow> SetOp('b,'a)"
  where "preimage \<equiv> \<^bold>C \<^bold>B" \<comment> \<open>i.e. (;)\<close>

lemma "preimage f B = f ; B" unfolding preimage_def comb_defs ..
lemma "preimage f B = (\<lambda>a. B (f a))" unfolding preimage_def comb_defs ..


declare image_def[func_defs] preimage_def[func_defs]

text \<open>Introduce convenient notation.\<close>
notation(input) image ("\<lparr>_ _\<rparr>") and preimage ("\<lparr>_ _\<rparr>\<inverse>")
notation(output) image ("\<lparr>'(_') '(_')\<rparr>") and preimage ("\<lparr>'(_') '(_')\<rparr>\<inverse>")

term "\<lparr>f A\<rparr>" \<comment> \<open>read "the image of A under f"\<close>
term "\<lparr>f B\<rparr>\<inverse> = (\<lambda>a. B (f a))"  \<comment> \<open>read "the image of A under f"\<close>

text \<open>Range can be defined in terms of image as expected.\<close>
lemma range_def2: "range = \<^bold>C image \<UU>"
  unfolding comb_defs func_defs by simp

term "preimage (f::'a\<Rightarrow>'b) \<circ> image f" 
term "image (f::'a\<Rightarrow>'b) \<circ> preimage f"

(* TODO: make definitions out of these? *)
lemma "preimage f \<circ> image f = (\<lambda>A. \<lambda>a. f\<^sup>= a \<sqinter> A)"
  unfolding func_defs comb_defs by metis
lemma "image f \<circ> preimage f = (\<lambda>B. \<lambda>b. f\<inverse> b \<sqinter> preimage f B)" 
  unfolding func_defs comb_defs by metis

text \<open>Preservation/reversal of monoidal structure under set-operations.\<close>
lemma image_morph1: "image (f \<circ> g) = image f \<circ> image g"
  unfolding func_defs comb_defs by auto
lemma image_morph2: "image \<^bold>I = \<^bold>I" 
  unfolding func_defs comb_defs by simp
lemma preimage_morph1: "preimage (f \<circ> g) = preimage g \<circ> preimage f" (*note reversal*)
  unfolding func_defs comb_defs ..
lemma preimage_morph2: "preimage \<^bold>I = \<^bold>I" 
  unfolding func_defs comb_defs ..

text \<open>Random-looking simplification(?) rule that becomes useful later on.\<close> (*TODO: interpret*)
lemma image_simp1: "image ((G \<circ> R) a) \<circ> image (\<^bold>T a) = image (\<^bold>T a) \<circ> image (\<^bold>S (G \<circ> R))"
  apply(rule ext) unfolding comb_defs func_defs by fastforce


subsection \<open>Miscellaneous\<close>

text \<open>Function "update" or "override" at a point.\<close>
definition update :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b" ("_[_\<mapsto>_]")
  where "f[a \<mapsto> b] \<equiv> \<lambda>x. if x = a then b else f x"

declare update_def[func_defs]

text \<open>A set S can be closed under a n-ary endooperation, a generalized endooperation, or a set endooperation.\<close>
definition op1_closed::"EOp('a) \<Rightarrow> Set(Set('a))" ("_-closed\<^sub>1")
  where "f-closed\<^sub>1 \<equiv> \<lambda>S. \<forall>x. S x \<rightarrow> S(f x)"
definition op2_closed::"EOp\<^sub>2('a) \<Rightarrow> Set(Set('a))" ("_-closed\<^sub>2")
  where "g-closed\<^sub>2 \<equiv> \<lambda>S. \<forall>x y. S x \<rightarrow> S y \<rightarrow> S(g x y)"
definition opG_closed::"EOp\<^sub>G('a) \<Rightarrow> Set(Set('a))" ("_-closed\<^sub>G")
  where "F-closed\<^sub>G \<equiv> \<lambda>S. \<forall>X. X \<subseteq> S \<rightarrow> S(F X)"
definition setop_closed::"SetEOp('a) \<Rightarrow> Set(Set('a))" ("_-closed\<^sub>S")
  where "\<phi>-closed\<^sub>S \<equiv> \<lambda>S. \<forall>X. X \<subseteq> S \<rightarrow> \<phi> X \<subseteq> S"

declare op1_closed_def[func_defs] op2_closed_def[func_defs] 
        opG_closed_def[func_defs] setop_closed_def[func_defs]

text \<open>Closure under n-ary endooperations can be reduced to closure under (n-1)-ary endooperations.\<close>
lemma op2_closed_def2: "g-closed\<^sub>2 = (\<lambda>S. (\<forall>x. S x \<longrightarrow> (g x)-closed\<^sub>1 S))"
  unfolding func_defs by simp
lemma "(\<lambda>S. \<forall>x y z. S x \<rightarrow> S y \<rightarrow> S z \<rightarrow> S(g x y z)) = (\<lambda>S. (\<forall>x. S x \<longrightarrow> (g x)-closed\<^sub>2 S))"
  unfolding func_defs by simp
\<comment> \<open>and so on ...\<close>

text \<open>The set of elements inductively generated by \<open>G\<close> by using a sequence of constructors, as indicated.\<close>
definition inductiveSet1 :: "Set('a) \<Rightarrow> EOp('a) \<Rightarrow> Set('a)" ("indSet\<^sub>1") 
  where "indSet\<^sub>1 G f \<equiv> \<Inter>(\<lambda>S. G \<subseteq> S \<and> f-closed\<^sub>1 S)" \<comment> \<open>one unary constructor\<close>
definition inductiveSet2 :: "Set('a) \<Rightarrow> EOp\<^sub>2('a) \<Rightarrow> Set('a)" ("indSet\<^sub>2") 
  where "indSet\<^sub>2 G g \<equiv> \<Inter>(\<lambda>S. G \<subseteq> S \<and> g-closed\<^sub>2 S)" \<comment> \<open>one binary constructor\<close>
\<comment> \<open>and so on ...\<close>
definition inductiveSet11 :: "Set('a) \<Rightarrow> EOp('a) \<Rightarrow> EOp('a) \<Rightarrow> Set('a)" ("indSet\<^sub>1\<^sub>1") 
  where "indSet\<^sub>1\<^sub>1 G f\<^sub>1 f\<^sub>2 \<equiv> \<Inter>(\<lambda>S. G \<subseteq> S \<and> f\<^sub>1-closed\<^sub>1 S \<and> f\<^sub>2-closed\<^sub>1 S)" \<comment> \<open>two unary constructors\<close>
definition inductiveSet12 :: "Set('a) \<Rightarrow> EOp('a) \<Rightarrow> EOp\<^sub>2('a) \<Rightarrow> Set('a)" ("indSet\<^sub>1\<^sub>2") 
  where "indSet\<^sub>1\<^sub>2 G f g   \<equiv> \<Inter>(\<lambda>S. G \<subseteq> S \<and> f-closed\<^sub>1 S \<and> g-closed\<^sub>2 S)"  \<comment> \<open>a unary and a binary constructor\<close>
\<comment> \<open>and so on ...\<close>

declare inductiveSet1_def[func_defs] inductiveSet2_def[func_defs] 
        inductiveSet11_def[func_defs] inductiveSet12_def[func_defs]

text \<open>A convenient special case when the set of generators \<open>G\<close> is a singleton \<open>{g}\<close>.\<close>
lemma inductiveSet1_singleton: "indSet\<^sub>1 {g} f = \<Inter>(\<lambda>S. S g \<and> f-closed\<^sub>1 S)" 
  unfolding func_defs comb_defs by simp
\<comment> \<open>and so on ...\<close>

text \<open>The set of all powers (via iterated composition) for a given endofunction (including \<open>\<^bold>I\<close>).\<close>
definition funPower::"ERel(EOp('a))"
  where "funPower \<equiv> \<^bold>B (indSet\<^sub>1 (\<Q> \<^bold>I)) \<^bold>B"

declare funPower_def[func_defs]

lemma "funPower f = indSet\<^sub>1 {\<^bold>I} (\<lambda>h. f \<circ> h)" unfolding func_defs comb_defs ..
lemma funPower_def2: "funPower f g = (\<forall>S. (\<forall>h. S h \<rightarrow> S (f \<circ> h)) \<rightarrow> S \<^bold>I \<rightarrow> S g)" 
  unfolding func_defs comb_defs by metis

text \<open>Definition works as expected:\<close>
lemma "funPower f \<^bold>I" unfolding funPower_def2 by simp
lemma "funPower f f" unfolding funPower_def2 comb_defs by simp
lemma "funPower f (f\<circ>f)" unfolding funPower_def2 comb_defs by simp
lemma "funPower f (f\<circ>f\<circ>f\<circ>f\<circ>f\<circ>f\<circ>f\<circ>f\<circ>f\<circ>f\<circ>f\<circ>f)" unfolding funPower_def2 comb_defs by simp
lemma funPower_ind: "funPower f g \<Longrightarrow> funPower f (f \<circ> g)" by (metis funPower_def2)

(*Useful(?) property (cf. Bishop & Andrews 1998)*)
lemma "(\<exists>g. funPower f g \<and> \<exists>!(FP g)) \<rightarrow> \<exists>(FP f)" \<comment> \<open>proof by external provers\<close>
  unfolding funPower_def2 unfolding func_defs \<Phi>21_comb_def S11_comb_def 
  oops (*TODO: zipperpin can use "comm f \<equiv> \<lambda>g. f \<circ> g = g \<circ> f" to find a proof*)


end