theory env
imports "../../logic_bridge"
begin

section \<open>Environment Monad\<close>

text \<open>We can conceive of functional types of the form \<open>'a \<Rightarrow> 'b\<close> as arising via an "environmentalization",
 or "indexation" of the type \<open>'b\<close> by the type \<open>'a\<close>, i.e. as \<open>'a-Env('b)\<close> using our type notation. 
 This type constructor comes with a monad structure (and is thus an applicative and a functor too).\<close>


subsection \<open>Functor\<close>

text \<open>Note that \<open>\<^bold>\<Phi>\<^sub>m\<^sub>n\<close> combinators can be used to index (or "environmentalize") a given m-ary function n-times.\<close>
term "(\<^bold>\<Phi>\<^sub>0\<^sub>1 (f::'a)) :: 'e-Env('a)"
term "(\<^bold>\<Phi>\<^sub>1\<^sub>1 (f::'a \<Rightarrow> 'b)) :: 'e-Env('a) \<Rightarrow> 'e-Env('b)"
term "(\<^bold>\<Phi>\<^sub>1\<^sub>2 (f::'a \<Rightarrow> 'b)) :: 'e\<^sub>2-Env('e\<^sub>1-Env('a)) \<Rightarrow> 'e\<^sub>2-Env('e\<^sub>1-Env('b))"
\<comment> \<open>...and so on\<close>
term "(\<^bold>\<Phi>\<^sub>2\<^sub>1 (g::'a \<Rightarrow> 'b \<Rightarrow> 'c)) :: 'e-Env('a) \<Rightarrow> 'e-Env('b) \<Rightarrow> 'e-Env('c)"
term "(\<^bold>\<Phi>\<^sub>2\<^sub>2 (g::'a \<Rightarrow> 'b \<Rightarrow> 'c)) :: 'e\<^sub>2-Env('e\<^sub>1-Env('a)) \<Rightarrow> 'e\<^sub>2-Env('e\<^sub>1-Env('b)) \<Rightarrow> 'e\<^sub>2-Env('e\<^sub>1-Env('c))"
\<comment> \<open>...and so on\<close>

text \<open>Hence the \<open>\<^bold>\<Phi>\<^sub>m\<^sub>n\<close> combinators can play the role of (n-times iterated) "m-ary functor maps".\<close>
abbreviation(input) fmap0::"'a \<Rightarrow> 'e-Env('a)"
  where "fmap0 \<equiv> \<^bold>\<Phi>\<^sub>0\<^sub>1" \<comment> \<open>aka. \<open>\<^bold>K\<close>\<close>
abbreviation(input) fmap1::"('a \<Rightarrow> 'b) \<Rightarrow> 'e-Env('a) \<Rightarrow> 'e-Env('b)"
  where "fmap1 \<equiv> \<^bold>\<Phi>\<^sub>1\<^sub>1" \<comment> \<open>aka. \<open>\<^bold>B\<close>\<close>
abbreviation(input) fmap2::"('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('e-Env('a) \<Rightarrow> 'e-Env('b) \<Rightarrow> 'e-Env('c))"
  where "fmap2 \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1" \<comment> \<open>cf. Haskell's \<open>liftA2\<close>\<close>
abbreviation(input) fmap3::"('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('e-Env('a) \<Rightarrow> 'e-Env('b) \<Rightarrow> 'e-Env('c) \<Rightarrow> 'e-Env('d))"
  where "fmap3 \<equiv> \<^bold>\<Phi>\<^sub>3\<^sub>1"
abbreviation(input) fmap4::"('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'f) \<Rightarrow> ('e-Env('a) \<Rightarrow> 'e-Env('b) \<Rightarrow> 'e-Env('c) \<Rightarrow> 'e-Env('d) \<Rightarrow> 'e-Env('f))"
  where "fmap4 \<equiv> \<^bold>\<Phi>\<^sub>4\<^sub>1"
\<comment> \<open>...and so on\<close>

text \<open>Functor's "unit" (monad's "return" resp. applicative's "pure") corresponds to the nullary case.\<close>
abbreviation "unit \<equiv> fmap0"
text \<open>Functor's classic "fmap" corresponds to the unary case.\<close>
abbreviation "fmap \<equiv> fmap1"

text \<open>Indeed, we have:\<close>
lemma "unit = \<^bold>K" unfolding comb_defs ..
lemma "fmap = \<^bold>B" unfolding comb_defs ..


subsection \<open>Applicative\<close>

text \<open>Analogously, we can employ the combinator family \<open>\<^bold>S\<^sub>m\<^sub>n\<close> as (n-times iterated) "m-ary applicatives".\<close>
abbreviation(input) ap0::"'e-Env('b) \<Rightarrow> 'e-Env('b)"
  where "ap0 \<equiv> \<^bold>S\<^sub>0\<^sub>1" \<comment> \<open>aka. \<open>\<^bold>A\<close>\<close>
abbreviation(input) ap1::"'e-Env('a \<Rightarrow> 'b) \<Rightarrow> 'e-Env('a) \<Rightarrow> 'e-Env('b)"
  where "ap1 \<equiv> \<^bold>S\<^sub>1\<^sub>1" \<comment> \<open>aka. \<open>\<^bold>S\<close>\<close>
abbreviation(input) ap2::"'e-Env('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('e-Env('a) \<Rightarrow> 'e-Env('b) \<Rightarrow> 'e-Env('c))"
  where "ap2 \<equiv> \<^bold>S\<^sub>2\<^sub>1"
abbreviation(input) ap3::"'e-Env('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('e-Env('a) \<Rightarrow> 'e-Env('b) \<Rightarrow> 'e-Env('c) \<Rightarrow> 'e-Env('d))"
  where "ap3 \<equiv> \<^bold>S\<^sub>3\<^sub>1"
\<comment> \<open>...and so on\<close>

text \<open>In fact, we have that n-ary applicatives result from applying n+1-ary fmap to the identity function.\<close>
lemma "ap0 = fmap1 \<^bold>I" unfolding comb_defs ..
lemma "ap1 = fmap2 \<^bold>I" unfolding comb_defs ..
lemma "ap2 = fmap3 \<^bold>I" unfolding comb_defs ..
lemma "ap3 = fmap4 \<^bold>I" unfolding comb_defs ..
\<comment> \<open>...and so on\<close>

text \<open>Applicative's classic "ap" corresponds to the unary case.\<close>
abbreviation "ap \<equiv> ap1"
abbreviation(input) apr :: "'e-Env('a) \<Rightarrow> 'e-Env('a \<Rightarrow> 'b) \<Rightarrow> 'e-Env('b)"(infixl "*>" 54)
  where "a *> f \<equiv> ap f a"  \<comment> \<open>convenient "pipeline notation"\<close>

text \<open>Indeed, we have:\<close>
lemma "ap = \<^bold>S" unfolding comb_defs ..

text \<open>Check that applicative operations satisfy the corresponding laws.\<close>
lemma ap_identity:    "x *> (unit \<^bold>I) = x" unfolding comb_defs ..
lemma ap_composition: "w *> (v *> (u *> (unit \<^bold>B))) = (w *> v) *> u" unfolding comb_defs ..
lemma ap_homomorphism: "(unit x) *> (unit f) = unit (f x)" unfolding comb_defs ..
lemma ap_interchange: "(unit x) *> f = f *> unit (\<^bold>T x)" unfolding comb_defs ..


subsection \<open>Monad\<close>

text \<open>In the same spirit, we can employ the combinator family \<open>\<^bold>\<Sigma>\<^sub>m\<^sub>n\<close> as (n-times iterated) "m-ary binds".\<close>
abbreviation(input) bindr1::"('a \<Rightarrow> 'e-Env('b)) \<Rightarrow> 'e-Env('a) \<Rightarrow> 'e-Env('b)"
  where "bindr1 \<equiv> \<^bold>\<Sigma>\<^sub>1\<^sub>1" \<comment> \<open>bind-reversed\<close>
abbreviation(input) bindr2::"('a \<Rightarrow> 'b \<Rightarrow> 'e-Env('c)) \<Rightarrow> ('e-Env('a) \<Rightarrow> 'e-Env('b) \<Rightarrow> 'e-Env('c))"
  where "bindr2 \<equiv> \<^bold>\<Sigma>\<^sub>2\<^sub>1"
abbreviation(input) bindr3::"('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'e-Env('d)) \<Rightarrow> ('e-Env('a) \<Rightarrow> 'e-Env('b) \<Rightarrow> 'e-Env('c) \<Rightarrow> 'e-Env('d))"
  where "bindr3 \<equiv> \<^bold>\<Sigma>\<^sub>3\<^sub>1"
\<comment> \<open>...and so on\<close>

text \<open>Monad's usual "bind" corresponds to the (reversed) unary case, and gets its customary notation.\<close>
abbreviation "bindr \<equiv> bindr1"
abbreviation(input) bind::"'e-Env('a) \<Rightarrow> ('a \<Rightarrow> 'e-Env('b)) \<Rightarrow> 'e-Env('b)" (infixl "\<bind>" 54)
  where "a \<bind> f \<equiv> bindr f a"

text \<open>In fact, we have that\<close>
lemma "bindr = \<^bold>\<Sigma>" unfolding comb_defs ..
lemma "bindr = \<^bold>B \<ggreater>\<^sub>2 \<^bold>W" unfolding comb_defs ..

text \<open>fmap can be stated in terms of (reversed) bind and unit...\<close>
lemma "fmap = (\<^bold>B \<ggreater>\<^sub>2 bindr) unit"   unfolding comb_defs ..
text \<open>... and ap in terms of bind and fmap\<close>
lemma "ap = \<^bold>B\<^sub>1\<^sub>1 bind \<^bold>I (\<^bold>C fmap)" unfolding comb_defs ..

text \<open>The so-called "monad laws". They guarantee that term operations compose reliably.\<close>
lemma monad_unit1: "(unit x \<bind> f) = f x" unfolding comb_defs ..  \<comment> \<open>left identity\<close>
lemma monad_unit2: "(x \<bind> unit) = x" unfolding comb_defs ..      \<comment> \<open>right identity\<close>
lemma monad_assoc: "((x \<bind> f) \<bind> g) = (x \<bind> (\<lambda>z. f z \<bind> g))" unfolding comb_defs .. \<comment> \<open>associativity\<close>


text \<open>Monad's "join" corresponds in fact to the \<open>\<^bold>W\<close> combinator.\<close>
abbreviation(input) join::"'e-Env('e-Env('a)) \<Rightarrow> 'e-Env('a)"
  where "join  \<equiv> \<^bold>W"

text \<open>Recalling that\<close>
lemma "join = bindr \<^bold>I" unfolding comb_defs ..

text \<open>We extrapolate to obtain some interesting interrelations, for different arities\<close>
lemma "ap0 \<ggreater> join = bindr1 \<^bold>I" unfolding comb_defs ..
lemma "ap1 \<ggreater>\<^sub>2 join = bindr2 \<^bold>I" unfolding comb_defs ..
lemma "ap2 \<ggreater>\<^sub>3 join = bindr3 \<^bold>I" unfolding comb_defs ..

text \<open>Similarly, we can define bindr in terms of join and fmap, for different arities\<close>
lemma "bindr1 = fmap1 \<ggreater>\<^sub>2 join" unfolding comb_defs ..
lemma "bindr2 = fmap2 \<ggreater>\<^sub>3 join" unfolding comb_defs ..
lemma "bindr3 = fmap3 \<ggreater>\<^sub>4 join" unfolding comb_defs ..

text \<open>Moreover, recalling that\<close>
lemma "ap F A = join (fmap (\<lambda>f. fmap f A) F)"  unfolding comb_defs ..

text \<open>We can extrapolate to define ap in terms of join and fmap\<close> (*TODO: for different arities*)
lemma "ap1 = ((\<^bold>C \<ggreater> (\<ggreater>) \<ggreater>\<^sub>2 \<^bold>C) fmap fmap) \<ggreater>\<^sub>2 join"  unfolding comb_defs ..


subsection \<open>Pipelines\<close>

subsubsection \<open>Arrows\<close>

text \<open>Monadic (aka. Kleisli) arrows\<close>
term "(m :: 'a \<Rightarrow> 'e-Env('b)) :: 'a \<Rightarrow> 'e \<Rightarrow> 'b"
text \<open>Applicative (aka. static) arrows\<close>
term "(a :: 'e-Env('a \<Rightarrow> 'b)) :: 'e \<Rightarrow> 'a \<Rightarrow> 'b"

text \<open>Takes a plain function and disguises it as a monadic arrow.\<close>
abbreviation(input) asArrowM::"('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'e-Env('b))"
  where "asArrowM \<equiv> \<^bold>B \<^bold>K"

text \<open>Takes an applicative arrow and transforms it into a monadic arrow.\<close>
abbreviation(input) intoArrowM::"'e-Env('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'e-Env('b))"
  where "intoArrowM \<equiv> \<^bold>C"
text \<open>Takes a monadic arrow and transforms it into an applicative arrow.\<close>
abbreviation(input) intoArrowA::"('a \<Rightarrow> 'e-Env('b)) \<Rightarrow> 'e-Env('a \<Rightarrow> 'b)"
  where "intoArrowA \<equiv> \<^bold>C"

text \<open>Note that\<close>
lemma "ap = intoArrowM \<ggreater> bindr" unfolding comb_defs ..


subsubsection \<open>Functional composition\<close>

text \<open>Recall that for the case of plain functions, we have the following types:\<close>
term "(|>) :: 'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b"                  \<comment> \<open>(reversed) application\<close>
term "(\<ggreater>)  :: 'e-Env('a) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'e-Env('b)"  \<comment> \<open>(reversed) composition\<close>

text \<open>Composition is associative and suitably interrelates with application to build pipelines.\<close>
lemma "f \<ggreater> (g \<ggreater> h) = (f \<ggreater> g) \<ggreater> h" unfolding comb_defs ..
lemma "(x |> f |> g |> h) = (x |> f \<ggreater> g \<ggreater> h)" unfolding comb_defs ..

text \<open>Interrelation between application and composition.\<close>
lemma "(\<ggreater>) = (\<lambda>f g x. x |> f |> g)" unfolding comb_defs ..
lemma "\<^bold>A = \<^bold>B \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>B = \<^bold>D \<^bold>A" unfolding comb_defs ..


subsubsection \<open>Monadic composition\<close>

text \<open>Thus, monadic (aka. Kleisli-) composition is to "bindr" as functional composition is to application.\<close>
abbreviation(input) mcomp::"('b \<Rightarrow> 'e-Env('c)) \<Rightarrow> ('a \<Rightarrow> 'e-Env('b)) \<Rightarrow> ('a \<Rightarrow> 'e-Env('c))" 
  where "mcomp \<equiv> \<^bold>D bindr"
abbreviation(input) mcomp' (infixr "\<Zfinj>" 56) \<comment> \<open>reversed monadic composition, aka. the fish operator ">=>"\<close>
  where "f \<Zfinj> g \<equiv> mcomp g f"

lemma "f \<Zfinj> g = (\<lambda>x. f x \<bind> g)" unfolding comb_defs ..

text \<open>Note the corresponding types:\<close>
term "(\<bind>) :: 'e-Env('a) \<Rightarrow> ('a \<Rightarrow> 'e-Env('b)) \<Rightarrow> 'e-Env('b)"
term "(\<Zfinj>)  :: ('a \<Rightarrow> 'e-Env('b)) \<Rightarrow> ('b \<Rightarrow> 'e-Env('c)) \<Rightarrow> ('a \<Rightarrow> 'e-Env('c))"

text \<open>As expected, monadic composition is associative and suitably interrelates with bind to build pipelines:\<close>
lemma "f \<Zfinj> (g \<Zfinj> h) = (f \<Zfinj> g) \<Zfinj> h" unfolding comb_defs ..
lemma "(x \<bind> f \<bind> g \<bind> h) = (x \<bind> f \<Zfinj> g \<Zfinj> h)" unfolding comb_defs ..

text \<open>Bind in terms of monadic composition\<close>
lemma "bindr = (\<Zfinj>) \<^bold>I" unfolding comb_defs ..
lemma "(\<bind>) = ((\<Zfinj>) \<ggreater> \<^bold>C) \<^bold>I" unfolding comb_defs ..


subsubsection \<open>Applicative composition\<close>

text \<open>Analogously, we can introduce applicative composition.\<close>
abbreviation(input) acomp::"'e-Env('b \<Rightarrow> 'c) \<Rightarrow> 'e-Env('a \<Rightarrow> 'b) \<Rightarrow> 'e-Env('a \<Rightarrow> 'c)" 
  where "acomp \<equiv> (\<^bold>D (\<ggreater>\<^sub>2) intoArrowM ap) \<ggreater>\<^sub>2 intoArrowA"
abbreviation(input) acomp' (infixr "\<Zinj>" 56) \<comment> \<open>reversed applicative composition\<close>
  where "f \<Zinj> g \<equiv> acomp g f"

lemma "f \<Zinj> g = intoArrowA (intoArrowM f \<ggreater> ap g)" unfolding comb_defs ..
lemma "f \<Zinj> g = intoArrowA (\<lambda>x. (intoArrowM f x) *> g)" unfolding comb_defs ..
lemma "f \<Zinj> g = (\<lambda>e\<^sub>1. \<lambda>x. ((\<lambda>e\<^sub>2. f e\<^sub>2 x) *> g) e\<^sub>1)" unfolding comb_defs ..

text \<open>Note the corresponding types:\<close>
term "(*>) :: 'e-Env('a) \<Rightarrow> 'e-Env('a \<Rightarrow> 'b) \<Rightarrow> 'e-Env('b)"
term "(\<Zinj>) :: 'e-Env('a \<Rightarrow> 'b) \<Rightarrow> 'e-Env('b \<Rightarrow> 'c) \<Rightarrow>  'e-Env('a \<Rightarrow> 'c)"

text \<open>Applicative composition is associative and suitably interrelates with ap to build pipelines:\<close>
lemma "f \<Zinj> (g \<Zinj> h) = (f \<Zinj> g) \<Zinj> h" unfolding comb_defs ..
lemma "(x *> f *> g *> h) = (x *> f \<Zinj> g \<Zinj> h)" unfolding comb_defs ..

text \<open>The following interrelations hold in the current (environment) monad:\<close>
lemma "f \<Zinj> g = ap (fmap (\<ggreater>) f) g" unfolding comb_defs ..
lemma "f \<Zinj> g = ap (ap (unit (\<ggreater>)) f) g" unfolding comb_defs ..
lemma "(\<Zinj>) = fmap2 (\<ggreater>)" unfolding comb_defs ..

end