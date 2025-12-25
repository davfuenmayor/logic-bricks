theory pair
  imports "../../pairs"
begin

section \<open>Pair Monad\<close>

text \<open>We can conceive of types of form \<open>Pair('a)\<close>, i.e. \<open>o \<Rightarrow> 'a\<close>, as arising via "environmentalization"
 (or "indexation") of the type \<open>'a\<close> by the boolean type \<open>o\<close> (i.e. as an instance of the environment 
 monad discussed previously). Furthermore, we can adopt an alternative perspective and consider a 
 constructor that returns the type of "\<open>'a\<close>-valuations" for booleans. This type constructor comes with
  a monad structure too (and is also an applicative and a functor).\<close>

named_theorems all_defs
declare comb_defs[all_defs] pair_defs[all_defs]


subsection \<open>Functor\<close>

abbreviation(input) fmap0::"'a \<Rightarrow> Pair('a)"
  where "fmap0 \<equiv> \<^bold>\<Psi>\<^sub>2\<^sub>0 mkPair"
abbreviation(input) fmap1::"('a \<Rightarrow> 'b) \<Rightarrow> Pair('a) \<Rightarrow> Pair('b)"
  where "fmap1 \<equiv> \<^bold>\<Psi>\<^sub>2\<^sub>1 mkPair \<ggreater> uncurry"
abbreviation(input) fmap2::"('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> (Pair('a) \<Rightarrow> Pair('b) \<Rightarrow> Pair('c))"
  where "fmap2 \<equiv> \<^bold>\<Psi>\<^sub>2\<^sub>2 mkPair \<ggreater> (uncurry \<ggreater>\<^sub>2 uncurry)"
abbreviation(input) fmap3::"('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> (Pair('a) \<Rightarrow> Pair('b) \<Rightarrow> Pair('c) \<Rightarrow> Pair('d))"
  where "fmap3 \<equiv> \<^bold>\<Psi>\<^sub>2\<^sub>3 mkPair \<ggreater> (uncurry \<ggreater>\<^sub>2 uncurry \<ggreater>\<^sub>2 uncurry)"
abbreviation(input) fmap4::"('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> (Pair('a) \<Rightarrow> Pair('b) \<Rightarrow> Pair('c) \<Rightarrow> Pair('d) \<Rightarrow> Pair('e))"
  where "fmap4 \<equiv> \<^bold>\<Psi>\<^sub>2\<^sub>4 mkPair \<ggreater> (uncurry \<ggreater>\<^sub>2 uncurry \<ggreater>\<^sub>2 uncurry \<ggreater>\<^sub>2 uncurry)"
\<comment> \<open>\<dots>  \<open>fmapN \<equiv> \<^bold>\<Psi>\<^sub>2\<^sub>n mkPair) \<ggreater> (uncurry)\<^sup>n\<close>\<close>

text \<open>Functor's "unit" (monad's "return" resp. applicative's "pure") corresponds to the nullary case.\<close>
abbreviation "unit \<equiv> fmap0"
text \<open>Functor's classic "fmap" corresponds to the unary case.\<close>
abbreviation "fmap \<equiv> fmap1"


subsection \<open>Applicative\<close>

abbreviation(input) ap0::"Pair('b) \<Rightarrow> Pair('b)"
  where "ap0 \<equiv> \<^bold>\<Psi>\<^sub>2\<^sub>1 (\<^bold>\<Phi>\<^sub>2\<^sub>1 mkPair) \<^bold>T \<T> \<F>" \<comment> \<open>ie. \<open>\<^bold>A\<close>\<close>
abbreviation(input) ap1::"Pair('a \<Rightarrow> 'b) \<Rightarrow> Pair('a) \<Rightarrow> Pair('b)"
  where "ap1 \<equiv> \<^bold>\<Psi>\<^sub>2\<^sub>1 (\<^bold>\<Phi>\<^sub>2\<^sub>2 mkPair) (\<^bold>R\<^sub>3 \<^bold>S) \<T> \<F>"
abbreviation(input) ap2::"Pair('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> (Pair('a) \<Rightarrow> Pair('b) \<Rightarrow> Pair('c))"
  where "ap2 \<equiv> \<^bold>\<Psi>\<^sub>2\<^sub>1 (\<^bold>\<Phi>\<^sub>2\<^sub>3 mkPair) (\<^bold>R\<^sub>4 \<^bold>S\<^sub>2\<^sub>1) \<T> \<F>"
abbreviation(input) ap3::"Pair('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> (Pair('a) \<Rightarrow> Pair('b) \<Rightarrow> Pair('c) \<Rightarrow> Pair('d))"
  where "ap3 \<equiv> \<^bold>\<Psi>\<^sub>2\<^sub>1 (\<^bold>\<Phi>\<^sub>2\<^sub>4 mkPair) (\<^bold>R\<^sub>5 \<^bold>S\<^sub>3\<^sub>1) \<T> \<F>"
\<comment> \<open>...and so on\<close>

lemma "ap0 = fmap1 \<^bold>I" unfolding all_defs ..
lemma "ap1 = fmap2 \<^bold>I" unfolding all_defs ..
lemma "ap2 = fmap3 \<^bold>I" unfolding all_defs ..
lemma "ap3 = fmap4 \<^bold>I" unfolding all_defs ..
\<comment> \<open>...and so on\<close>

text \<open>Applicative's classic "ap" corresponds to the unary case.\<close>
abbreviation "ap \<equiv> ap1"
abbreviation(input) apr :: "Pair('a) \<Rightarrow> Pair('a \<Rightarrow> 'b) \<Rightarrow> Pair('b)"(infixl "*>" 54)
  where "a *> f \<equiv> ap f a"  \<comment> \<open>convenient "pipeline notation"\<close>

text \<open>Indeed, we have:\<close> (*TODO: complete and add to other monads too*)
lemma "ap0 = \<^bold>A" unfolding all_defs by fastforce
lemma "ap1 = \<^bold>\<Phi>\<^sub>2\<^sub>1 ap0" unfolding all_defs by fastforce
\<comment> \<open>...and so on\<close>

text \<open>Check that applicative operations satisfy the corresponding laws.\<close>
lemma ap_identity:    "x *> (unit \<^bold>I) = x" unfolding all_defs by auto
lemma ap_composition: "w *> (v *> (u *> (unit \<^bold>B))) = (w *> v) *> u" unfolding all_defs by presburger
lemma ap_homomorphism: "(unit x) *> (unit f) = unit (f x)" unfolding all_defs by simp
lemma ap_interchange: "(unit x) *> f = f *> unit (\<^bold>T x)" unfolding all_defs by simp


subsection \<open>Monad\<close>

text \<open>In fact (m-ary versions of) rightImage corresponds to (m-ary versions of) bindr.\<close>
abbreviation(input) bindr1::"('a \<Rightarrow> Pair('b)) \<Rightarrow> Pair('a) \<Rightarrow> Pair('b)"
  where "bindr1 \<equiv> (\<^bold>\<Psi>\<^sub>2\<^sub>1 \<ggreater>\<^sub>4 \<^bold>C) (\<^bold>\<Phi>\<^sub>2\<^sub>2 mkPair) (\<^bold>C\<^sub>3 \<^bold>\<Sigma>) \<T> \<F>"
abbreviation(input) bindr2::"('a \<Rightarrow> 'b \<Rightarrow> Pair('c)) \<Rightarrow> (Pair('a) \<Rightarrow> Pair('b) \<Rightarrow> Pair('c))"
  where "bindr2 \<equiv> (\<^bold>\<Psi>\<^sub>2\<^sub>1 \<ggreater>\<^sub>4 \<^bold>C\<^sub>3) (\<^bold>\<Phi>\<^sub>2\<^sub>3 mkPair) (\<^bold>C\<^sub>4 \<^bold>\<Sigma>\<^sub>2\<^sub>1) \<T> \<F>"
abbreviation(input) bindr3::"('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> Pair('d)) \<Rightarrow> (Pair('a) \<Rightarrow> Pair('b) \<Rightarrow> Pair('c) \<Rightarrow> Pair('d))"
  where "bindr3 \<equiv> (\<^bold>\<Psi>\<^sub>2\<^sub>1 \<ggreater>\<^sub>4 \<^bold>C\<^sub>4) (\<^bold>\<Phi>\<^sub>2\<^sub>4 mkPair) (\<^bold>C\<^sub>5 \<^bold>\<Sigma>\<^sub>3\<^sub>1) \<T> \<F>"
\<comment> \<open>...and so on\<close>

text \<open>Monad's usual "bind" corresponds to the (reversed) unary case, and gets its customary notation.\<close>
abbreviation "bindr \<equiv> bindr1"
abbreviation(input) bind::"Pair('a) \<Rightarrow> ('a \<Rightarrow> Pair('b)) \<Rightarrow> Pair('b)" (infixl "\<bind>" 54)
  where "a \<bind> f \<equiv> bindr f a"

text \<open>fmap can be stated in terms of (reversed) bind and unit...\<close>
lemma "fmap = (\<^bold>B \<ggreater>\<^sub>2 bindr) unit" unfolding all_defs by presburger
text \<open>... and ap in terms of bind and fmap\<close>
lemma "ap = \<^bold>B\<^sub>1\<^sub>1 bind \<^bold>I (\<^bold>C fmap)" unfolding all_defs by presburger

text \<open>The so-called "monad laws". They guarantee that term operations compose reliably.\<close>
lemma monad_unit1: "(unit x \<bind> f) = f x" unfolding all_defs by auto  \<comment> \<open>left identity\<close>
lemma monad_unit2: "(x \<bind> unit) = x" unfolding all_defs by auto      \<comment> \<open>right identity\<close>
lemma monad_assoc: "((x \<bind> f) \<bind> g) = (x \<bind> (\<lambda>z. f z \<bind> g))" unfolding all_defs by simp \<comment> \<open>associativity\<close>


text \<open>Monad's "join" corresponds in fact to big-union.\<close>
abbreviation(input) join::"Pair(Pair('a)) \<Rightarrow> Pair('a)"
  where "join \<equiv> \<^bold>\<Psi>\<^sub>2\<^sub>1 (\<^bold>\<Phi>\<^sub>2\<^sub>1 mkPair) (\<^bold>C\<^bold>W) \<T> \<F>"

text \<open>Recalling that\<close>
lemma "join = bindr \<^bold>I" unfolding all_defs ..

text \<open>We extrapolate to obtain some interesting interrelations, for different arities\<close>
lemma "ap0 \<ggreater> join = bindr1 \<^bold>I" unfolding all_defs by presburger
lemma "ap1 \<ggreater>\<^sub>2 join = bindr2 \<^bold>I" unfolding all_defs by presburger
lemma "ap2 \<ggreater>\<^sub>3 join = bindr3 \<^bold>I" unfolding all_defs by presburger

text \<open>Similarly, we can define bindr in terms of join and fmap, for different arities\<close>
lemma "bindr1 = fmap1 \<ggreater>\<^sub>2 join" unfolding all_defs by presburger
lemma "bindr2 = fmap2 \<ggreater>\<^sub>3 join" unfolding all_defs by presburger
lemma "bindr3 = fmap3 \<ggreater>\<^sub>4 join" unfolding all_defs by presburger

text \<open>Moreover, recalling that\<close>
lemma "ap F A = join (fmap (\<lambda>f. fmap f A) F)" unfolding all_defs by simp 

text \<open>We can extrapolate to define ap in terms of join and fmap\<close> (*TODO: for different arities*)
lemma "ap1 = ((\<^bold>C \<ggreater> (\<ggreater>) \<ggreater>\<^sub>2 \<^bold>C) fmap fmap) \<ggreater>\<^sub>2 join" unfolding all_defs by presburger


subsection \<open>Pipelines\<close>

subsubsection \<open>Arrows\<close>

text \<open>Monadic (aka. Kleisli) arrows correspond to relations\<close>
term "(m :: 'a \<Rightarrow> Pair('b)) :: 'a \<Rightarrow> o \<Rightarrow> 'b"
text \<open>Applicative (aka. static) arrows correspond to function-sets (sets of functions)\<close>
term "(a :: Pair('a \<Rightarrow> 'b)) :: o \<Rightarrow> 'a \<Rightarrow> 'b"

text \<open>Takes a plain function and disguises it as a monadic arrow.\<close>
abbreviation(input) asArrowM::"('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> Pair('b))"
  where "asArrowM \<equiv> \<^bold>B (\<^bold>W mkPair)"

text \<open>Takes an applicative arrow and transforms it into a monadic arrow.\<close>
abbreviation(input) intoArrowM::"Pair('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> Pair('b))"
  where "intoArrowM \<equiv> \<^bold>\<Psi>\<^sub>2\<^sub>1 (\<^bold>\<Phi>\<^sub>2\<^sub>2 mkPair) \<^bold>T \<T> \<F>"
text \<open>Takes a monadic arrow and transforms it into an applicative arrow.\<close>
abbreviation(input) intoArrowA::"('a \<Rightarrow> Pair('b)) \<Rightarrow> Pair('a \<Rightarrow> 'b)"
  where "intoArrowA \<equiv> \<^bold>\<Psi>\<^sub>2\<^sub>1 (\<^bold>\<Phi>\<^sub>2\<^sub>1 mkPair) (\<^bold>R\<^sub>3 \<^bold>I) \<T> \<F>"

lemma "intoArrowM p a = <\<pi>\<^sub>1 p a, \<pi>\<^sub>2 p a>" unfolding all_defs ..
lemma "intoArrowA f = <f \<ggreater> \<pi>\<^sub>1 , f \<ggreater> \<pi>\<^sub>2>" unfolding all_defs ..

text \<open>Note that\<close>
lemma "ap = intoArrowM \<ggreater> bindr" unfolding all_defs by presburger


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
abbreviation(input) mcomp::"('b \<Rightarrow> Pair('c)) \<Rightarrow> ('a \<Rightarrow> Pair('b)) \<Rightarrow> ('a \<Rightarrow> Pair('c))" 
  where "mcomp \<equiv> \<^bold>D bindr"
abbreviation(input) mcomp' (infixr "\<Zfinj>" 56) \<comment> \<open>reversed monadic composition, aka. the fish operator ">=>"\<close>
  where "f \<Zfinj> g \<equiv> mcomp g f"

lemma "f \<Zfinj> g = (\<lambda>x. f x \<bind> g)" unfolding comb_defs ..

text \<open>Note the corresponding types:\<close>
term "(\<bind>) :: Pair('a) \<Rightarrow> ('a \<Rightarrow> Pair('b)) \<Rightarrow> Pair('b)"
term "(\<Zfinj>)  :: ('a \<Rightarrow> Pair('b)) \<Rightarrow> ('b \<Rightarrow> Pair('c)) \<Rightarrow> ('a \<Rightarrow> Pair('c))"

text \<open>As expected, monadic composition is associative and suitably interrelates with bind to build pipelines:\<close>
lemma "f \<Zfinj> (g \<Zfinj> h) = (f \<Zfinj> g) \<Zfinj> h" unfolding all_defs by presburger
lemma "(x \<bind> f \<bind> g \<bind> h) = (x \<bind> f \<Zfinj> g \<Zfinj> h)" unfolding all_defs by simp

text \<open>Bind in terms of monadic composition\<close>
lemma "bindr = (\<Zfinj>) \<^bold>I" unfolding comb_defs ..
lemma "(\<bind>) = ((\<Zfinj>) \<ggreater> \<^bold>C) \<^bold>I" unfolding comb_defs ..


subsubsection \<open>Applicative composition\<close>

text \<open>Analogously, we can introduce applicative composition.\<close>
abbreviation(input) acomp::"Pair('b \<Rightarrow> 'c) \<Rightarrow> Pair('a \<Rightarrow> 'b) \<Rightarrow> Pair('a \<Rightarrow> 'c)" 
  where "acomp \<equiv> (\<^bold>D (\<ggreater>\<^sub>2) intoArrowM ap) \<ggreater>\<^sub>2 intoArrowA"
abbreviation(input) acomp' (infixr "\<Zinj>" 56) \<comment> \<open>reversed applicative composition\<close>
  where "f \<Zinj> g \<equiv> acomp g f"

lemma "f \<Zinj> g = intoArrowA (intoArrowM f \<ggreater> ap g)" unfolding comb_defs ..
lemma "f \<Zinj> g = intoArrowA (\<lambda>x. (intoArrowM f x) *> g)" unfolding comb_defs ..

text \<open>Note the corresponding types:\<close>
term "(*>) :: Pair('a) \<Rightarrow> Pair('a \<Rightarrow> 'b) \<Rightarrow> Pair('b)"
term "(\<Zinj>) :: Pair('a \<Rightarrow> 'b) \<Rightarrow> Pair('b \<Rightarrow> 'c) \<Rightarrow> Pair('a \<Rightarrow> 'c)"

text \<open>Applicative composition is associative and suitably interrelates with ap to build pipelines:\<close>
lemma "f \<Zinj> (g \<Zinj> h) = (f \<Zinj> g) \<Zinj> h" unfolding all_defs by presburger
lemma "(x *> f *> g *> h) = (x *> f \<Zinj> g \<Zinj> h)" unfolding all_defs by simp

text \<open>The following interrelations hold in the current (pair) monad:\<close>
lemma "f \<Zinj> g = ap (fmap (\<ggreater>) f) g" unfolding all_defs by presburger
lemma "f \<Zinj> g = ap (ap (unit (\<ggreater>)) f) g" unfolding all_defs by presburger
lemma "(\<Zinj>) = fmap2 (\<ggreater>)" unfolding all_defs by presburger 

end