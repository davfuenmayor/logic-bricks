theory set
imports "../../operators"
begin

section \<open>Set Monad\<close>

text \<open>We can conceive of types of form \<open>Set('a)\<close>, i.e. \<open>'a \<Rightarrow> o\<close>, as arising via an "environmentalization"
 (or "indexation") of the boolean type \<open>o\<close> by the type \<open>'a\<close> (i.e. as an instance of the environment 
 monad discussed previously). Furthermore, we can adopt an alternative perspective and consider a 
 constructor that returns the type of boolean "valuations" (or "classifiers") for objects of type \<open>'a\<close>.
 This type constructor comes with a (dual) monad structure too (and is also an applicative and a functor).\<close>

named_theorems all_defs
declare comb_defs[all_defs] func_defs[all_defs] rel_defs[all_defs]

subsection \<open>Functor\<close>

abbreviation(input) fmap0::"'a \<Rightarrow> Set('a)"
  where "fmap0 \<equiv> \<Q>"
abbreviation(input) fmap1::"('a \<Rightarrow> 'b) \<Rightarrow> Set('a) \<Rightarrow> Set('b)"
  where "fmap1 \<equiv> image"
abbreviation(input) fmap2::"('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> (Set('a) \<Rightarrow> Set('b) \<Rightarrow> Set('c))"
  where "fmap2 \<equiv> image\<^sub>2"
abbreviation(input) fmap3::"('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> (Set('a) \<Rightarrow> Set('b) \<Rightarrow> Set('c) \<Rightarrow> Set('d))"
  where "fmap3 \<equiv> image\<^sub>3"
\<comment> \<open>...and so on\<close>

text \<open>Functor's "unit" (monad's "return" resp. applicative's "pure") corresponds to the nullary case.\<close>
abbreviation "unit \<equiv> fmap0"
text \<open>Functor's classic "fmap" corresponds to the unary case.\<close>
abbreviation "fmap \<equiv> fmap1"


subsection \<open>Applicative\<close>

abbreviation(input) ap0::"Set('b) \<Rightarrow> Set('b)"
  where "ap0 \<equiv> fmap1 \<^bold>I" \<comment> \<open>ie. \<open>\<^bold>A\<close>\<close>
abbreviation(input) ap1::"Set('a \<Rightarrow> 'b) \<Rightarrow> Set('a) \<Rightarrow> Set('b)"
  where "ap1 \<equiv> fmap2 \<^bold>I"
abbreviation(input) ap2::"Set('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> (Set('a) \<Rightarrow> Set('b) \<Rightarrow> Set('c))"
  where "ap2 \<equiv> fmap3 \<^bold>I"
\<comment> \<open>...and so on\<close>

text \<open>Applicative's classic "ap" corresponds to the unary case.\<close>
abbreviation "ap \<equiv> ap1"
abbreviation(input) apr :: "Set('a) \<Rightarrow> Set('a \<Rightarrow> 'b) \<Rightarrow> Set('b)"(infixl "*>" 54)
  where "a *> f \<equiv> ap f a"  \<comment> \<open>convenient "pipeline notation"\<close>

text \<open>Indeed, we have:\<close>
lemma "ap0 = \<^bold>A" unfolding all_defs by simp
lemma "ap = intoRel \<ggreater> rightImage"  unfolding all_defs by blast
lemma "ap = (image image) \<ggreater> \<Union>\<^sup>r" unfolding all_defs by blast
\<comment> \<open>...and so on\<close>

text \<open>Check that applicative operations satisfy the corresponding laws.\<close>
lemma ap_identity:    "x *> (unit \<^bold>I) = x" unfolding all_defs by simp
lemma ap_composition: "w *> (v *> (u *> (unit \<^bold>B))) = (w *> v) *> u" unfolding all_defs by fast
lemma ap_homomorphism: "(unit x) *> (unit f) = unit (f x)" unfolding all_defs by simp
lemma ap_interchange: "(unit x) *> f = f *> unit (\<^bold>T x)" unfolding all_defs by simp


subsection \<open>Monad\<close>

text \<open>In fact (m-ary versions of) rightImage corresponds to (m-ary versions of) bindr.\<close>
abbreviation(input) bindr1::"('a \<Rightarrow> Set('b)) \<Rightarrow> Set('a) \<Rightarrow> Set('b)"
  where "bindr1 \<equiv> rightImage" \<comment> \<open>bind-reversed\<close>
abbreviation(input) bindr2::"('a \<Rightarrow> 'b \<Rightarrow> Set('c)) \<Rightarrow> (Set('a) \<Rightarrow> Set('b) \<Rightarrow> Set('c))"
  where "bindr2 \<equiv> rightImage\<^sub>2"
abbreviation(input) bindr3::"('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> Set('d)) \<Rightarrow> (Set('a) \<Rightarrow> Set('b) \<Rightarrow> Set('c) \<Rightarrow> Set('d))"
  where "bindr3 \<equiv> rightImage\<^sub>3"
\<comment> \<open>...and so on\<close>

text \<open>Monad's usual "bind" corresponds to the (reversed) unary case, and gets its customary notation.\<close>
abbreviation "bindr \<equiv> bindr1"
abbreviation(input) bind::"Set('a) \<Rightarrow> ('a \<Rightarrow> Set('b)) \<Rightarrow> Set('b)" (infixl "\<bind>" 54)
  where "a \<bind> f \<equiv> bindr f a"

text \<open>fmap can be stated in terms of (reversed) bind and unit...\<close>
lemma "fmap = (\<^bold>B \<ggreater>\<^sub>2 bindr) unit" unfolding all_defs ..
text \<open>... and ap in terms of bind and fmap\<close>
lemma "ap = \<^bold>B\<^sub>1\<^sub>1 bind \<^bold>I (\<^bold>C fmap)" unfolding all_defs by blast

text \<open>The so-called "monad laws". They guarantee that term operations compose reliably.\<close>
lemma monad_unit1: "(unit x \<bind> f) = f x" unfolding all_defs by simp  \<comment> \<open>left identity\<close>
lemma monad_unit2: "(x \<bind> unit) = x" unfolding all_defs by simp      \<comment> \<open>right identity\<close>
lemma monad_assoc: "((x \<bind> f) \<bind> g) = (x \<bind> (\<lambda>z. f z \<bind> g))" unfolding all_defs by auto \<comment> \<open>associativity\<close>


text \<open>Monad's "join" corresponds in fact to big-union.\<close>
abbreviation(input) join::"Set(Set('a)) \<Rightarrow> Set('a)"
  where "join  \<equiv> \<Union>"

text \<open>Recalling that\<close>
lemma "join = bindr \<^bold>I" unfolding all_defs by metis

text \<open>We extrapolate to obtain some interesting interrelations, for different arities\<close>
lemma "ap0 \<ggreater> join = bindr1 \<^bold>I" unfolding all_defs by metis
lemma "ap1 \<ggreater>\<^sub>2 join = bindr2 \<^bold>I" unfolding all_defs by metis
lemma "ap2 \<ggreater>\<^sub>3 join = bindr3 \<^bold>I" unfolding all_defs by metis

text \<open>Similarly, we can define bindr in terms of join and fmap, for different arities\<close>
lemma "bindr1 = fmap1 \<ggreater>\<^sub>2 join" unfolding all_defs by metis
lemma "bindr2 = fmap2 \<ggreater>\<^sub>3 join" unfolding all_defs by metis
lemma "bindr3 = fmap3 \<ggreater>\<^sub>4 join" unfolding all_defs by metis

text \<open>Moreover, recalling that\<close>
lemma "ap F A = join (fmap (\<lambda>f. fmap f A) F)" unfolding all_defs by blast 

text \<open>We can extrapolate to define ap in terms of join and fmap\<close> (*TODO: for different arities*)
lemma "ap1 = ((\<^bold>C \<ggreater> (\<ggreater>) \<ggreater>\<^sub>2 \<^bold>C) fmap fmap) \<ggreater>\<^sub>2 join" unfolding all_defs by blast


subsection \<open>Pipelines\<close>

subsubsection \<open>Arrows\<close>

text \<open>Monadic (aka. Kleisli) arrows correspond to relations\<close>
term "(m :: 'a \<Rightarrow> Set('b)) :: Rel('a,'b)"
text \<open>Applicative (aka. static) arrows correspond to function-sets (sets of functions)\<close>
term "a :: Set('a \<Rightarrow> 'b)"

text \<open>Takes a plain function and disguises it as a monadic arrow.\<close>
abbreviation(input) asArrowM::"('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> Set('b))"
  where "asArrowM \<equiv> asRel"

text \<open>Takes an applicative arrow and transforms it into a monadic arrow.\<close>
abbreviation(input) intoArrowM::"Set('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> Set('b))"
  where "intoArrowM \<equiv> intoRel"
text \<open>Takes a monadic arrow and transforms it into an applicative arrow.\<close>
abbreviation(input) intoArrowA::"('a \<Rightarrow> Set('b)) \<Rightarrow> Set('a \<Rightarrow> 'b)"
  where "intoArrowA \<equiv> intoFunSet"

text \<open>Note that\<close>
lemma "ap = intoArrowM \<ggreater> bindr" unfolding all_defs by fast


subsubsection \<open>Functional composition\<close>

text \<open>Quickly recall, again, that for the case of plain functions, we have:\<close>
term "(|>) :: 'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b"                  \<comment> \<open>reversed application\<close>
term "(\<ggreater>)  :: 'e-Env('a) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'e-Env('b)"  \<comment> \<open>reversed composition\<close>

text \<open>Composition is associative and suitably interrelates with application to build pipelines.\<close>
lemma "f \<ggreater> (g \<ggreater> h) = (f \<ggreater> g) \<ggreater> h" unfolding comb_defs ..
lemma "(x |> f |> g |> h) = (x |> f \<ggreater> g \<ggreater> h)" unfolding comb_defs ..

text \<open>Interrelation between application and composition.\<close>
lemma "(\<ggreater>) = (\<lambda>f g x. x |> f |> g)" unfolding comb_defs ..
lemma "\<^bold>A = \<^bold>B \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>B = \<^bold>D \<^bold>A" unfolding comb_defs ..


subsubsection \<open>Monadic composition\<close>

text \<open>Thus, monadic (aka. Kleisli-) composition is to "bindr" as functional composition is to application.\<close>
abbreviation(input) mcomp::"('b \<Rightarrow> Set('c)) \<Rightarrow> ('a \<Rightarrow> Set('b)) \<Rightarrow> ('a \<Rightarrow> Set('c))" 
  where "mcomp \<equiv> \<^bold>D bindr"
abbreviation(input) mcomp' (infixr "\<Zfinj>" 56) \<comment> \<open>reversed monadic composition, aka. the fish operator ">=>"\<close>
  where "f \<Zfinj> g \<equiv> mcomp g f"

lemma "f \<Zfinj> g = (\<lambda>x. f x \<bind> g)" unfolding comb_defs ..

text \<open>In the case of Set monad, Kleisli composition correspond to relation-composition.\<close>
lemma "(\<Zfinj>) = (;)"   unfolding all_defs by metis

text \<open>Note the corresponding types:\<close>
term "(\<bind>) :: Set('a) \<Rightarrow> ('a \<Rightarrow> Set('b)) \<Rightarrow> Set('b)"
term "(\<Zfinj>)  :: ('a \<Rightarrow> Set('b)) \<Rightarrow> ('b \<Rightarrow> Set('c)) \<Rightarrow> ('a \<Rightarrow> Set('c))"

text \<open>As expected, monadic composition is associative and suitably interrelates with bind to build pipelines:\<close>
lemma "f \<Zfinj> (g \<Zfinj> h) = (f \<Zfinj> g) \<Zfinj> h" unfolding all_defs by auto
lemma "(x \<bind> f \<bind> g \<bind> h) = (x \<bind> f \<Zfinj> g \<Zfinj> h)" unfolding all_defs by auto

text \<open>Bind in terms of monadic composition\<close>
lemma "bindr = (\<Zfinj>) \<^bold>I" unfolding comb_defs ..
lemma "(\<bind>) = ((\<Zfinj>) \<ggreater> \<^bold>C) \<^bold>I" unfolding comb_defs ..


subsubsection \<open>Applicative composition\<close>

text \<open>Analogously, we can introduce applicative composition.\<close>
abbreviation(input) acomp::"Set('b \<Rightarrow> 'c) \<Rightarrow> Set('a \<Rightarrow> 'b) \<Rightarrow> Set('a \<Rightarrow> 'c)" 
  where "acomp \<equiv> (\<^bold>D (\<ggreater>\<^sub>2) intoArrowM ap) \<ggreater>\<^sub>2 intoArrowA"
abbreviation(input) acomp' (infixr "\<Zinj>" 56) \<comment> \<open>reversed applicative composition\<close>
  where "f \<Zinj> g \<equiv> acomp g f"

lemma "f \<Zinj> g = intoArrowA (intoArrowM f \<ggreater> ap g)" unfolding comb_defs ..
lemma "f \<Zinj> g = intoArrowA (\<lambda>x. (intoArrowM f x) *> g)" unfolding comb_defs ..

text \<open>Note the corresponding types:\<close>
term "(*>) :: Set('a) \<Rightarrow> Set('a \<Rightarrow> 'b) \<Rightarrow> Set('b)"
term "(\<Zinj>) :: Set('a \<Rightarrow> 'b) \<Rightarrow> Set('b \<Rightarrow> 'c) \<Rightarrow> Set('a \<Rightarrow> 'c)"

text \<open>Applicative composition is associative and suitably interrelates with ap to build pipelines:\<close>
lemma "f \<Zinj> (g \<Zinj> h) = (f \<Zinj> g) \<Zinj> h" unfolding all_defs apply (rule ext)+ apply auto apply (metis B1_comb_def) by (metis o_apply)
lemma "(x *> f *> g *> h) = (x *> f \<Zinj> g \<Zinj> h)" unfolding all_defs apply (rule ext)+ apply auto apply fastforce by metis

end