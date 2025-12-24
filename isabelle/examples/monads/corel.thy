theory corel
  imports env coset
begin

(*Disambiguate notation*)
no_notation
  env.apr  (infixl "*>" 54) and env.bind  (infixl "\<bind>" 54) and env.mcomp' (infixr "\<Zfinj>" 56) and env.acomp' (infixr "\<Zinj>" 56) and
  coset.apr  (infixl "*>" 54) and coset.bind  (infixl "\<bind>" 54) and coset.mcomp' (infixr "\<Zfinj>" 56) and coset.acomp' (infixr "\<Zinj>" 56)
notation
  env.apr  (infixl "*>\<^sup>e" 54) and env.bind  (infixl "\<bind>\<^sup>e" 54) and env.mcomp' (infixr "\<Zfinj>\<^sup>e" 56) and env.acomp' (infixr "\<Zinj>\<^sup>e" 56) and
  coset.apr  (infixl "*>\<^sup>s" 54) and coset.bind  (infixl "\<bind>\<^sup>s" 54) and coset.mcomp' (infixr "\<Zfinj>\<^sup>s" 56) and coset.acomp' (infixr "\<Zinj>\<^sup>s" 56)


section \<open>Co-Relation Monad\<close>

text \<open>The \<open>Rel('a,'b)\<close> type constructor also comes with a "dual" monad structure, which merges, 
 in a sense, the environment monad with the dual of the set (aka. coset) monad.\<close>

named_theorems all_defs
declare comb_defs[all_defs] func_defs[all_defs] rel_defs[all_defs]


subsection \<open>Functor\<close>

abbreviation(input) fmap0::"'a \<Rightarrow>  Rel('b,'a)"
  where "fmap0 \<equiv> coset.fmap0 \<ggreater> env.fmap0"
abbreviation(input) fmap1::"('a \<Rightarrow> 'b) \<Rightarrow> Rel('c,'a) \<Rightarrow> Rel('c,'b)"
  where "fmap1 \<equiv> coset.fmap1 \<ggreater> env.fmap1"
abbreviation(input) fmap2::"('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> (Rel('d,'a) \<Rightarrow> Rel('d,'b) \<Rightarrow> Rel('d,'c))"
  where "fmap2 \<equiv> coset.fmap2 \<ggreater> env.fmap2"
abbreviation(input) fmap3::"('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> (Rel('e,'a) \<Rightarrow> Rel('e,'b) \<Rightarrow> Rel('e,'c) \<Rightarrow> Rel('e,'d))"
  where "fmap3 \<equiv> coset.fmap3 \<ggreater> env.fmap3"
\<comment> \<open>...and so on\<close>

lemma "fmap0 f A = \<lbrace>f\<rbrace>" unfolding all_defs ..
lemma "fmap1 f A = (\<lambda>x y. \<forall>a. f a = y \<rightarrow> A x a)" unfolding all_defs ..
lemma "fmap2 f A B = (\<lambda>y z. \<forall>a b. f a b = z \<rightarrow> A y a \<or> B y b)" unfolding all_defs ..
\<comment> \<open>...and so on\<close>

text \<open>Functor's "unit" (monad's "return" resp. applicative's "pure") corresponds to the nullary case.\<close>
abbreviation unit where "unit \<equiv> fmap0"
text \<open>Functor's classic "fmap" corresponds to the unary case.\<close>
abbreviation fmap where "fmap \<equiv> fmap1"


subsection \<open>Applicative\<close>

abbreviation(input) ap0::"Rel('b,'a) \<Rightarrow> Rel('b,'a)"
  where "ap0 \<equiv> env.fmap1 coset.ap0" \<comment> \<open>ie. \<open>\<^bold>A\<close>\<close>
abbreviation(input) ap1::"Rel('c,'a \<Rightarrow> 'b) \<Rightarrow> Rel('c,'a) \<Rightarrow> Rel('c,'b)"
  where "ap1 \<equiv> env.fmap2 coset.ap1"
abbreviation(input) ap2::"Rel('d,'a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> (Rel('d,'a) \<Rightarrow> Rel('d,'b) \<Rightarrow> Rel('d,'c))"
  where "ap2 \<equiv> env.fmap3 coset.ap2"
\<comment> \<open>...and so on\<close>

text \<open>Applicative's classic "ap" corresponds to the unary case.\<close>
notation ap1 ("ap")
abbreviation(input) apr :: "Rel('c,'a) \<Rightarrow> Rel('c,'a \<Rightarrow> 'b) \<Rightarrow> Rel('c,'b)"(infixl "*>" 54)
  where "a *> f \<equiv> ap f a"  \<comment> \<open>convenient "pipeline notation"\<close>

text \<open>Indeed, we have:\<close>
lemma "ap0 = fmap1 \<^bold>I" unfolding all_defs ..
lemma "ap1 = fmap2 \<^bold>I" unfolding all_defs ..
lemma "ap2 = fmap3 \<^bold>I" unfolding all_defs ..
\<comment> \<open>...and so on\<close>

text \<open>Check that applicative operations satisfy the corresponding laws.\<close>
lemma ap_identity:    "x *> (unit \<^bold>I) = x" unfolding all_defs by simp
lemma ap_composition: "w *> (v *> (u *> (unit \<^bold>B))) = (w *> v) *> u" unfolding all_defs by fast
lemma ap_homomorphism: "(unit x) *> (unit f) = unit (f x)" unfolding all_defs by auto
lemma ap_interchange: "(unit x) *> f = f *> unit (\<^bold>T x)" unfolding all_defs by auto


subsection \<open>Monad\<close>

abbreviation(input) bindr1::"('a \<Rightarrow> Rel('c,'b)) \<Rightarrow> Rel('c,'a) \<Rightarrow> Rel('c,'b)"
  where "bindr1 \<equiv> \<^bold>C \<ggreater> env.fmap2 coset.bindr1" \<comment> \<open>bind-reversed\<close>
abbreviation(input) bindr2::"('a \<Rightarrow> 'b \<Rightarrow> Rel('d,'c)) \<Rightarrow> Rel('d,'a) \<Rightarrow> Rel('d,'b) \<Rightarrow> Rel('d,'c)"
  where "bindr2 \<equiv> \<^bold>R\<^sub>3 \<ggreater> env.fmap3 coset.bindr2"
abbreviation(input) bindr3::"('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> Rel('e,'d)) \<Rightarrow> Rel('e,'a) \<Rightarrow> Rel('e,'b) \<Rightarrow> Rel('e,'c) \<Rightarrow> Rel('e,'d)"
  where "bindr3 \<equiv> \<^bold>R\<^sub>4 \<ggreater> env.fmap4 coset.bindr3" 
\<comment> \<open>...and so on\<close>

text \<open>Monad's usual "bind" corresponds to the (reversed) unary case, and gets its customary notation.\<close>
abbreviation bindr where "bindr \<equiv> bindr1"
abbreviation(input) bind::"Rel('c,'a) \<Rightarrow> ('a \<Rightarrow> Rel('c,'b)) \<Rightarrow> Rel('c,'b)" (infixl "\<bind>" 54)
  where "a \<bind> f \<equiv> bindr f a"

text \<open>fmap can be stated in terms of (reversed) bind and unit...\<close>
lemma "fmap = (\<^bold>B \<ggreater>\<^sub>2 bindr) unit" unfolding all_defs by simp
text \<open>... and ap in terms of bind and fmap\<close>
lemma "ap = \<^bold>B\<^sub>1\<^sub>1 bind \<^bold>I (\<^bold>C fmap)" unfolding all_defs by blast

text \<open>The so-called "monad laws". They guarantee that term operations compose reliably.\<close>
lemma monad_unit1: "(unit x \<bind> f) = f x" unfolding all_defs by auto  \<comment> \<open>left identity\<close>
lemma monad_unit2: "(x \<bind> unit) = x" unfolding all_defs by simp      \<comment> \<open>right identity\<close>
lemma monad_assoc: "((x \<bind> f) \<bind> g) = (x \<bind> (\<lambda>z. (f z) \<bind> g))" unfolding all_defs by auto \<comment> \<open>associativity\<close>


abbreviation(input) join::"Rel('c,Rel('c,'a)) \<Rightarrow> Rel('c,'a)"
  where "join \<equiv> env.fmap (coset.intoArrowM \<ggreater>\<^sub>2 coset.join) \<ggreater> env.join"

text \<open>Recalling that\<close>
lemma "join = bindr \<^bold>I" unfolding all_defs by metis

text \<open>We extrapolate to obtain some interesting interrelations, for different arities\<close>
lemma "ap0 \<ggreater> join = bindr1 \<^bold>I" unfolding all_defs by metis
lemma "ap1 \<ggreater>\<^sub>2 join = bindr2 \<^bold>I" unfolding all_defs by metis
lemma "ap2 \<ggreater>\<^sub>3 join = bindr3 \<^bold>I" unfolding all_defs by fast

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

text \<open>Monadic (aka. Kleisli) arrows correspond to ternary relations\<close>
term "(m :: 'a \<Rightarrow> Rel('b,'c)) :: Rel\<^sub>3('a,'b,'c)"
text \<open>Applicative (aka. static) arrows correspond to indexed function-sets (sets of functions)\<close>
term "a :: Rel('b,'a \<Rightarrow> 'c)"

text \<open>Takes a plain function and disguises it as a monadic arrow.\<close>
abbreviation(input) asArrowM::"('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> Rel('b,'c))"
  where "asArrowM \<equiv> coset.asArrowM \<ggreater> env.asArrowM"

text \<open>Takes an applicative arrow and transforms it into a monadic arrow.\<close>
abbreviation(input) intoArrowM::"Rel('b,'a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> Rel('b,'c))"
  where "intoArrowM \<equiv> (env.fmap \<ggreater>\<^sub>2 env.intoArrowM) coset.intoArrowM"
text \<open>Takes a monadic arrow and transforms it into an applicative arrow.\<close>
abbreviation(input) intoArrowA::"('a \<Rightarrow> Rel('b,'c)) \<Rightarrow> Rel('b,'a \<Rightarrow> 'c)"
  where "intoArrowA \<equiv> env.intoArrowA \<ggreater>\<^sub>2 coset.intoArrowA"

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
abbreviation(input) mcomp::"('b \<Rightarrow> Rel('w,'c)) \<Rightarrow> ('a \<Rightarrow> Rel('w,'b)) \<Rightarrow> ('a \<Rightarrow> Rel('w,'c))" 
  where "mcomp \<equiv> \<^bold>D bindr"
abbreviation(input) mcomp' (infixr "\<Zfinj>" 56) \<comment> \<open>reversed monadic composition, aka. the fish operator ">=>"\<close>
  where "f \<Zfinj> g \<equiv> mcomp g f"

lemma "f \<Zfinj> g = (\<lambda>x. (f x) \<bind> g)" unfolding comb_defs ..

text \<open>In fact, Kleisli composition can be used to model (dual)composition of ternary relations.\<close>
lemma "R\<^sub>1 \<Zfinj> R\<^sub>2 = R\<^sub>1 \<Zfinj> R\<^sub>2" unfolding all_defs .. \<comment> \<open>check unfolded term\<close>

text \<open>Note the corresponding types:\<close>
term "(\<bind>) :: Rel('w,'a) \<Rightarrow> ('a \<Rightarrow> Rel('w,'b)) \<Rightarrow> Rel('w,'b)"
term "(\<Zfinj>)  :: ('a \<Rightarrow> Rel('w,'b)) \<Rightarrow> ('b \<Rightarrow> Rel('w,'c)) \<Rightarrow> ('a \<Rightarrow> Rel('w,'c))"

text \<open>As expected, monadic composition is associative and suitably interrelates with bind to build pipelines:\<close>
lemma "f \<Zfinj> (g \<Zfinj> h) = (f \<Zfinj> g) \<Zfinj> h" unfolding all_defs by fast
lemma "(x \<bind> f \<bind> g \<bind> h) = (x \<bind> f \<Zfinj> g \<Zfinj> h)" unfolding all_defs by fast

text \<open>Bind in terms of monadic composition\<close>
lemma "bindr = (\<Zfinj>) \<^bold>I" unfolding comb_defs ..
lemma "(\<bind>) = ((\<Zfinj>) \<ggreater> \<^bold>C) \<^bold>I" unfolding comb_defs ..


subsubsection \<open>Applicative composition\<close>

text \<open>Analogously, we can introduce applicative composition.\<close>
abbreviation(input) acomp::"Rel('w, 'b \<Rightarrow> 'c) \<Rightarrow> Rel('w, 'a \<Rightarrow> 'b) \<Rightarrow> Rel('w, 'a \<Rightarrow> 'c)" 
  where "acomp \<equiv> (\<^bold>D (\<ggreater>\<^sub>2) intoArrowM ap) \<ggreater>\<^sub>2 intoArrowA"
abbreviation(input) acomp' (infixr "\<Zinj>" 56) \<comment> \<open>reversed applicative composition\<close>
  where "f \<Zinj> g \<equiv> acomp g f"

lemma "f \<Zinj> g = intoArrowA (intoArrowM f \<ggreater> ap g)" unfolding comb_defs ..
lemma "f \<Zinj> g = intoArrowA (\<lambda>x. (intoArrowM f x) *> g)" unfolding rel_defs  comb_defs ..

text \<open>Note the corresponding types:\<close>
term "(*>) :: Rel('c,'a) \<Rightarrow> Rel('c,'a \<Rightarrow> 'b) \<Rightarrow> Rel('c,'b)"
term "(\<Zinj>) :: Rel('w,'a \<Rightarrow> 'b) \<Rightarrow> Rel('w,'b \<Rightarrow> 'c) \<Rightarrow> Rel('w,'a \<Rightarrow> 'c)"

text \<open>Applicative composition is associative and suitably interrelates with ap to build pipelines:\<close>
lemma "f \<Zinj> (g \<Zinj> h) = (f \<Zinj> g) \<Zinj> h" unfolding all_defs apply (rule ext)+ apply auto apply (metis B1_comb_def) by (metis o_apply)
lemma "(x *> f *> g *> h) = (x *> f \<Zinj> g \<Zinj> h)" unfolding all_defs apply (rule ext)+ apply auto by (fastforce | metis)+


end