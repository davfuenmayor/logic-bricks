theory rel
imports env set
begin

(*Disambiguate notation*)
no_notation
  env.apr  (infixl "\<ggreater>" 54) and env.bind  (infixl "\<bind>" 54) and env.mcomp' (infixr "\<Zfinj>" 56) and env.acomp' (infixr "\<Zinj>" 56) and
  set.apr  (infixl "\<ggreater>" 54) and set.bind  (infixl "\<bind>" 54) and set.mcomp' (infixr "\<Zfinj>" 56) and set.acomp' (infixr "\<Zinj>" 56)
notation
  env.apr  (infixl "\<ggreater>\<^sup>e" 54) and env.bind  (infixl "\<bind>\<^sup>e" 54) and env.mcomp' (infixr "\<Zfinj>\<^sup>e" 56) and env.acomp' (infixr "\<Zinj>\<^sup>e" 56) and
  set.apr  (infixl "\<ggreater>\<^sup>s" 54) and set.bind  (infixl "\<bind>\<^sup>s" 54) and set.mcomp' (infixr "\<Zfinj>\<^sup>s" 56) and set.acomp' (infixr "\<Zinj>\<^sup>s" 56)


section \<open>Relation Monad\<close>

text \<open>The \<open>Rel('a,'b)\<close> type constructor also comes with a monad structure, which merges, 
 in a sense, the environment monad with the set monad.\<close>

named_theorems all_defs
declare comb_defs[all_defs] func_defs[all_defs] rel_defs[all_defs]


subsection \<open>Functor\<close>

abbreviation(input) fmap0::"'a \<Rightarrow>  Rel('b,'a)"
  where "fmap0 \<equiv> env.fmap0 \<circ> set.fmap0"
abbreviation(input) fmap1::"('a \<Rightarrow> 'b) \<Rightarrow> Rel('c,'a) \<Rightarrow> Rel('c,'b)"
  where "fmap1 \<equiv> env.fmap1 \<circ> set.fmap1"
abbreviation(input) fmap2::"('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> (Rel('d,'a) \<Rightarrow> Rel('d,'b) \<Rightarrow> Rel('d,'c))"
  where "fmap2 \<equiv> env.fmap2 \<circ> set.fmap2"
abbreviation(input) fmap3::"('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> (Rel('e,'a) \<Rightarrow> Rel('e,'b) \<Rightarrow> Rel('e,'c) \<Rightarrow> Rel('e,'d))"
  where "fmap3 \<equiv> env.fmap3 \<circ> set.fmap3"
\<comment> \<open>...and so on\<close>

text \<open>Functor's "unit" (monad's "return" resp. applicative's "pure") corresponds to the nullary case.\<close>
abbreviation unit where "unit \<equiv> fmap0"
text \<open>Functor's classic "fmap" corresponds to the unary case.\<close>
abbreviation fmap where "fmap \<equiv> fmap1"


subsection \<open>Applicative\<close>

abbreviation(input) ap0::"Rel('b,'a) \<Rightarrow> Rel('b,'a)"
  where "ap0 \<equiv> env.fmap1 set.ap0" \<comment> \<open>ie. \<open>\<^bold>A\<close>\<close>
abbreviation(input) ap1::"Rel('c,'a \<Rightarrow> 'b) \<Rightarrow> Rel('c,'a) \<Rightarrow> Rel('c,'b)"
  where "ap1 \<equiv> env.fmap2 set.ap1"
abbreviation(input) ap2::"Rel('d,'a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> (Rel('d,'a) \<Rightarrow> Rel('d,'b) \<Rightarrow> Rel('d,'c))"
  where "ap2 \<equiv> env.fmap3 set.ap2"
\<comment> \<open>...and so on\<close>

text \<open>Applicative's classic "ap" corresponds to the unary case.\<close>
notation ap1 ("ap")
abbreviation(input) apr :: "Rel('c,'a) \<Rightarrow> Rel('c,'a \<Rightarrow> 'b) \<Rightarrow> Rel('c,'b)"(infixl "\<ggreater>" 54)
  where "a \<ggreater> f \<equiv> ap f a"  \<comment> \<open>convenient "pipeline notation"\<close>

text \<open>Indeed, we have:\<close>
lemma "ap0 = fmap1 \<^bold>I" unfolding all_defs ..
lemma "ap1 = fmap2 \<^bold>I" unfolding all_defs ..
lemma "ap2 = fmap3 \<^bold>I" unfolding all_defs ..
\<comment> \<open>...and so on\<close>

text \<open>More explicitly\<close>
lemma "ap0 = \<^bold>A" unfolding all_defs by simp
lemma "ap1 = \<^bold>\<Phi>\<^sub>2\<^sub>1 (rightImage \<circ> intoRel)" unfolding all_defs by metis
lemma "ap1 = (\<lambda>g\<^sub>1 g\<^sub>2 x c. \<exists>a b. a b = c \<and> g\<^sub>1 x a \<and> g\<^sub>2 x b)" unfolding all_defs ..
lemma "ap2 = (\<lambda>g\<^sub>1 g\<^sub>2 g\<^sub>3 x d. \<exists>a b c. a b c = d \<and> g\<^sub>1 x a \<and> g\<^sub>2 x b \<and> g\<^sub>3 x c)" unfolding all_defs ..
\<comment> \<open>...and so on\<close>

text \<open>Check that applicative operations satisfy the corresponding laws.\<close>
lemma ap_identity:    "x \<ggreater> (unit \<^bold>I) = x" unfolding all_defs by simp
lemma ap_composition: "w \<ggreater> (v \<ggreater> (u \<ggreater> (unit \<^bold>B))) = (w \<ggreater> v) \<ggreater> u" unfolding all_defs by fast
lemma ap_homomorphism: "(unit x) \<ggreater> (unit f) = unit (f x)" unfolding all_defs by simp
lemma ap_interchange: "(unit x) \<ggreater> f = f \<ggreater> (unit (\<^bold>T x))" unfolding all_defs by simp


subsection \<open>Monad\<close>

abbreviation(input) bindr1::"('a \<Rightarrow> Rel('c,'b)) \<Rightarrow> Rel('c,'a) \<Rightarrow> Rel('c,'b)"
  where "bindr1 \<equiv> (env.fmap2 set.bindr1) \<circ> \<^bold>C" \<comment> \<open>bind-reversed\<close>
abbreviation(input) bindr2::"('a \<Rightarrow> 'b \<Rightarrow> Rel('d,'c)) \<Rightarrow> Rel('d,'a) \<Rightarrow> Rel('d,'b) \<Rightarrow> Rel('d,'c)"
  where "bindr2 \<equiv> (env.fmap3 set.bindr2) \<circ> \<^bold>R"
abbreviation(input) bindr3::"('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> Rel('e,'d)) \<Rightarrow> Rel('e,'a) \<Rightarrow> Rel('e,'b) \<Rightarrow> Rel('e,'c) \<Rightarrow> Rel('e,'d)"
  where "bindr3 \<equiv> (env.fmap4 set.bindr3) \<circ> \<^bold>C\<^sub>2\<^sub>3\<^sub>4\<^sub>1" 
\<comment> \<open>...and so on\<close>

text \<open>Monad's usual "bind" corresponds to the (reversed) unary case, and gets its customary notation.\<close>
abbreviation bindr where "bindr \<equiv> bindr1"
abbreviation(input) bind::"Rel('c,'a) \<Rightarrow> ('a \<Rightarrow> Rel('c,'b)) \<Rightarrow> Rel('c,'b)" (infixl "\<bind>" 54)
  where "a \<bind> f \<equiv> bindr f a"

text \<open>fmap can be stated in terms of (reversed) bind and unit...\<close>
lemma "fmap = (bindr \<circ>\<^sub>2 \<^bold>B) unit" unfolding all_defs ..
text \<open>... and ap in terms of bind and fmap\<close>
lemma "ap = \<^bold>B\<^sub>1\<^sub>1 bind \<^bold>I (\<^bold>C fmap)" unfolding all_defs by blast

text \<open>The so-called "monad laws". They guarantee that term operations compose reliably.\<close>
lemma monad_unit1: "(unit x \<bind> f) = f x" unfolding all_defs by simp  \<comment> \<open>left identity\<close>
lemma monad_unit2: "(x \<bind> unit) = x" unfolding all_defs by simp      \<comment> \<open>right identity\<close>
lemma monad_assoc: "((x \<bind> f) \<bind> g) = (x \<bind> (\<lambda>z. (f z) \<bind> g))" unfolding all_defs by auto \<comment> \<open>associativity\<close>


abbreviation(input) join::"Rel('c,Rel('c,'a)) \<Rightarrow> Rel('c,'a)"
  where "join \<equiv>  env.join \<circ> (env.fmap (set.join \<circ>\<^sub>2 set.intoArrowM))"

lemma "join = env.join \<circ> (env.fmap (\<Union> \<circ>\<^sub>2 intoRel))" unfolding all_defs by metis
lemma "join = env.join \<circ> (env.fmap \<Union>\<^sup>r)" unfolding all_defs by metis
lemma "join =  \<^bold>W \<circ> (\<^bold>B \<Union>\<^sup>r)"  unfolding all_defs ..

text \<open>Recalling that\<close>
lemma "join = bindr \<^bold>I" unfolding all_defs by metis

text \<open>We extrapolate to obtain some interesting interrelations, for different arities\<close>
lemma "join \<circ> ap0 = bindr1 \<^bold>I"  unfolding all_defs by metis
lemma "join \<circ>\<^sub>2 ap1 = bindr2 \<^bold>I" unfolding all_defs by metis
lemma "join \<circ>\<^sub>3 ap2 = bindr3 \<^bold>I" unfolding all_defs by metis

text \<open>Similarly, we can define bindr in terms of join and fmap, for different arities\<close>
lemma "bindr1 = join \<circ>\<^sub>2 fmap1" unfolding all_defs by metis
lemma "bindr2 = join \<circ>\<^sub>3 fmap2" unfolding all_defs by metis
lemma "bindr3 = join \<circ>\<^sub>4 fmap3" unfolding all_defs by metis

text \<open>Moreover, recalling that\<close>
lemma "ap F A = join (fmap (\<lambda>f. fmap f A) F)" unfolding all_defs by blast 

text \<open>We can extrapolate to define ap in terms of join and fmap\<close> (*TODO: for different arities*)
lemma "ap1 = join \<circ>\<^sub>2 ((\<^bold>C \<circ>\<^sub>2 (;) \<circ> \<^bold>C) fmap fmap)" unfolding all_defs by blast


subsection \<open>Pipelines\<close>

subsubsection \<open>Arrows\<close>

text \<open>Monadic (aka. Kleisli) arrows correspond to ternary relations\<close>
term "(m :: 'a \<Rightarrow> Rel('b,'c)) :: Rel\<^sub>3('a,'b,'c)"
text \<open>Applicative (aka. static) arrows correspond to indexed function-sets (sets of functions)\<close>
term "a :: Rel('b,'a \<Rightarrow> 'c)"

text \<open>Takes a plain function and disguises it as a monadic arrow.\<close>
abbreviation(input) asArrowM::"('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> Rel('b,'c))"
  where "asArrowM \<equiv> env.asArrowM \<circ> set.asArrowM"

text \<open>Takes an applicative arrow and transforms it into a monadic arrow.\<close>
abbreviation(input) intoArrowM::"Rel('b,'a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> Rel('b,'c))"
  where "intoArrowM \<equiv> (env.intoArrowM \<circ>\<^sub>2 env.fmap) set.intoArrowM"
text \<open>Takes a monadic arrow and transforms it into an applicative arrow.\<close>
abbreviation(input) intoArrowA::"('a \<Rightarrow> Rel('b,'c)) \<Rightarrow> Rel('b,'a \<Rightarrow> 'c)"
  where "intoArrowA \<equiv> set.intoArrowA \<circ>\<^sub>2 env.intoArrowA"

lemma "intoArrowM = (\<^bold>C \<circ>\<^sub>2 \<^bold>B) intoRel" unfolding all_defs by metis
lemma "intoArrowA = intoFunSet \<circ>\<^sub>2 \<^bold>C" unfolding all_defs by metis

text \<open>Note that\<close>
lemma "ap = bindr \<circ> intoArrowM" unfolding all_defs by fast


subsubsection \<open>Functional composition\<close>

text \<open>Quickly recall, again, that for the case of plain functions, we have:\<close>
term "(|>) :: 'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b"                  \<comment> \<open>reversed application\<close>
term "(;)  :: 'e-Env('a) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'e-Env('b)"  \<comment> \<open>reversed composition\<close>

text \<open>Composition is associative and suitably interrelates with application to build pipelines.\<close>
lemma "f ; (g ; h) = (f ; g) ; h" unfolding comb_defs ..
lemma "(x |> f |> g |> h) = (x |> f ; g ; h)" unfolding comb_defs ..

text \<open>Interrelation between application and composition.\<close>
lemma "f ; g = (\<lambda>x. f x |> g)" unfolding comb_defs ..
lemma "(\<circ>) = (\<lambda>g f x. g @ f @ x)" unfolding comb_defs ..
lemma "(@) = (\<circ>) \<^bold>I" unfolding comb_defs ..
lemma "(\<circ>) = \<^bold>D (@)" unfolding comb_defs ..


subsubsection \<open>Monadic composition\<close>

text \<open>Thus, monadic (aka. Kleisli-) composition is to "bindr" as functional composition is to application.\<close>
abbreviation(input) mcomp::"('b \<Rightarrow> Rel('w,'c)) \<Rightarrow> ('a \<Rightarrow> Rel('w,'b)) \<Rightarrow> ('a \<Rightarrow> Rel('w,'c))" 
  where "mcomp \<equiv> \<^bold>D bindr"
abbreviation(input) mcomp' (infixr "\<Zfinj>" 56) \<comment> \<open>reversed monadic composition, aka. the fish operator ">=>"\<close>
  where "f \<Zfinj> g \<equiv> mcomp g f"

lemma "f \<Zfinj> g = (\<lambda>x. (f x) \<bind> g)" unfolding comb_defs ..

text \<open>In the case of Rel monad, Kleisli composition can be used to model composition of ternary relations.\<close>
lemma "mcomp = \<^bold>D (\<^bold>\<Phi>\<^sub>2\<^sub>1 rightImage) \<circ> \<^bold>C" unfolding all_defs ..
lemma "F \<Zfinj> G = (\<lambda>x y z. \<exists>u. F x y u \<and> G u y z)" unfolding all_defs by auto

text \<open>Note the corresponding types:\<close>
term "(\<bind>) :: Rel('w,'a) \<Rightarrow> ('a \<Rightarrow> Rel('w,'b)) \<Rightarrow> Rel('w,'b)"
term "(\<Zfinj>)  :: ('a \<Rightarrow> Rel('w,'b)) \<Rightarrow> ('b \<Rightarrow> Rel('w,'c)) \<Rightarrow> ('a \<Rightarrow> Rel('w,'c))"

text \<open>As expected, monadic composition is associative and suitably interrelates with bind to build pipelines:\<close>
lemma "f \<Zfinj> (g \<Zfinj> h) = (f \<Zfinj> g) \<Zfinj> h" unfolding all_defs by fast
lemma "(x \<bind> f \<bind> g \<bind> h) = (x \<bind> f \<Zfinj> g \<Zfinj> h)" unfolding all_defs by fast

text \<open>Bind in terms of monadic composition\<close>
lemma "bindr = (\<Zfinj>) \<^bold>I" unfolding comb_defs ..
lemma "(\<bind>) = (\<^bold>C \<circ> (\<Zfinj>)) \<^bold>I" unfolding comb_defs ..


subsubsection \<open>Applicative composition\<close>

text \<open>Analogously, we can introduce applicative composition.\<close>
abbreviation(input) acomp::"Rel('w, 'b \<Rightarrow> 'c) \<Rightarrow> Rel('w, 'a \<Rightarrow> 'b) \<Rightarrow> Rel('w, 'a \<Rightarrow> 'c)" 
  where "acomp \<equiv> intoArrowA \<circ>\<^sub>2 (\<^bold>B\<^sub>1\<^sub>0 (\<circ>\<^sub>2) ap intoArrowM)"
abbreviation(input) acomp' (infixr "\<Zinj>" 56) \<comment> \<open>reversed applicative composition\<close>
  where "f \<Zinj> g \<equiv> acomp g f"

lemma "f \<Zinj> g = intoArrowA (intoArrowM f ; ap g)" unfolding comb_defs ..
lemma "f \<Zinj> g = intoArrowA (\<lambda>x. (intoArrowM f x) \<ggreater> g)" unfolding rel_defs  comb_defs ..

text \<open>Note the corresponding types:\<close>
term "(\<ggreater>) :: Rel('c,'a) \<Rightarrow> Rel('c,'a \<Rightarrow> 'b) \<Rightarrow> Rel('c,'b)"
term "(\<Zinj>) :: Rel('w,'a \<Rightarrow> 'b) \<Rightarrow> Rel('w,'b \<Rightarrow> 'c) \<Rightarrow> Rel('w,'a \<Rightarrow> 'c)"

text \<open>Applicative composition is associative and suitably interrelates with ap to build pipelines:\<close>
lemma "f \<Zinj> (g \<Zinj> h) = (f \<Zinj> g) \<Zinj> h" unfolding all_defs apply (rule ext)+ apply auto apply (metis B1_comb_def) by (metis o_apply)
lemma "(x \<ggreater> f \<ggreater> g \<ggreater> h) = (x \<ggreater> f \<Zinj> g \<Zinj> h)" unfolding all_defs apply (rule ext)+ apply auto apply fastforce by metis


end