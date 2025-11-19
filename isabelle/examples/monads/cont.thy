theory cont
imports "../../logic_bridge"
begin

section \<open>Continuation Monad\<close>


subsection \<open>Functor\<close>

abbreviation(input) fmap0 :: "'a \<Rightarrow> ('r\<^sub>1 \<Rightarrow> 'r\<^sub>2) \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont('a)"
  where "fmap0 \<equiv> \<^bold>L (\<^bold>T \<circ>\<^sub>2 \<^bold>B\<^sub>0)"
abbreviation(input) fmap1::"('a \<Rightarrow> 'b) \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont('a) \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont('b)"
  where "fmap1 \<equiv> \<^bold>L (\<^bold>T \<circ>\<^sub>2 \<^bold>B\<^sub>1)"
abbreviation(input) fmap2::"('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont\<^sub>2('a,'b) \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont('c)"
  where "fmap2 \<equiv> \<^bold>L (\<^bold>T \<circ>\<^sub>2 \<^bold>B\<^sub>2)"
abbreviation(input) fmap3::"('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont\<^sub>3('a,'b,'c) \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont('d)"
  where "fmap3 \<equiv> \<^bold>L (\<^bold>T \<circ>\<^sub>2 \<^bold>B\<^sub>3)"
abbreviation(input) fmap4::"('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont\<^sub>4('a,'b,'c,'d) \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont('e)"
  where "fmap4 \<equiv> \<^bold>L (\<^bold>T \<circ>\<^sub>2 \<^bold>B\<^sub>4)"
\<comment> \<open>and so on...\<close>

lemma "fmap0 = (\<^bold>L \<circ> (\<^bold>C\<^bold>B\<^sub>2 \<^bold>B\<^sub>0)) \<^bold>T" unfolding comb_defs ..
lemma "fmap1 = (\<^bold>L \<circ> (\<^bold>C\<^bold>B\<^sub>2 \<^bold>B\<^sub>1)) \<^bold>T" unfolding comb_defs ..
lemma "fmap2 = (\<^bold>L \<circ> (\<^bold>C\<^bold>B\<^sub>2 \<^bold>B\<^sub>2)) \<^bold>T" unfolding comb_defs ..
lemma "fmap3 = (\<^bold>L \<circ> (\<^bold>C\<^bold>B\<^sub>2 \<^bold>B\<^sub>3)) \<^bold>T" unfolding comb_defs ..
lemma "fmap4 = (\<^bold>L \<circ> (\<^bold>C\<^bold>B\<^sub>2 \<^bold>B\<^sub>4)) \<^bold>T" unfolding comb_defs ..
\<comment> \<open>and so on...\<close>

lemma "fmap0 = (\<lambda>f k g. k (g f))" unfolding comb_defs ..
lemma "fmap1 = (\<lambda>f k g. k (g \<circ> f))" unfolding comb_defs ..
lemma "fmap2 = (\<lambda>f k g. k (g \<circ>\<^sub>2 f))" unfolding comb_defs ..
lemma "fmap3 = (\<lambda>f k g. k (g \<circ>\<^sub>3 f))" unfolding comb_defs ..
lemma "fmap4 = (\<lambda>f k g. k (g \<circ>\<^sub>4 f))" unfolding comb_defs ..
\<comment> \<open>and so on...\<close>

lemma "fmap0 f = (\<lambda>k g. (f |> g) |> k)" unfolding comb_defs ..
lemma "fmap1 f = (\<lambda>k g. (f ; g)  |> k)" unfolding comb_defs ..
lemma "fmap2 f = (\<lambda>k g. (f ;\<^sub>2 g) |> k)" unfolding comb_defs ..
lemma "fmap3 f = (\<lambda>k g. (f ;\<^sub>3 g) |> k)" unfolding comb_defs ..
lemma "fmap4 f = (\<lambda>k g. (f ;\<^sub>4 g) |> k)" unfolding comb_defs ..
\<comment> \<open>and so on...\<close>

text \<open>Functor's classic "fmap" corresponds to the unary case.\<close>
abbreviation "fmap \<equiv> fmap1"

text \<open>In contrast to the environment functor, in the case of the continuation functor, "unit" does 
 not correspond to "fmap0". We introduce "unit" for different arities as follows:\<close>
abbreviation(input) unit1::"'a \<Rightarrow> 'r-ECont('a)"
  where "unit1 \<equiv> \<^bold>T\<^sub>1"
abbreviation(input) unit2::"'a \<Rightarrow> 'b \<Rightarrow> 'r-ECont\<^sub>2('a,'b)"
  where "unit2 \<equiv> \<^bold>T\<^sub>2"
abbreviation(input) unit3::"'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'r-ECont\<^sub>3('a,'b,'c)"
  where "unit3 \<equiv> \<^bold>T\<^sub>3"
\<comment> \<open>and so on...\<close>

abbreviation "unit \<equiv> unit1"

lemma "unit = (|>)" unfolding comb_defs ..
lemma "unit = \<^bold>C \<^bold>A" unfolding comb_defs ..
lemma "unit1 = \<^bold>C fmap0 \<^bold>A" unfolding comb_defs ..
lemma "unit2 = \<^bold>V" unfolding comb_defs ..


subsection \<open>Applicative\<close>

abbreviation(input) ap0::"'r\<^sub>2,'r\<^sub>3-Cont('a) \<Rightarrow> ('r\<^sub>1 \<Rightarrow> 'r\<^sub>2) \<Rightarrow> 'r\<^sub>1,'r\<^sub>3-Cont('a)"
  where "ap0 \<equiv> ((\<^bold>C\<^bold>B\<^sub>2) \<circ> (\<^bold>C\<^bold>B\<^sub>2)) \<^bold>B\<^sub>0"
abbreviation(input) ap1::"'r\<^sub>2,'r\<^sub>3-Cont('a \<Rightarrow> 'b) \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont('a) \<Rightarrow> 'r\<^sub>1,'r\<^sub>3-Cont('b)"
  where "ap1 \<equiv> ((\<^bold>C\<^bold>B\<^sub>2) \<circ> (\<^bold>C\<^bold>B\<^sub>2)) \<^bold>B\<^sub>1"
abbreviation(input) ap2::"'r\<^sub>2,'r\<^sub>3-Cont('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont\<^sub>2('a,'b) \<Rightarrow> 'r\<^sub>1,'r\<^sub>3-Cont('c)"
  where "ap2 \<equiv> ((\<^bold>C\<^bold>B\<^sub>2) \<circ> (\<^bold>C\<^bold>B\<^sub>2)) \<^bold>B\<^sub>2"
abbreviation(input) ap3::"'r\<^sub>2,'r\<^sub>3-Cont('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont\<^sub>3('a,'b,'c) \<Rightarrow> 'r\<^sub>1,'r\<^sub>3-Cont('d)"
  where "ap3 \<equiv> ((\<^bold>C\<^bold>B\<^sub>2) \<circ> (\<^bold>C\<^bold>B\<^sub>2)) \<^bold>B\<^sub>3"
abbreviation(input) ap4::"'r\<^sub>2,'r\<^sub>3-Cont('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont\<^sub>4('a,'b,'c,'d) \<Rightarrow> 'r\<^sub>1,'r\<^sub>3-Cont('e)"
  where "ap4 \<equiv> ((\<^bold>C\<^bold>B\<^sub>2) \<circ> (\<^bold>C\<^bold>B\<^sub>2)) \<^bold>B\<^sub>4"

lemma "ap0 = (\<lambda>f k g. f (\<lambda>x. k (g  x)))" unfolding comb_defs ..
lemma "ap1 = (\<lambda>f k g. f (\<lambda>x. k (g \<circ> x)))" unfolding comb_defs ..
lemma "ap2 = (\<lambda>f k g. f (\<lambda>x. k (g \<circ>\<^sub>2 x)))" unfolding comb_defs ..
lemma "ap3 = (\<lambda>f k g. f (\<lambda>x. k (g \<circ>\<^sub>3 x)))" unfolding comb_defs ..
lemma "ap4 = (\<lambda>f k g. f (\<lambda>x. k (g \<circ>\<^sub>4 x)))" unfolding comb_defs ..

text \<open>Applicative's classic "ap" corresponds to the unary case.\<close>
abbreviation "ap \<equiv> ap1"
abbreviation(input) apr :: "'r\<^sub>1,'r\<^sub>2-Cont('a) \<Rightarrow> 'r\<^sub>2,'r\<^sub>3-Cont('a \<Rightarrow> 'b) \<Rightarrow> 'r\<^sub>1,'r\<^sub>3-Cont('b)" (infixl "\<ggreater>" 54)
  where "a \<ggreater> f \<equiv> ap f a"  \<comment> \<open>convenient "pipeline notation"\<close>

text \<open>Check that applicative operations satisfy the corresponding laws.\<close>
lemma ap_identity:    "x \<ggreater> (unit \<^bold>I) = x" unfolding comb_defs ..
lemma ap_composition: "w \<ggreater> (v \<ggreater> (u \<ggreater> (unit \<^bold>B))) = (w \<ggreater> v) \<ggreater> u" unfolding comb_defs ..
lemma ap_homomorphism: "(unit x) \<ggreater> (unit f) = unit (f x)" unfolding comb_defs ..
lemma ap_interchange: "(unit x) \<ggreater> f = f \<ggreater> unit (\<^bold>T x)" unfolding comb_defs ..


subsection \<open>Monad\<close>

abbreviation bindr1::"('a \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont('b)) \<Rightarrow> 'r\<^sub>2,'r\<^sub>3-Cont('a) \<Rightarrow> 'r\<^sub>1,'r\<^sub>3-Cont('b)"
  where "bindr1 \<equiv> \<^bold>D\<^bold>C\<^bold>B \<^bold>C"
abbreviation bindr2::"('a \<Rightarrow> 'b \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont('c)) \<Rightarrow> 'r\<^sub>2,'r\<^sub>3-Cont\<^sub>2('a,'b) \<Rightarrow> 'r\<^sub>1,'r\<^sub>3-Cont('c)"
  where "bindr2 \<equiv> \<^bold>D\<^bold>C\<^bold>B \<^bold>C\<^sub>2\<^sub>3\<^sub>1"
abbreviation bindr3::"('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont('d)) \<Rightarrow> 'r\<^sub>2,'r\<^sub>3-Cont\<^sub>3('a,'b,'c) \<Rightarrow> 'r\<^sub>1,'r\<^sub>3-Cont('d)"
  where "bindr3 \<equiv> \<^bold>D\<^bold>C\<^bold>B \<^bold>C\<^sub>2\<^sub>3\<^sub>4\<^sub>1"
\<comment> \<open>...and so on\<close>

text \<open>In fact, the term corresponding to bindr1 could have been given a more general type:\<close>
term "\<^bold>D\<^bold>C\<^bold>B \<^bold>C :: ('a \<Rightarrow> 'd \<Rightarrow> 'b) \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'c) \<Rightarrow> 'd \<Rightarrow> 'c"

text \<open>Monad's usual "bind" corresponds to the (reversed) unary case, and gets its customary notation.\<close>
abbreviation "bindr \<equiv> bindr1"
abbreviation(input) bind::"'r\<^sub>2,'r\<^sub>3-Cont('a) \<Rightarrow> ('a \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont('b)) \<Rightarrow> 'r\<^sub>1,'r\<^sub>3-Cont('b)" (infixl "\<bind>" 54)
  where "a \<bind> f \<equiv> bindr f a"

lemma "bindr = (\<lambda>f k. k \<circ> (\<^bold>C f))" unfolding comb_defs ..
lemma "bindr = \<^bold>L (\<^bold>T \<circ>\<^sub>2 (\<^bold>L\<^bold>V))" unfolding comb_defs ..
lemma "bindr2 = (\<lambda>f k. k \<circ> (\<^bold>R f))" unfolding comb_defs ..

text \<open>Note that\<close>
lemma "\<^bold>D\<^bold>C\<^bold>B = \<^bold>B (\<^bold>C\<^bold>B)" unfolding comb_defs ..
lemma "\<^bold>D\<^bold>C\<^bold>B = \<^bold>C\<^sub>3\<^sub>1\<^sub>2\<^sub>4 \<^bold>B\<^sub>2" unfolding comb_defs ..
lemma "\<^bold>D\<^bold>C\<^bold>B = (\<lambda>g x f z. f (g x z))" unfolding comb_defs ..

text \<open>The so-called "monad laws". They guarantee that term operations compose reliably.\<close>
lemma monad_unit1: "(unit x \<bind> f) = f x" unfolding comb_defs ..  \<comment> \<open>left identity\<close>
lemma monad_unit2: "(x \<bind> unit) = x" unfolding comb_defs ..      \<comment> \<open>right identity\<close>
lemma monad_assoc: "((x \<bind> f) \<bind> g) = (x \<bind> (\<lambda>z. f z \<bind> g))" unfolding comb_defs .. \<comment> \<open>associativity\<close>


abbreviation join::"'r\<^sub>2,'r\<^sub>3-Cont('r\<^sub>1,'r\<^sub>2-Cont('a)) \<Rightarrow> 'r\<^sub>1,'r\<^sub>3-Cont('a)"
  where "join \<equiv> \<^bold>C\<^bold>B \<^bold>T" (* preImage (;) wrt. \<^bold>T (|>) *)

text \<open>In fact, the term corresponding to join could have been given a more general type:\<close>
term "\<^bold>C\<^bold>B \<^bold>T :: ((('a \<Rightarrow> 'b) \<Rightarrow> 'b) \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'c"

lemma "join = (\<lambda>k. \<lambda>g. k (\<lambda>y. y g))" unfolding comb_defs ..
lemma "join = (\<lambda>k. \<lambda>g. k (\<^bold>T g))" unfolding comb_defs ..
lemma "join = (\<lambda>k. \<lambda>g. \<^bold>B k \<^bold>T g)" unfolding comb_defs ..
lemma "join = (;) \<^bold>T" unfolding comb_defs ..
lemma "join = (;) (|>)" unfolding comb_defs ..


subsection \<open>Interrelations\<close>

text \<open>We can define bindr in terms of join and fmap\<close>
lemma "join = bindr \<^bold>I" unfolding comb_defs ..
lemma "bindr  = join \<circ>\<^sub>2 fmap" unfolding comb_defs ..

text \<open>Moreover, we can define ap in terms of join and fmap\<close>
lemma "ap0 F A = join (fmap (\<lambda>f. fmap0 f A) F)"  unfolding comb_defs ..
lemma "ap1 F A = join (fmap (\<lambda>f. fmap1 f A) F)"  unfolding comb_defs ..
lemma "ap2 F A = join (fmap (\<lambda>f. fmap2 f A) F)"  unfolding comb_defs ..
lemma "ap3 F A = join (fmap (\<lambda>f. fmap3 f A) F)"  unfolding comb_defs ..
lemma "ap4 F A = join (fmap (\<lambda>f. fmap4 f A) F)"  unfolding comb_defs ..

lemma "ap0 = join \<circ>\<^sub>2 ((\<^bold>C \<circ>\<^sub>2 (;) \<circ> \<^bold>C) fmap0 fmap)"  unfolding comb_defs ..
lemma "ap1 = join \<circ>\<^sub>2 ((\<^bold>C \<circ>\<^sub>2 (;) \<circ> \<^bold>C) fmap1 fmap)"  unfolding comb_defs ..
lemma "ap2 = join \<circ>\<^sub>2 ((\<^bold>C \<circ>\<^sub>2 (;) \<circ> \<^bold>C) fmap2 fmap)"  unfolding comb_defs ..
lemma "ap3 = join \<circ>\<^sub>2 ((\<^bold>C \<circ>\<^sub>2 (;) \<circ> \<^bold>C) fmap3 fmap)"  unfolding comb_defs ..
lemma "ap4 = join \<circ>\<^sub>2 ((\<^bold>C \<circ>\<^sub>2 (;) \<circ> \<^bold>C) fmap4 fmap)"  unfolding comb_defs ..


text \<open>fmap can be stated in terms of (reversed) bind and unit...\<close>
lemma "fmap = (bindr \<circ>\<^sub>2 \<^bold>B) unit"   unfolding comb_defs ..
text \<open>... and ap in terms of bind and fmap\<close>
lemma "ap0 =  \<^bold>B\<^sub>1\<^sub>1 bind \<^bold>I (\<^bold>C fmap0)" unfolding comb_defs ..
lemma "ap1 =  \<^bold>B\<^sub>1\<^sub>1 bind \<^bold>I (\<^bold>C fmap1)" unfolding comb_defs ..
lemma "ap2 =  \<^bold>B\<^sub>1\<^sub>1 bind \<^bold>I (\<^bold>C fmap2)" unfolding comb_defs ..
lemma "ap3 =  \<^bold>B\<^sub>1\<^sub>1 bind \<^bold>I (\<^bold>C fmap3)" unfolding comb_defs ..
lemma "ap4 =  \<^bold>B\<^sub>1\<^sub>1 bind \<^bold>I (\<^bold>C fmap4)" unfolding comb_defs ..


subsection \<open>Pipelines\<close>

subsubsection \<open>Arrows\<close>

text \<open>Monadic (aka. Kleisli) arrows\<close>
term "(m :: 'a \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont('b)) :: 'a \<Rightarrow> ('b \<Rightarrow> 'r\<^sub>1) \<Rightarrow> 'r\<^sub>2"
text \<open>Applicative (aka. static) arrows\<close>
term "(a :: 'r\<^sub>1,'r\<^sub>2-Cont('a \<Rightarrow> 'b)) :: (('a \<Rightarrow> 'b) \<Rightarrow> 'r\<^sub>1) \<Rightarrow> 'r\<^sub>2"

text \<open>Takes a plain function and disguises it as a monadic arrow.\<close>
abbreviation(input) asArrowM::"('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'r-ECont('b))"
  where "asArrowM \<equiv> \<^bold>L \<^bold>B"

text \<open>Takes an applicative arrow and transforms it into a monadic arrow.\<close>
abbreviation(input) intoArrowM::"'r\<^sub>1,'r\<^sub>2-Cont('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont('b))"
  where "intoArrowM \<equiv> \<^bold>C\<^bold>B\<^sub>2 (\<^bold>R \<^bold>B)"

(***TODO***)
text \<open>Takes a monadic arrow and transforms it into an applicative arrow (wrt. a given transformation function).\<close>
term "intoArrowA :: ('r\<^sub>1 \<Rightarrow> 'r\<^sub>2) \<Rightarrow> ('a \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont('b)) \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont('a \<Rightarrow> 'b)"
term "intoArrowA :: ('r\<^sub>1 \<Rightarrow> 'r\<^sub>2) \<Rightarrow> ('a \<Rightarrow> ('b \<Rightarrow> 'r\<^sub>1) \<Rightarrow> 'r\<^sub>2) \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'r\<^sub>1) \<Rightarrow> 'r\<^sub>2"


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
abbreviation(input) mcomp::"('b \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont('c)) \<Rightarrow> ('a \<Rightarrow> 'r\<^sub>2,'r\<^sub>3-Cont('b)) \<Rightarrow> ('a \<Rightarrow> 'r\<^sub>1,'r\<^sub>3-Cont('c))"
  where "mcomp \<equiv> \<^bold>D bindr"
abbreviation(input) mcomp' (infixr "\<Zfinj>" 56) \<comment> \<open>reversed monadic composition, aka. the fish operator ">=>"\<close>
  where "f \<Zfinj> g \<equiv> mcomp g f"

lemma "f \<Zfinj> g = (\<lambda>x. f x \<bind> g)" unfolding comb_defs ..

text \<open>Note the corresponding types:\<close>
term "(\<bind>) :: 'r\<^sub>2,'r\<^sub>3-Cont('a) \<Rightarrow> ('a \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont('b)) \<Rightarrow> 'r\<^sub>1,'r\<^sub>3-Cont('b)"
term "(\<Zfinj>)  :: ('a \<Rightarrow> 'r\<^sub>2,'r\<^sub>3-Cont('b)) \<Rightarrow> ('b \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont('c)) \<Rightarrow> ('a \<Rightarrow> 'r\<^sub>1,'r\<^sub>3-Cont('c))"

text \<open>As expected, monadic composition is associative and suitably interrelates with bind to build pipelines:\<close>
lemma "f \<Zfinj> (g \<Zfinj> h) = (f \<Zfinj> g) \<Zfinj> h" unfolding comb_defs ..
lemma "(x \<bind> f \<bind> g \<bind> h) = (x \<bind> f \<Zfinj> g \<Zfinj> h)" unfolding comb_defs ..

text \<open>Bind in terms of monadic composition\<close>
lemma "bindr = (\<Zfinj>) \<^bold>I" unfolding comb_defs ..
lemma "(\<bind>) = (\<^bold>C \<circ> (\<Zfinj>)) \<^bold>I" unfolding comb_defs ..


subsubsection \<open>Applicative composition\<close>

text \<open>Analogously, we can introduce applicative composition.\<close>

abbreviation(input) acomp  :: "'r\<^sub>2,'r\<^sub>3-Cont('b \<Rightarrow> 'c) \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont('a \<Rightarrow> 'b) \<Rightarrow> 'r\<^sub>1,'r\<^sub>3-Cont('a \<Rightarrow> 'c)"
  where "acomp \<equiv> \<^bold>C\<^bold>B\<^sub>2 ap"
abbreviation(input) acomp' (infixr "\<Zinj>" 56) \<comment> \<open>reversed applicative composition\<close>
  where "f \<Zinj> g \<equiv> acomp g f"

lemma "acomp = (\<lambda>g f k. g (k \<ggreater> f))" unfolding comb_defs ..
lemma "acomp = (\<lambda>g f k. (k \<ggreater> f) |> g)" unfolding comb_defs ..
lemma "acomp = (\<lambda>g f k. g (\<lambda>h. f (\<lambda>x. k (h \<circ> x))))" unfolding comb_defs ..

text \<open>Note the corresponding types:\<close>
term "(\<Zfinj>)  :: ('a \<Rightarrow> 'r\<^sub>2,'r\<^sub>3-Cont('b)) \<Rightarrow> ('b \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont('c)) \<Rightarrow> ('a \<Rightarrow> 'r\<^sub>1,'r\<^sub>3-Cont('c))"
term "(\<Zinj>) :: 'r\<^sub>1,'r\<^sub>2-Cont('a \<Rightarrow> 'b) \<Rightarrow> 'r\<^sub>2,'r\<^sub>3-Cont('b \<Rightarrow> 'c) \<Rightarrow> 'r\<^sub>1,'r\<^sub>3-Cont('a \<Rightarrow> 'c)"

text \<open>Applicative composition is associative and suitably interrelates with ap to build pipelines:\<close>
lemma "f \<Zinj> (g \<Zinj> h) = (f \<Zinj> g) \<Zinj> h" unfolding comb_defs ..
lemma "(x \<ggreater> f \<ggreater> g \<ggreater> h) = (x \<ggreater> f \<Zinj> g \<Zinj> h)" unfolding comb_defs ..

text \<open>Some interrelations:\<close>
lemma "acomp g f = ap (fmap (\<circ>) g) f" unfolding comb_defs ..
lemma "acomp g f = ap (ap (unit (\<circ>)) g) f" unfolding comb_defs ..


subsection \<open>Special functions for manipulating (delimited) continuations\<close>

text \<open>Evaluate a (CPS) expression by passing the identity continuation to it.\<close>
abbreviation(input) eval :: "'p,'o-Cont('p) \<Rightarrow> 'o"
  where "eval \<equiv> unit \<^bold>I"

lemma "eval = \<^bold>T\<^bold>I" unfolding comb_defs ..
lemma "eval m = m (\<lambda>x. x)" unfolding comb_defs ..

text \<open>Reset (aka. "prompt") delimits the start of the continuation.
 The type is the principal (i.e. most general) type assigned by the HM type inference algorithm.\<close>
abbreviation(input) reset :: "'a,'r-Cont('a) \<Rightarrow> 'o,'o-Cont('r)"
  where "reset \<equiv> \<^bold>T \<circ> eval"

notation reset ("prompt") (*another common wording*)

lemma "reset = \<^bold>B \<^bold>T (\<^bold>T \<^bold>I)" unfolding comb_defs ..
lemma "reset = \<^bold>B \<^bold>B \<^bold>B \<^bold>T \<^bold>T \<^bold>I" unfolding comb_defs ..
lemma "reset = (\<^bold>T \<circ>\<^sub>2 \<^bold>T) \<^bold>I" unfolding comb_defs ..
lemma "reset = eval (\<^bold>T \<circ>\<^sub>2 \<^bold>T)" unfolding comb_defs ..

lemma "reset m = (\<lambda>k. k (m \<^bold>I))" unfolding comb_defs ..
lemma "reset m = (\<lambda>k. k (m (\<lambda>x. x)))" unfolding comb_defs ..
lemma "reset = (\<lambda>m k. k (m (\<lambda>x. x)))" unfolding comb_defs ..

text \<open>An alternative (but unduly constrained) type often used in the literature:\<close>
term "reset:: 'a-ECont('a) \<Rightarrow> 'o-ECont('a)"

text \<open>Captures the current continuation up to the nearest \<open>reset\<close> and hands it to its first argument
  as a reified function, which, when called, "jumps" back to the captured point (reinstalling the delimiter).
  The type given is the principal (i.e. most general) type assigned by the HM type-inference algorithm.\<close>
abbreviation(input) shift::"(('a \<Rightarrow> 'o,'o-Cont('p)) \<Rightarrow> 'r,'q-Cont('r)) \<Rightarrow> 'p,'q-Cont('a)"
  where  "shift \<equiv> eval \<circ>\<^sub>2 (\<^bold>C\<^bold>B (\<^bold>B\<^bold>T))"

lemma "shift = (\<lambda>f k. eval (f (\<^bold>B\<^bold>T k)))" unfolding comb_defs ..
lemma "shift = (\<lambda>f k. f (\<^bold>B\<^bold>T k) \<^bold>I)" unfolding comb_defs ..
lemma "shift = (\<lambda>f k. f (\<lambda>a c. c (k a)) \<^bold>I)" unfolding comb_defs ..

lemma "shift = \<^bold>B\<^sub>1\<^sub>1 (eval \<circ>\<^sub>2 \<^bold>A) \<^bold>I (\<^bold>B\<^bold>T)" unfolding comb_defs ..
lemma "shift = (\<^bold>C\<^bold>B (\<^bold>B\<^bold>T)) \<circ> (\<^bold>C\<^bold>C \<^bold>I)" unfolding comb_defs ..

text \<open>An alternative (but unduly constrained) type often used in the literature:\<close>
term "shift :: (('a \<Rightarrow> 'r-ECont('r)) \<Rightarrow> 'r-ECont('r)) \<Rightarrow> 'r-ECont('a)"


text \<open>Control is analogous to shift (but without reinstalling the delimiter)\<close>
abbreviation(input) control:: "(('a \<Rightarrow> 'x,'o-Cont('p)) \<Rightarrow> 'r,'q-Cont('r)) \<Rightarrow> 'o,'q-Cont('a)"
  where "control \<equiv> eval \<circ>\<^sub>2 (\<^bold>C\<^bold>B (\<^bold>B\<^bold>K))"

lemma "control = (\<lambda>f k. eval (f (\<^bold>B\<^bold>K k)))" unfolding comb_defs ..
lemma "control = (\<lambda>f k. f (\<^bold>B\<^bold>K k) \<^bold>I)" unfolding comb_defs ..
lemma "control = (\<lambda>f k. f (\<lambda>a c. k a) \<^bold>I)" unfolding comb_defs ..

lemma "control = \<^bold>B\<^sub>1\<^sub>1 (eval \<circ>\<^sub>2 \<^bold>A) \<^bold>I (\<^bold>B\<^bold>K)" unfolding comb_defs ..
lemma "control = ((\<^bold>C\<^bold>B (\<^bold>B\<^bold>K)) \<circ> (\<^bold>C\<^bold>C \<^bold>I))" unfolding comb_defs ..

text \<open>Alternative (but unduly constrained) types found in the literature:\<close>
term "control :: (('a \<Rightarrow> 'r-ECont('b)) \<Rightarrow> 'r-ECont('r)) \<Rightarrow> 'r-ECont('a)"
term "control :: (('a \<Rightarrow> 'r-ECont('r)) \<Rightarrow> 'r-ECont('r)) \<Rightarrow> 'r-ECont('a)"

text \<open>In fact, the principal type for the definiens (as computed by HM algo) is a bit more general:\<close>
term "(\<lambda>f k. f (\<lambda>a c. k a) \<^bold>I) ::(('a \<Rightarrow> 'b \<Rightarrow> 'o) \<Rightarrow> ('r \<Rightarrow> 'r) \<Rightarrow> 'q) \<Rightarrow> ('a \<Rightarrow> 'o) \<Rightarrow> 'q"

text \<open>Escape (aka. call/cc) invokes the first argument with the current continuation.\<close>
abbreviation(input) escape :: "(('a \<Rightarrow> 'x,'r\<^sub>1-Cont('b)) \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont('a)) \<Rightarrow> 'r\<^sub>1,'r\<^sub>2-Cont('a)"
  where "escape \<equiv> \<^bold>C \<^bold>\<Sigma> (\<^bold>B\<^bold>K)"

lemma "escape = (\<lambda>f. \<^bold>\<Sigma> f (\<^bold>B\<^bold>K))" unfolding comb_defs ..
lemma "escape = (\<lambda>f k. f (\<^bold>B\<^bold>K k) k)" unfolding comb_defs ..
lemma "escape = (\<lambda>f k. f (\<lambda>a c. k a) k)" unfolding comb_defs ..

text \<open> An alternative (but unduly constrained) type often used in the literature:\<close>
term "escape :: (('a \<Rightarrow> 'r-ECont('b)) \<Rightarrow> 'r-ECont('a)) \<Rightarrow> 'r-ECont('a)"

text \<open>In fact, the principal type for the definiens is a bit more general:\<close>
term "(\<lambda>f k. f (\<lambda>a c. k a) k) :: (('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> 'd) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> 'd"

text \<open>Some interrelations satisfied by escape, shift and control\<close>
lemma "escape (\<lambda>k. m) = m" unfolding comb_defs ..
lemma "shift (\<lambda>k. m \<bind> k) = m" unfolding comb_defs ..
lemma "control (\<lambda>k. m \<bind> k) = m" unfolding comb_defs ..
lemma "escape h = shift (\<lambda>k. h (\<lambda>x. shift (\<lambda>c. k x)) \<bind> k)" unfolding comb_defs ..
lemma "escape h = control (\<lambda>k. h (\<lambda>x. control (\<lambda>c. k x)) \<bind> k)" unfolding comb_defs ..

(*TODO: Tests checking operational semantics *)

end