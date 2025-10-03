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

lemma "fmap0 = (\<^bold>L \<circ> (\<^bold>C\<^bold>B\<^sub>2 \<^bold>B\<^sub>0)) \<^bold>T" unfolding comb_defs ..
lemma "fmap1 = (\<^bold>L \<circ> (\<^bold>C\<^bold>B\<^sub>2 \<^bold>B\<^sub>1)) \<^bold>T" unfolding comb_defs ..
lemma "fmap2 = (\<^bold>L \<circ> (\<^bold>C\<^bold>B\<^sub>2 \<^bold>B\<^sub>2)) \<^bold>T" unfolding comb_defs ..
lemma "fmap3 = (\<^bold>L \<circ> (\<^bold>C\<^bold>B\<^sub>2 \<^bold>B\<^sub>3)) \<^bold>T" unfolding comb_defs ..
lemma "fmap4 = (\<^bold>L \<circ> (\<^bold>C\<^bold>B\<^sub>2 \<^bold>B\<^sub>4)) \<^bold>T" unfolding comb_defs ..

lemma "fmap0 = (\<lambda>f k g. k (g f))" unfolding comb_defs ..
lemma "fmap1 = (\<lambda>f k g. k (g \<circ> f))" unfolding comb_defs ..
lemma "fmap2 = (\<lambda>f k g. k (g \<circ>\<^sub>2 f))" unfolding comb_defs ..
lemma "fmap3 = (\<lambda>f k g. k (g \<circ>\<^sub>3 f))" unfolding comb_defs ..
lemma "fmap4 = (\<lambda>f k g. k (g \<circ>\<^sub>4 f))" unfolding comb_defs ..

lemma "fmap0 f = (\<lambda>k g. (f |> g) |> k)" unfolding comb_defs ..
lemma "fmap1 f = (\<lambda>k g. (f ; g)  |> k)" unfolding comb_defs ..
lemma "fmap2 f = (\<lambda>k g. (f ;\<^sub>2 g) |> k)" unfolding comb_defs ..
lemma "fmap3 f = (\<lambda>k g. (f ;\<^sub>3 g) |> k)" unfolding comb_defs ..
lemma "fmap4 f = (\<lambda>k g. (f ;\<^sub>4 g) |> k)" unfolding comb_defs ..

text \<open>Functor's classic "fmap" corresponds to the unary case.\<close>
abbreviation "fmap \<equiv> fmap1"


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


text \<open>In contrast to the environment monad, in the case of the continuation monad "unit" does not 
correspond exactly to "fmap0". It is not unrelated however.\<close>
abbreviation(input) unit::"'a \<Rightarrow> 'r-ECont('a)"
  where "unit \<equiv> \<^bold>T"

lemma "unit = (|>)" unfolding comb_defs ..
lemma "unit = \<^bold>C \<^bold>A" unfolding comb_defs ..
lemma "unit = \<^bold>C \<^bold>I" unfolding comb_defs ..
lemma "unit = \<^bold>C fmap0 \<^bold>A" unfolding comb_defs ..
lemma "unit = \<^bold>C fmap0 \<^bold>I" unfolding comb_defs ..
lemma "unit = \<^bold>C\<^bold>C \<^bold>I fmap0" unfolding comb_defs ..

text \<open>The so-called "monad laws". They guarantee that term operations compose reliably.\<close>
lemma monad_unit1: "(unit x \<bind> f) = f x" unfolding comb_defs ..  \<comment> \<open>left identity\<close>
lemma monad_unit2: "(x \<bind> unit) = x" unfolding comb_defs ..      \<comment> \<open>right identity\<close>
lemma monad_assoc: "((x \<bind> f) \<bind> g) = (x \<bind> (\<lambda>z. f z \<bind> g))" unfolding comb_defs .. \<comment> \<open>associativity\<close>


abbreviation join::"'r\<^sub>2,'r\<^sub>3-Cont('r\<^sub>1,'r\<^sub>2-Cont('a)) \<Rightarrow> 'r\<^sub>1,'r\<^sub>3-Cont('a)"
  where "join \<equiv> \<^bold>C\<^bold>B \<^bold>T" (* preImage (;) wrt. \<^bold>T *)

text \<open>In fact, the term corresponding to join could have been given a more general type:\<close>
term "\<^bold>C\<^bold>B \<^bold>T :: ((('a \<Rightarrow> 'b) \<Rightarrow> 'b) \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'c"

lemma "join = (\<lambda>k. \<lambda>g. k (\<lambda>y. y g))" unfolding comb_defs ..
lemma "join = (\<lambda>k. \<lambda>g. k (\<^bold>T g))" unfolding comb_defs ..
lemma "join = (\<lambda>k. \<lambda>g. \<^bold>B k \<^bold>T g)" unfolding comb_defs ..
lemma "join = (;) \<^bold>T" unfolding comb_defs ..


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

end