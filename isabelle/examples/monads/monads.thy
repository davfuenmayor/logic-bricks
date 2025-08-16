theory monads
imports "../../induction" "HOL-Eisbach.Eisbach"
begin

section \<open>Monads\<close>

named_theorems monad_defs


subsection \<open>Monad Laws\<close>

text \<open>The so-called "monad laws". They guarantee that monad-related term operations compose reliably.\<close>
abbreviation(input) "monadLaw1 unit bind \<equiv> \<forall>f a. (bind (unit a) f) = (f a)" \<comment> \<open>left identity\<close>
abbreviation(input) "monadLaw2 unit bind \<equiv> \<forall>A. (bind A unit) = A" \<comment> \<open>right identity\<close>
abbreviation(input) "monadLaw3 bind \<equiv> \<forall>A f g. (bind A (\<lambda>a. bind (f a) g)) = bind (bind A f) g" \<comment> \<open>associativity\<close>


subsection \<open>Identity Monad\<close>

text \<open>We start by considering the (degenerate) base case arising from an identity type constructor\<close>
abbreviation(input) unit_id::"'a \<Rightarrow> 'a"
  where "unit_id \<equiv> \<^bold>I"
abbreviation(input) fmap_id::"('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"
  where "fmap_id \<equiv> \<^bold>A"
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


subsection \<open>Environment (aka. Reader) Monad\<close>

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


text \<open>Verifies compliance with the monad laws.\<close>
lemma "monadLaw1 unit_env bind_env" unfolding comb_defs by simp
lemma "monadLaw2 unit_env bind_env" unfolding comb_defs by simp
lemma "monadLaw3 bind_env" unfolding comb_defs by simp


subsubsection \<open>Digression: On Higher Arities\<close>

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


subsection \<open>Set Monad\<close>

text \<open>We can conceive of types of form \<open>Set('a)\<close>, i.e. \<open>'a \<Rightarrow> o\<close>, as arising via an "environmentalization"
 (or "indexation") of the boolean type \<open>o\<close> by the type \<open>'a\<close> (i.e. as an instance of the environment 
 monad discussed previously). Furthermore, we can adopt an alternative perspective and consider a 
 constructor that returns the type of boolean "valuations" (or "classifiers") for objects of type \<open>'a\<close>.
 This type constructor comes with a monad structure too (and is also an applicative and a functor).\<close>

abbreviation(input) unit_set::"'a \<Rightarrow> Set('a)"
  where "unit_set \<equiv> \<Q>"
abbreviation(input) fmap_set::"('a \<Rightarrow> 'b) \<Rightarrow> Set('a) \<Rightarrow> Set('b)"
  where "fmap_set \<equiv> image"
abbreviation(input) join_set::"Set(Set('a)) \<Rightarrow> Set('a)"
  where "join_set \<equiv> \<Union>"
abbreviation(input) ap_set::"Set('a \<Rightarrow> 'b) \<Rightarrow> Set('a) \<Rightarrow> Set('b)"
  where "ap_set \<equiv> rightImage \<circ> intoRel"
abbreviation(input) rbind_set::"('a \<Rightarrow> Set('b)) \<Rightarrow> Set('a) \<Rightarrow> Set('b)"
  where "rbind_set \<equiv> rightImage" \<comment> \<open>reversed bind\<close>

text \<open>We define the customary bind operation as "flipped" \<open>rbind\<close> (which seems more intuitive).\<close>
abbreviation bind_set::"Set('a) \<Rightarrow> ('a \<Rightarrow> Set('b)) \<Rightarrow> Set('b)"
  where "bind_set \<equiv> \<^bold>C rbind_set"

text \<open>Some properties of monads in general.\<close>
lemma "rbind_set = join_set \<circ>\<^sub>2 fmap_set" unfolding rel_defs func_defs comb_defs by metis
lemma "join_set = rbind_set \<^bold>I" unfolding rel_defs func_defs comb_defs by metis
\<comment> \<open>... and so on\<close>

text \<open>Some properties of this particular monad.\<close>
lemma "ap_set = \<Union>\<^sup>r \<circ> (image image)" unfolding rel_defs func_defs comb_defs by blast
\<comment> \<open>... and so on\<close>

text \<open>Verifies compliance with the monad laws.\<close>
lemma "monadLaw1 unit_set bind_set" unfolding rel_defs func_defs comb_defs by simp
lemma "monadLaw2 unit_set bind_set" unfolding rel_defs func_defs comb_defs by simp
lemma "monadLaw3 bind_set" unfolding rel_defs func_defs comb_defs by auto


subsection \<open>Relation Monad\<close>

text \<open>In fact, the \<open>Rel('a,'b)\<close> type constructor also comes with a monad structure, which can be seen as 
 a kind of "monad composition" of the environment monad with the set monad.\<close>

abbreviation(input) unit_rel::"'a \<Rightarrow> Rel('b,'a)"
  where "unit_rel \<equiv> \<^bold>K \<circ> \<Q>"
abbreviation(input) fmap_rel::"('a \<Rightarrow> 'b) \<Rightarrow> Rel('c,'a) \<Rightarrow> Rel('c,'b)"
  where "fmap_rel \<equiv> \<^bold>B \<circ> image"
abbreviation(input) join_rel::"Rel('c,Rel('c,'a)) \<Rightarrow> Rel('c,'a)"
  where "join_rel \<equiv> \<^bold>W \<circ> (\<^bold>B \<Union>\<^sup>r)"
abbreviation(input) ap_rel::"Rel('c, 'a \<Rightarrow> 'b) \<Rightarrow> Rel('c,'a) \<Rightarrow> Rel('c,'b)"
  where "ap_rel \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (rightImage \<circ> intoRel)"
abbreviation(input) rbind_rel::"('a \<Rightarrow> Rel('c,'b)) \<Rightarrow> Rel('c,'a) \<Rightarrow> Rel('c,'b)"
  where "rbind_rel \<equiv> (\<^bold>\<Phi>\<^sub>2\<^sub>1 rightImage) \<circ> \<^bold>C" \<comment> \<open>reversed bind\<close>

text \<open>Again, we define the bind operation as "flipped" rbind\<close>
abbreviation bind_rel::"Rel('c,'a) \<Rightarrow> ('a \<Rightarrow> Rel('c,'b)) \<Rightarrow> Rel('c,'b)"
  where "bind_rel \<equiv> \<^bold>C rbind_rel"

text \<open>Some properties of monads in general.\<close>
lemma "rbind_rel = join_rel \<circ>\<^sub>2 fmap_rel" unfolding rel_defs func_defs comb_defs by metis
lemma "join_rel = rbind_rel \<^bold>I" unfolding rel_defs func_defs comb_defs by metis
\<comment> \<open>... and so on\<close>

text \<open>Note that for the relation monad we have:\<close>
lemma "unit_rel = \<^bold>B unit_env unit_set" ..
lemma "fmap_rel = \<^bold>B fmap_env fmap_set" ..
lemma "ap_rel = \<^bold>\<Phi>\<^sub>2\<^sub>1 ap_set" ..
lemma "rbind_rel = \<^bold>B (\<^bold>C \<^bold>B \<^bold>C) \<^bold>\<Phi>\<^sub>2\<^sub>1 rbind_set" unfolding comb_defs ..
\<comment> \<open>... and so on\<close>

text \<open>Finally, verify compliance with the monad laws.\<close>
lemma "monadLaw1 unit_rel bind_rel" unfolding rel_defs func_defs comb_defs by simp
lemma "monadLaw2 unit_rel bind_rel" unfolding rel_defs func_defs comb_defs by simp
lemma "monadLaw3 bind_rel" unfolding rel_defs func_defs comb_defs by auto


end