section \<open>Endopairs\<close>

theory endopairs (* A basic theory of endopairs *)
  imports logic_bridge
begin

named_theorems endopair_defs and endopair_simps

subsection \<open>Definitions\<close>

text \<open>Term constructor: making an endopair out of two given objects.\<close>
definition mkEndopair::"'a \<Rightarrow> 'a \<Rightarrow> EPair('a)" ("<_,_>") 
  where "mkEndopair \<equiv> \<^bold>L\<^sub>3 If"

declare mkEndopair_def[endopair_defs]

text \<open>With syntactic sugar the above definition looks like:\<close>
lemma "<x,y> = (\<lambda>b. if b then x else y)"
  unfolding endopair_defs comb_defs ..

text \<open>Under the hood, the term constructor \<open>mkEndopair\<close> is built in terms of definite descriptions.\<close>
lemma mkEndopair_def2: "<x,y> = (\<lambda>b. \<iota> z. (b \<rightarrow> z = x) \<and> (\<not>b \<rightarrow> z = y))" 
  unfolding endopair_defs comb_defs unfolding If_def by simp

text \<open>Incidentally, (endo)pairs of booleans have an alternative, simpler representation.\<close>
lemma mkEndopair_bool_simp: "<x,y> = (\<lambda>b. (b \<and> x) \<or> (\<not>b \<and> y))" 
  apply(rule ext) unfolding endopair_defs comb_defs by simp

text \<open>Componentwise equality comparison between endopairs (added as convenient simplification rule).\<close>
lemma mkEndopair_equ_simp: "(<x\<^sub>1,x\<^sub>2> = <y\<^sub>1,y\<^sub>2>) = (x\<^sub>1 = y\<^sub>1 \<and> x\<^sub>2 = y\<^sub>2)"
  unfolding endopair_defs comb_defs by metis

text \<open>We conveniently add the previous lemmata as a simplification rules.\<close>
declare mkEndopair_bool_simp[endopair_simps] and mkEndopair_equ_simp[endopair_simps]

text \<open>Now, observe that:\<close>
lemma "<x,y> \<T> = x" 
  unfolding endopair_defs comb_defs by simp
lemma "<x,y> \<F> = y" 
  unfolding endopair_defs comb_defs by simp

text \<open>This motivates the introduction of the following projection/extraction functions.\<close>
definition proj1::"EPair('a) \<Rightarrow> 'a" ("\<pi>\<^sub>1")
  where "\<pi>\<^sub>1 \<equiv> \<^bold>T \<T>"
definition proj2::"EPair('a) \<Rightarrow> 'a" ("\<pi>\<^sub>2")
  where "\<pi>\<^sub>2 \<equiv> \<^bold>T \<F>"

declare proj1_def[endopair_defs] proj2_def[endopair_defs]

lemma "\<pi>\<^sub>1 = (\<lambda>P. P \<T>)"   (*sanity check*)
  unfolding endopair_defs comb_defs ..
lemma "\<pi>\<^sub>2 = (\<lambda>P. P \<F>)"   (*sanity check*)
  unfolding endopair_defs comb_defs ..

text \<open>The following lemmata (aka. "product laws") verify that the previous definitions work as intended.\<close>
lemma proj1_simp: "\<pi>\<^sub>1 <x,y> = x" 
  unfolding endopair_defs comb_defs by simp
lemma proj2_simp: "\<pi>\<^sub>2 <x,y> = y" 
  unfolding endopair_defs comb_defs by simp
lemma mkEndopair_simp: "<\<pi>\<^sub>1 P, \<pi>\<^sub>2 P> = P" 
  unfolding endopair_defs comb_defs apply(rule ext) by simp

text \<open>We conveniently add them as simplification rules.\<close>
declare proj1_simp[endopair_simps] proj2_simp[endopair_simps] mkEndopair_simp[endopair_simps]

text \<open>Let's now add a useful "swap" (endo)operation on endopairs.\<close>
definition swap::"EOp(EPair('a))" 
  where "swap \<equiv> (\<ggreater>) (\<not>)"

declare swap_def[endopair_defs]

lemma "swap p = (\<not>) \<ggreater> p" unfolding endopair_defs comb_defs ..
lemma "swap p = (\<lambda>b. p (\<not>b))" unfolding endopair_defs comb_defs ..

text \<open>We conveniently prove and add some useful simplification rules.\<close>
lemma swap_simp1: "swap <a,b> = <b,a>" 
  unfolding endopair_defs comb_defs by auto
lemma swap_simp2: "<\<pi>\<^sub>2 p, \<pi>\<^sub>1 p> = swap p" 
  unfolding endopair_defs comb_defs by auto

declare swap_simp1[endopair_simps] swap_simp2[endopair_simps]


subsection \<open>Currying\<close>

text \<open>The morphisms that convert between unary operations on endopairs and (curried) binary operations.\<close>
definition curry::"Op(EPair('a),'b) \<Rightarrow> Op\<^sub>2('a,'b)" ("\<lfloor>_\<rfloor>")
  where "curry \<equiv> (\<ggreater>\<^sub>2) mkEndopair"
definition uncurry::"Op\<^sub>2('a,'b) \<Rightarrow> Op(EPair('a),'b)" ("\<lceil>_\<rceil>")
  where "uncurry \<equiv> \<^bold>L\<^sub>3 \<^bold>\<Phi>\<^sub>2\<^sub>1 \<pi>\<^sub>1 \<pi>\<^sub>2"

declare curry_def[endopair_defs] uncurry_def[endopair_defs]

text \<open>Some sanity checks:\<close>
lemma "curry f = \<^bold>B\<^sub>2 f mkEndopair" unfolding endopair_defs comb_defs ..
lemma "curry f = (\<lambda>x y. f <x,y>)" unfolding endopair_defs comb_defs ..
lemma "uncurry f = \<^bold>\<Phi>\<^sub>2\<^sub>1 f \<pi>\<^sub>1 \<pi>\<^sub>2" unfolding endopair_defs comb_defs ..
lemma "uncurry f = (\<lambda>P. f (\<pi>\<^sub>1 P) (\<pi>\<^sub>2 P))" unfolding endopair_defs comb_defs ..

text \<open>Note, in particular\<close>
lemma "mkEndopair = curry \<^bold>I" unfolding endopair_defs comb_defs ..

text \<open>Both morphisms constitute an isomorphism (we add them as simplification rules too)\<close>
lemma curry_simp1: "\<lfloor>\<lceil>f\<rceil>\<rfloor> = f" 
  unfolding curry_def uncurry_def comb_defs unfolding endopair_simps ..
lemma curry_simp2: "\<lceil>\<lfloor>f\<rfloor>\<rceil> = f"
  unfolding curry_def uncurry_def comb_defs unfolding endopair_simps ..

declare curry_simp1[endopair_simps] curry_simp2[endopair_simps]

end