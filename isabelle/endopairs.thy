theory endopairs (* A basic theory of endopairs *)
  imports base
begin


section \<open>Endopairs\<close>

(*Let's put endopair-related definitions/simplification-rules in respective bags*)
named_theorems endopair_defs 
named_theorems endopair_simps

(*Term constructor: making an endopair out of two given objects*)
definition mkEndopair::"'a \<Rightarrow> 'a \<Rightarrow> EPair('a)" ("<_,_>") 
  where "mkEndopair \<equiv> \<^bold>L If"

declare mkEndopair_def[endopair_defs]

lemma "<x,y> = (\<lambda>b. if b then x else y)"  (*sanity check*)
  unfolding endopair_defs comb_defs ..

(*Under the hood, the term constructor mkEndopair is built in terms of definite descriptions: *)
lemma mkEndopair_def2: "<x,y> = (\<lambda>b. \<iota> z. (b \<rightarrow> z = x) \<and> (\<not>b \<rightarrow> z = y))" 
  unfolding endopair_defs comb_defs unfolding If_def by simp

(*Incidentally, (endo)pairs of booleans have an alternative, simpler representation: *)
lemma mkEndopair_bool_simp: "<x,y> = (\<lambda>b. (b \<and> x) \<or> (\<not>b \<and> y))" 
  apply(rule ext) unfolding endopair_defs comb_defs by simp

(*We conveniently add the previous lemma as a simplification rule*)
declare mkEndopair_bool_simp[endopair_simps]

(* Componentwise equality comparison between endopairs (added as convenient simplification rule)*)
lemma mkEndopair_equ_simp: "(<x\<^sub>1,x\<^sub>2> = <y\<^sub>1,y\<^sub>2>) = (x\<^sub>1 = y\<^sub>1 \<and> x\<^sub>2 = y\<^sub>2)"
  unfolding endopair_defs comb_defs by metis

declare mkEndopair_equ_simp[endopair_simps]

(*Now, observe that*)
lemma "<x,y> True = x" 
  unfolding endopair_defs comb_defs by simp
lemma "<x,y> False = y" 
  unfolding endopair_defs comb_defs by simp

(*This motivates the introduction of the following projection/extraction functions*)
definition proj1::"EPair('a) \<Rightarrow> 'a" ("\<pi>\<^sub>1")
  where "\<pi>\<^sub>1 \<equiv> \<^bold>T True"
definition proj2::"EPair('a) \<Rightarrow> 'a" ("\<pi>\<^sub>2")
  where "\<pi>\<^sub>2 \<equiv> \<^bold>T False"

declare proj1_def[endopair_defs] proj2_def[endopair_defs]

lemma "\<pi>\<^sub>1 = (\<lambda>P. P True)"   (*sanity check*)
  unfolding endopair_defs comb_defs ..
lemma "\<pi>\<^sub>2 = (\<lambda>P. P False)"   (*sanity check*)
  unfolding endopair_defs comb_defs ..

(*The following lemmata (aka 'product laws') verify that the previous definitions work as intended*)
lemma proj1_simp: "\<pi>\<^sub>1 <x,y> = x" 
  unfolding endopair_defs comb_defs by simp
lemma proj2_simp: "\<pi>\<^sub>2 <x,y> = y" 
  unfolding endopair_defs comb_defs by simp
lemma mkEndopair_simp: "<\<pi>\<^sub>1 P, \<pi>\<^sub>2 P> = P" 
  unfolding endopair_defs comb_defs apply(rule ext) by simp

(*We conveniently add them as simplification rules*)
declare proj1_simp[endopair_simps] proj2_simp[endopair_simps] mkEndopair_simp[endopair_simps]

(*Let's now add the useful 'swap' (endo)operation on endopairs*)
definition swap::"EOp(EPair('a))" 
  where "swap \<equiv> \<^bold>C \<^bold>B (\<not>)"

declare swap_def[endopair_defs]

lemma "swap p = p \<circ> (\<not>)" unfolding endopair_defs comb_defs ..
lemma "swap p = (\<lambda>b. p (\<not>b))" unfolding endopair_defs comb_defs ..

lemma swap_simp1: "swap <a,b> = <b,a>" 
  unfolding endopair_defs comb_defs by auto
lemma swap_simp2: "<\<pi>\<^sub>2 p, \<pi>\<^sub>1 p> = swap p" 
  unfolding endopair_defs comb_defs by auto

declare swap_simp1[endopair_simps] swap_simp2[endopair_simps]


section \<open>Isomorphism of types for binary operations\<close>

(*The morphisms that convert unary operations on endopairs into (curried) binary operations, and viceversa*)
definition curry::"Op(EPair('a),'b) \<Rightarrow> Op\<^sub>2('a,'b)" ("\<lfloor>_\<rfloor>")
  where "curry \<equiv> \<^bold>C \<^bold>B\<^sub>2 mkEndopair"
definition uncurry::"Op\<^sub>2('a,'b) \<Rightarrow> Op(EPair('a),'b)" ("\<lceil>_\<rceil>")
  where "uncurry \<equiv> \<^bold>L \<^bold>\<Phi>\<^sub>2\<^sub>1 \<pi>\<^sub>1 \<pi>\<^sub>2"

declare curry_def[endopair_defs] uncurry_def[endopair_defs]

(*sanity checks*)
lemma "curry Op = \<^bold>B\<^sub>2 Op mkEndopair" unfolding endopair_defs comb_defs ..
lemma "curry Op = (\<lambda>x y. Op <x,y>)" unfolding endopair_defs comb_defs ..
lemma "uncurry Op = \<^bold>\<Phi>\<^sub>2\<^sub>1 Op \<pi>\<^sub>1 \<pi>\<^sub>2" unfolding endopair_defs comb_defs ..
lemma "uncurry Op = (\<lambda>P. Op (\<pi>\<^sub>1 P) (\<pi>\<^sub>2 P))" unfolding endopair_defs comb_defs ..

(*Both morphisms constitute an isomorphism (we tag them as simplification rules too)*)
lemma curry_simp1: "\<lfloor>\<lceil>Op\<rceil>\<rfloor> = Op" 
  unfolding curry_def uncurry_def comb_defs unfolding endopair_simps ..
lemma curry_simp2: "\<lceil>\<lfloor>Op\<rfloor>\<rceil> = Op"
  unfolding curry_def uncurry_def comb_defs unfolding endopair_simps ..

declare curry_simp1[endopair_simps] curry_simp2[endopair_simps]

end