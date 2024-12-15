theory funcs (* A basic theory of functions *)
imports sets
begin

section \<open>Functions\<close>

named_theorems func_defs  (*container for related definitions*)


subsection \<open>Algebraic structure\<close>

subsubsection \<open>Monoidal structure\<close>

(*The identity function is a nullary operation (i.e. a 'constant'). It corresponds to the \<^bold>I combinator.
 Function composition is the main binary operation between functions and corresponds to the \<^bold>B combinator.*)

(*Recalling*)
lemma "f \<circ> g \<circ> h = (\<lambda>x. f (g (h x)))" unfolding comb_defs ..
lemma "f ; g ; h = (\<lambda>x. h( g (f x)))" unfolding comb_defs ..

(*Composition and identity satisfy the monoid conditions.*)
lemma "(f \<circ> g) \<circ> h = f \<circ> (g \<circ> h)" unfolding comb_defs ..    (* associativity *)
lemma "\<^bold>I \<circ> f = f" unfolding comb_defs ..                   (* left identity *)
lemma "f \<circ> \<^bold>I = f" unfolding comb_defs ..                   (* right identity *)


subsubsection \<open>Transposition\<close>

(*Transposition of a (curried) binary function corresponds to the \<^bold>C combinator. It flips/swaps arguments.*)
lemma "f\<^sup>t\<^sup>t = f" unfolding comb_defs .. (* recall that transposition is an involution.*)


subsection \<open>Transformations\<close>

subsubsection \<open>Inverse and kernel of a function\<close>

(*The "inverse" of a function 'f' is the relation that assigns to each object 'b' in its codomain 
 the set of elements in its domain mapped to 'b' (i.e. the preimage of 'b' under 'f') *)
definition inverse::"('a \<Rightarrow> 'b) \<Rightarrow> Rel('b,'a)"
  where "inverse \<equiv> \<^bold>B\<^sub>2\<^sub>1\<^sub>0 \<Q>"

lemma "inverse f b = (\<lambda>a. f a = b)" unfolding inverse_def comb_defs ..

declare inverse_def[func_defs]

(*An alternative combinator-based definition (by commutativity of \<Q>)*)
lemma inverse_def2: "inverse = (\<^bold>D \<Q>)\<^sup>t" unfolding func_defs comb_defs by auto

(*We introduce some convenient superscript notation*)
notation(input) inverse ("_\<inverse>")  notation(output) inverse ("'(_')\<inverse>")

(*The related notion of 'inverse function' of a (bijective) function can be written as:*)
term "(\<iota> \<circ> f\<inverse>) ::('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)" (*Beware: well-behaved for bijective functions only!*)


(*The "kernel" of a function relates those elements in its domain that get assigned the same value*)
definition kernel::"('a \<Rightarrow> 'b) \<Rightarrow> ERel('a)"
  where "kernel \<equiv> \<^bold>\<Psi>\<^sub>2 \<Q>"

lemma "kernel f = (\<lambda>x y. f x = f y)" unfolding kernel_def comb_defs ..

declare kernel_def[func_defs]

(*Convenient superscript notation*)
notation(input) kernel ("_\<^sup>=")  notation(output) kernel ("'(_')\<^sup>=")


subsubsection \<open>Equalizer and coequalizer of a pair of functions\<close>

definition equalizer :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> Set('a)"
  where "equalizer \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 \<Q>"

lemma "equalizer f g = (\<lambda>x. f x = g x)" unfolding equalizer_def comb_defs ..

definition coequalizer :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> Set('b)"
  where "coequalizer \<equiv> \<^bold>W \<circ>\<^sub>2 (\<^bold>\<Psi>\<^sub>2 (\<^bold>B\<^sub>2\<^sub>1\<^sub>1 (\<sqinter>)) inverse)"

lemma "coequalizer f g = (\<lambda>x. (f\<inverse>) x \<sqinter> (g\<inverse>) x)" unfolding coequalizer_def comb_defs ..

declare equalizer_def[func_defs] coequalizer_def[func_defs]


subsubsection \<open>Pullback and pushout of a pair of functions\<close>

(*The pullback (aka. fiber product) of two functions 'f' and 'g' (sharing the same codomain), 
 relates those pairs of elements that get assigned the same value by 'f' and 'g' respectively*)
definition pullback :: "('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> Rel('a,'b)"
  where "pullback \<equiv> \<^bold>B\<^sub>2\<^sub>1\<^sub>1 \<Q>"

lemma "pullback f g = (\<lambda>x y. f x = g y)" unfolding pullback_def comb_defs ..

declare pullback_def[func_defs]

(*We can swap the roles of 'points' and 'functions' in the above definition using a permutator *)
lemma "\<^bold>C\<^sub>3\<^sub>4\<^sub>1\<^sub>2 pullback x y = (\<lambda>f g. f x = g y)" unfolding func_defs comb_defs ..

(*Inverse and kernel of a function can be easily stated in terms of pullback*)
lemma "inverse = pullback \<^bold>I" unfolding func_defs comb_defs by auto
lemma "kernel = \<^bold>W pullback" unfolding func_defs comb_defs ..

(*Similarly, the equalizer of two functions can be stated in terms of pullback*)
lemma "equalizer = \<^bold>W \<circ>\<^sub>2 pullback" unfolding func_defs comb_defs ..


(*The pushout (aka. fiber coproduct) of two functions 'f' and 'g' (sharing the same domain), relates
 those elements (in their codomains) that are images of the same element (i.e. whose preimages intersect)*)
definition pushout :: "('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> Rel('a,'b)" 
  where "pushout \<equiv>  \<^bold>C\<^sub>1\<^sub>3\<^sub>2\<^sub>4(\<^bold>B\<^sub>2\<^sub>2\<^sub>2 (\<sqinter>) inverse inverse)" (* 'inverse' appears twice with different types*)

lemma "pushout f g = (\<lambda>x y. f\<inverse> x \<sqinter> g\<inverse> y)" unfolding pushout_def comb_defs ..

declare pushout_def[func_defs]

(*The following point-free definition would unduly restrict types (since 'inverse' appears only once)*)
lemma "pushout = \<^bold>\<Psi>\<^sub>2 (\<^bold>B\<^sub>2\<^sub>1\<^sub>1 (\<sqinter>)) inverse" unfolding func_defs comb_defs .. 

(*The coequalizer of two functions can be stated in terms of pushout*)
lemma "coequalizer =  \<^bold>W \<circ>\<^sub>2 pushout" unfolding func_defs comb_defs ..


subsubsection \<open>Range, image & preimage of functions\<close>

(*Given a function f we can obtain its range as the set of those objects 'b' in the codomain that 
 are the image of some object 'a' (i.e. have a non-empty preimage) under the function f.*)
definition range::"('a \<Rightarrow> 'b) \<Rightarrow> Set('b)"
  where "range \<equiv> \<exists> \<circ>\<^sub>2 inverse"

lemma "range f = \<exists> \<circ> f\<inverse>" unfolding range_def comb_defs ..
lemma "range f b = (\<exists>a. f a = b)" unfolding range_def func_defs comb_defs ..

(*We can 'lift' functions to act on sets via the image operator. The term "image f" denotes a
 set-operation that takes a set 'A' and returns the set of elements whose f-preimage intersects 'A'.*)
definition image::"('a \<Rightarrow> 'b) \<Rightarrow> Set('a) \<Rightarrow> Set('b)"
  where "image \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<sqinter>) inverse)\<^sup>t"

lemma "image f A = (\<lambda>b. f\<inverse> b \<sqinter> A)" unfolding image_def comb_defs ..
lemma "image f A b = (\<exists>x. f\<inverse> b x \<and> A x)" unfolding image_def set_defs comb_defs ..

(*Analogously, the term "preimage f" denotes a set-operation that takes a set 'B' and returns the 
  set of those elements which 'f' maps to some element in 'B'.*)
definition preimage::"('a \<Rightarrow> 'b) \<Rightarrow> Set('b) \<Rightarrow> Set('a)"
  where "preimage \<equiv> \<^bold>B\<^sup>t"

lemma "preimage f B = (\<lambda>a. B (f a))" unfolding preimage_def comb_defs ..


declare range_def[func_defs] image_def[func_defs] preimage_def[func_defs]

(*Introduce convenient notation*)
notation(input) image ("\<lparr>_ _\<rparr>") and preimage ("\<lparr>_ _\<rparr>\<inverse>")
notation(output) image ("\<lparr>'(_') '(_')\<rparr>") and preimage ("\<lparr>'(_') '(_')\<rparr>\<inverse>")

term "\<lparr>f A\<rparr>" (*read "the image of A under f" *)
term "\<lparr>f B\<rparr>\<inverse> = (\<lambda>a. B (f a))"  (* read "the image of A under f" *)

(*Range can be defined in terms of image as expected*)
lemma range_def2: "range = image\<^sup>t \<UU>"
  unfolding comb_defs func_defs set_defs by simp


term "preimage (f::'a\<Rightarrow>'b) \<circ> image f" (*TODO: make definitions out of these? *)
term "image (f::'a\<Rightarrow>'b) \<circ> preimage f"

lemma "(preimage f \<circ> image f) = (\<lambda>A. \<lambda>a. f\<^sup>= a \<sqinter> A)"  
  unfolding func_defs set_defs comb_defs by metis
lemma "(image f \<circ> preimage f) = (\<lambda>B. \<lambda>b. f\<inverse> b \<sqinter> preimage f B)" 
  unfolding func_defs set_defs comb_defs by metis


subsubsection \<open>Fixed-points of endofunctions\<close>

definition fixedpoint::"('a \<Rightarrow> 'a) \<Rightarrow> Set('a)" ("fp")
  where "fp \<equiv> \<^bold>S \<Q>"
definition cofixedpoint::"('a \<Rightarrow> 'a) \<Rightarrow> Set('a)" ("cfp")
  where "cfp \<equiv> \<^bold>S \<D>"

lemma "fp f x = (x = f x)" unfolding fixedpoint_def comb_defs ..
lemma "cfp f x = (x \<noteq> f x)" unfolding cofixedpoint_def comb_defs ..

declare fixedpoint_def[func_defs] cofixedpoint_def[func_defs]
 

subsection \<open>Structure-preservation under image and preimage\<close>

lemma image_morph1: "image (f \<circ> g) = (image f) \<circ> (image g)"
  unfolding func_defs set_defs comb_defs by auto
lemma image_morph2: "image \<^bold>I = \<^bold>I" 
  unfolding func_defs set_defs comb_defs by simp
lemma preimage_morph1: "preimage (f \<circ> g) = (preimage g) \<circ> (preimage f)" 
  unfolding func_defs comb_defs ..
lemma preimage_morph2: "preimage \<^bold>I = \<^bold>I" 
  unfolding func_defs comb_defs ..


(*Random simplification(?) rule (TODO: interpret)*)
lemma image_simp1: "(image ((G \<circ> R) a)) \<circ> (image (\<^bold>T a)) = (image (\<^bold>T a)) \<circ> (image (\<^bold>S (G \<circ> R)))"
  apply(rule ext) unfolding comb_defs set_defs func_defs by fastforce

end