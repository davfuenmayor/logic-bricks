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
lemma "\<^bold>I \<circ> f = f" unfolding comb_defs ..                   (* identity 1 *)
lemma "f \<circ> \<^bold>I = f" unfolding comb_defs ..                   (* identity 2 *)


subsection \<open>Transformations\<close>

subsubsection \<open>Inverse of a function\<close>

(*The "inverse" of a function 'f' is the relation that assigns to each object 'b' in its codomain 
 the set of elements in its domain mapped to 'b' (i.e. the preimage of 'b' under 'f') *)
definition inverse::"('a \<Rightarrow> 'b) \<Rightarrow> Rel('b,'a)"
  where "inverse \<equiv> \<^bold>B\<^sub>1\<^sub>0 \<Q>"

lemma "inverse f b = (\<lambda>a. f a = b)" unfolding inverse_def comb_defs ..

declare inverse_def[func_defs]

(*An alternative combinator-based definition (by commutativity of \<Q>)*)
lemma inverse_def2: "inverse = \<^bold>C (\<^bold>D \<Q>)" unfolding func_defs comb_defs by auto

(*We introduce some convenient superscript notation*)
notation(input) inverse ("_\<inverse>")  notation(output) inverse ("'(_')\<inverse>")

(*The related notion of 'inverse function' of a (bijective) function can be written as:*)
term "(\<iota> \<circ> f\<inverse>) ::('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)" (*Beware: well-behaved for bijective functions only!*)


subsubsection \<open>Kernel of a function\<close>

(*The "kernel" of a function relates those elements in its domain that get assigned the same value*)
definition kernel::"('a \<Rightarrow> 'b) \<Rightarrow> ERel('a)"
  where "kernel \<equiv> \<^bold>\<Psi>\<^sub>2 \<Q>"

lemma "kernel f = (\<lambda>x y. f x = f y)" unfolding kernel_def comb_defs ..

declare kernel_def[func_defs]

(*Convenient superscript notation*)
notation(input) kernel ("_\<^sup>=")  notation(output) kernel ("'(_')\<^sup>=")


subsubsection \<open>Pullback and equalizer of a pair of functions\<close>

(*The pullback (aka. fiber product) of two functions 'f' and 'g' (sharing the same codomain), 
 relates those pairs of elements that get assigned the same value by 'f' and 'g' respectively*)
definition pullback :: "('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> Rel('a,'b)"
  where "pullback \<equiv> \<^bold>B\<^sub>1\<^sub>1 \<Q>"

lemma "pullback f g = (\<lambda>x y. f x = g y)" unfolding pullback_def comb_defs ..

declare pullback_def[func_defs]

(*Inverse and kernel of a function can be easily stated in terms of pullback*)
lemma "inverse = pullback \<^bold>I" unfolding func_defs comb_defs by auto
lemma "kernel = \<^bold>W pullback" unfolding func_defs comb_defs ..

(*The equalizer of two functions 'f' and 'g' (sharing the same domain and codomain) is the set of 
 elements in their (common) domain that get assigned the same value by both 'f' and 'g'. *)
definition equalizer :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> Set('a)"
  where "equalizer \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 \<Q>"

lemma "equalizer f g = (\<lambda>x. f x = g x)" unfolding equalizer_def comb_defs ..

declare equalizer_def[func_defs]

(*In fact, the equalizer of two functions can be stated in terms of pullback*)
lemma "equalizer = \<^bold>W \<circ>\<^sub>2 pullback" unfolding func_defs comb_defs ..

(*Note that we can swap the roles of 'points' and 'functions' in the above definitions using permutators *)
lemma "\<^bold>R equalizer x = (\<lambda>f g. f x = g x)" unfolding func_defs comb_defs ..
lemma "\<^bold>C\<^sub>2 pullback x y = (\<lambda>f g. f x = g y)" unfolding func_defs comb_defs ..


subsubsection \<open>Pushout and coequalizer of a pair of functions\<close>

(*The pushout (aka. fiber coproduct) of two functions 'f' and 'g' (sharing the same domain), relates
 pairs of elements (in their codomains) whose preimages under 'f' resp. 'g' intersect *)
definition pushout :: "('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> Rel('a,'b)" 
  where "pushout \<equiv> \<^bold>B\<^sub>2\<^sub>2 (\<sqinter>) inverse inverse" (*beware polymorphism: 'inverse' appears twice with different types*)

lemma "pushout f g = (\<lambda>x y. f\<inverse> x \<sqinter> g\<inverse> y)" unfolding pushout_def comb_defs ..

declare pushout_def[func_defs]

(*The equations below don't work as definitions since they unduly restrict types ('inverse' appears only once)*)
lemma "pushout = \<^bold>W (\<^bold>B\<^sub>2\<^sub>2 (\<sqinter>)) inverse" unfolding func_defs comb_defs .. 
lemma "pushout = \<^bold>\<Psi>\<^sub>2 (\<^bold>B\<^sub>1\<^sub>1 (\<sqinter>)) inverse" unfolding func_defs comb_defs .. 

(*The coequalizer of two functions 'f' and 'g' (sharing the same domain and codomain) is the set of 
 elements in their (common) codomain whose preimage under 'f' resp. 'g' intersect*)
definition coequalizer :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> Set('b)"
  where "coequalizer \<equiv> \<^bold>W \<circ>\<^sub>2 (\<^bold>\<Psi>\<^sub>2 (\<^bold>B\<^sub>1\<^sub>1 (\<sqinter>)) inverse)" 

lemma "coequalizer f g = \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<sqinter>) (f\<inverse>) (g\<inverse>)" unfolding coequalizer_def comb_defs ..
lemma "coequalizer f g = (\<lambda>x. (f\<inverse>) x \<sqinter> (g\<inverse>) x)" unfolding coequalizer_def comb_defs ..

declare coequalizer_def[func_defs]

(*The coequalizer of two functions can be stated in terms of pushout*)
lemma "coequalizer = \<^bold>W \<circ>\<^sub>2 pushout" unfolding func_defs comb_defs ..


subsubsection \<open>Fixed-Points\<close>
(*We encode the notion of fixed-points and non-fixed-points of an endofunction.*)

definition fixedPoint::"('a \<Rightarrow> 'a) \<Rightarrow> Set('a)" ("FP")
  where "FP \<equiv> \<^bold>S \<Q>"
definition nonFixedPoint::"('a \<Rightarrow> 'a) \<Rightarrow> Set('a)" ("nFP")
  where "nFP \<equiv> \<^bold>S \<D>"

lemma "FP f x = (x = f x)" unfolding fixedPoint_def comb_defs ..
lemma "nFP f x = (x \<noteq> f x)" unfolding nonFixedPoint_def comb_defs ..

declare fixedPoint_def[func_defs] nonFixedPoint_def[func_defs]

(*It holds in general:*)
lemma "nFP = \<midarrow> \<circ> FP" unfolding func_defs set_defs comb_defs ..
lemma "nFP f = \<midarrow>(FP f)" unfolding func_defs set_defs comb_defs ..


subsubsection \<open>Range of functions\<close>

(*Given a function f we can obtain its range as the set of those objects 'b' in the codomain that 
 are the image of some object 'a' (i.e. have a non-empty preimage) under the function f.*)
definition range::"('a \<Rightarrow> 'b) \<Rightarrow> Set('b)"
  where "range \<equiv> \<exists> \<circ>\<^sub>2 inverse"

declare range_def[func_defs]

lemma "range f = \<exists> \<circ> f\<inverse>" unfolding func_defs comb_defs ..
lemma "range f b = (\<exists>a. f a = b)" unfolding func_defs comb_defs ..


subsection \<open>Set-operations defined from functions\<close>

(*We can 'lift' functions to act on sets via the image operator. The term "image f" denotes a
 set-operation that takes a set 'A' and returns the set of elements whose f-preimage intersects 'A'.*)
definition image::"('a \<Rightarrow> 'b) \<Rightarrow> Set('a) \<Rightarrow> Set('b)"
  where "image \<equiv> \<^bold>C (\<^bold>B\<^sub>2\<^sub>0 (\<sqinter>) inverse)"

lemma "image f A = (\<lambda>b. f\<inverse> b \<sqinter> A)" unfolding image_def comb_defs ..
lemma "image f A b = (\<exists>x. f\<inverse> b x \<and> A x)" unfolding image_def set_defs comb_defs ..

(*Analogously, the term "preimage f" denotes a set-operation that takes a set 'B' and returns the 
  set of those elements which 'f' maps to some element in 'B'.*)
definition preimage::"('a \<Rightarrow> 'b) \<Rightarrow> Set('b) \<Rightarrow> Set('a)"
  where "preimage \<equiv> \<^bold>C \<^bold>B" (*i.e. (;) *)

lemma "preimage f B = f ; B" unfolding preimage_def comb_defs ..
lemma "preimage f B = (\<lambda>a. B (f a))" unfolding preimage_def comb_defs ..


declare image_def[func_defs] preimage_def[func_defs]

(*Introduce convenient notation*)
notation(input) image ("\<lparr>_ _\<rparr>") and preimage ("\<lparr>_ _\<rparr>\<inverse>")
notation(output) image ("\<lparr>'(_') '(_')\<rparr>") and preimage ("\<lparr>'(_') '(_')\<rparr>\<inverse>")

term "\<lparr>f A\<rparr>" (*read "the image of A under f" *)
term "\<lparr>f B\<rparr>\<inverse> = (\<lambda>a. B (f a))"  (* read "the image of A under f" *)

(*Range can be defined in terms of image as expected*)
lemma range_def2: "range = \<^bold>C image \<UU>"
  unfolding comb_defs func_defs set_defs by simp

term "preimage (f::'a\<Rightarrow>'b) \<circ> image f" 
term "image (f::'a\<Rightarrow>'b) \<circ> preimage f"

lemma "preimage f \<circ> image f = (\<lambda>A. \<lambda>a. f\<^sup>= a \<sqinter> A)"  (* TODO: make definitions out of these? *)
  unfolding func_defs set_defs comb_defs by metis
lemma "image f \<circ> preimage f = (\<lambda>B. \<lambda>b. f\<inverse> b \<sqinter> preimage f B)" 
  unfolding func_defs set_defs comb_defs by metis


(*Structure-preservation under set-operations*)
lemma image_morph1: "image (f \<circ> g) = image f \<circ> image g"
  unfolding func_defs set_defs comb_defs by auto
lemma image_morph2: "image \<^bold>I = \<^bold>I" 
  unfolding func_defs set_defs comb_defs by simp
lemma preimage_morph1: "preimage (f \<circ> g) = preimage g \<circ> preimage f" 
  unfolding func_defs comb_defs ..
lemma preimage_morph2: "preimage \<^bold>I = \<^bold>I" 
  unfolding func_defs comb_defs ..


subsection \<open>Monads\<close>

subsubsection \<open>Environment (aka. reader) monad\<close>

(*We can conceive of functional types of the form 'a \<Rightarrow> 'b as arising via an 'environmentalization', 
 or 'indexation' of the type 'b by the type 'a, i.e. as 'a-Env('b) using our type notation. 
 This type constructor comes with a monad structure (and is thus an applicative and a functor too).*)

abbreviation(input) unit_env::"'a \<Rightarrow> 'e-Env('a)"
  where "unit_env  \<equiv> \<^bold>K"
abbreviation(input) fmap_env::"('a \<Rightarrow> 'b) \<Rightarrow> 'e-Env('a) \<Rightarrow> 'e-Env('b)"
  where "fmap_env  \<equiv> \<^bold>B"
abbreviation(input) join_env::"'e-Env('e-Env('a)) \<Rightarrow> 'e-Env('a)"
  where "join_env  \<equiv> \<^bold>W"
abbreviation(input) ap_env::"'e-Env('a \<Rightarrow> 'b) \<Rightarrow> 'e-Env('a) \<Rightarrow> 'e-Env('b)"
  where "ap_env    \<equiv> \<^bold>S"
abbreviation(input) rbind_env::"('a \<Rightarrow> 'e-Env('b)) \<Rightarrow> 'e-Env('a) \<Rightarrow> 'e-Env('b)"
  where "rbind_env \<equiv> \<^bold>\<Sigma>" (*reversed bind*)

(*We define the customary bind operation as 'flipped' rbind (which seems more intuitive)*)
abbreviation(input) bind_env::"'e-Env('a) \<Rightarrow> ('a \<Rightarrow> 'e-Env('b)) \<Rightarrow> 'e-Env('b)"
  where "bind_env \<equiv> \<^bold>C rbind_env"
(*but we could have also given it a direct alternative definition*)
lemma "bind_env = \<^bold>W \<circ>\<^sub>2 (\<^bold>C \<^bold>B)" unfolding comb_defs ..

(*Some properties of monads in general*)
lemma "rbind_env = join_env \<circ>\<^sub>2 fmap_env" unfolding comb_defs ..
lemma "join_env = rbind_env \<^bold>I" unfolding comb_defs ..
(*...*)

(*Some properties of this particular monad*)
lemma "ap_env = rbind_env \<circ> \<^bold>C" unfolding comb_defs ..
(*...*)

(*The so-called "monad laws". They guarantee that monad-related term operations compose reliably.*)
abbreviation(input) "LawBind1 unit bind \<equiv> \<forall>f a. (bind (unit a) f) = (f a)" (*left identity*)
abbreviation(input) "LawBind2 unit bind \<equiv> \<forall>A. (bind A unit) = A" (*right identity*)
abbreviation(input) "LawBind3  bind \<equiv> \<forall>A f g. (bind A (\<lambda>a. bind (f a) g)) = bind (bind A f) g" (*associativity*)

(*Verifies compliance with the monad laws*)
lemma "LawBind1 unit_env bind_env" unfolding comb_defs by simp
lemma "LawBind2 unit_env bind_env" unfolding comb_defs by simp
lemma "LawBind3 bind_env" unfolding comb_defs by simp


subsubsection \<open>Identity monad\<close>

(*This is the degenerate (trivial?) case of the monad notion above for an identity type constructor*)

abbreviation(input) unit_id::"'a \<Rightarrow> 'a"
  where "unit_id \<equiv> \<^bold>I"
abbreviation(input) fmap_id::"('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  where "fmap_id \<equiv> \<^bold>A"
abbreviation(input) join_id::"'a \<Rightarrow> 'a"
  where "join_id \<equiv> \<^bold>I"
abbreviation(input) ap_id::"('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  where "ap_id \<equiv> \<^bold>A"
abbreviation(input) rbind_id::"('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  where "rbind_id \<equiv> \<^bold>A"
abbreviation(input) bind_id::"'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b"
  where "bind_id \<equiv> \<^bold>T"

lemma "LawBind1 unit_id bind_id" unfolding comb_defs by simp
lemma "LawBind2 unit_id bind_id" unfolding comb_defs by simp
lemma "LawBind3 bind_id" unfolding comb_defs by simp


subsection \<open>Miscellaneous\<close>

(*Function 'update' or 'override' at a point*)
definition update :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b" ("_[_\<mapsto>_]")
  where "f[a \<mapsto> b] \<equiv> \<lambda>x. if x = a then b else f x"

declare update_def[func_defs]


(*Random-looking simplification(?) rule that becomes useful later on (TODO: interpret)*)
lemma image_simp1: "image ((G \<circ> R) a) \<circ> image (\<^bold>T a) = image (\<^bold>T a) \<circ> image (\<^bold>S (G \<circ> R))"
  apply(rule ext) unfolding comb_defs set_defs func_defs by fastforce

end