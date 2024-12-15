theory combinators (*  A theory of generalized (arity-extended) combinators  *)
  imports Main
begin

no_notation (*hides notation from the library, so we can reintroduce those symbols later on*)
  Fun.comp (infixl "\<circ>" 55) and Fun.comp (infixl "o" 55)


section \<open>Generalized Combinators\<close>

named_theorems comb_defs (*container for combinator-related definitions*)

subsection \<open>Combinator definition\<close>

(*We refer to the next family combinators \<^bold>B\<^sub>m\<^sub>N as "compositors" (with N an m-array of numbers).
 They compose a given m-ary function 'f' with m functions 'g\<^sub>i' (i \<le> m) (each with arity N\<^sub>i),
 and return the composition of 'f' with all g\<^sub>is as a function (with arity: \<Sigma>\<^sub>i\<^sub>\<le>\<^sub>m N(i)). *)
definition B10_comb :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("\<^bold>B\<^sub>1\<^sub>0")
  where "\<^bold>B\<^sub>1\<^sub>0 \<equiv> \<lambda>f g. f g"
definition B11_comb :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'b" ("\<^bold>B\<^sub>1\<^sub>1")
  where "\<^bold>B\<^sub>1\<^sub>1 \<equiv> \<lambda>f g x. f (g x)"
definition B12_comb :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'b" ("\<^bold>B\<^sub>1\<^sub>2")
  where "\<^bold>B\<^sub>1\<^sub>2 \<equiv> \<lambda>f g x y. f (g x y)" (* cf. Smullyan's "blackbird" *)
definition B13_comb :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'b" ("\<^bold>B\<^sub>1\<^sub>3")
  where "\<^bold>B\<^sub>1\<^sub>3 \<equiv> \<lambda>f g x y z. f (g x y z)"
definition B14_comb :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'b" ("\<^bold>B\<^sub>1\<^sub>4")
  where "\<^bold>B\<^sub>1\<^sub>4 \<equiv> \<lambda>f g x y z w. f (g x y z w)"
(*... and so on*)
definition B200_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c" ("\<^bold>B\<^sub>2\<^sub>0\<^sub>0")
  where "\<^bold>B\<^sub>2\<^sub>0\<^sub>0 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2. f g\<^sub>1 g\<^sub>2"
definition B201_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> ('d \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'c" ("\<^bold>B\<^sub>2\<^sub>0\<^sub>1")
  where "\<^bold>B\<^sub>2\<^sub>0\<^sub>1 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>2. f g\<^sub>1 (g\<^sub>2 x\<^sub>2)" (* \<^bold>D combinator (cf. Smullyan's "dove")*)
definition B202_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> ('d \<Rightarrow> 'e \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'c" ("\<^bold>B\<^sub>2\<^sub>0\<^sub>2")
  where "\<^bold>B\<^sub>2\<^sub>0\<^sub>2 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>2 y\<^sub>2. f g\<^sub>1 (g\<^sub>2 x\<^sub>2 y\<^sub>2)" (* \<^bold>E combinator (cf. Smullyan's "eagle")*)
definition B210_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'd \<Rightarrow> 'c" ("\<^bold>B\<^sub>2\<^sub>1\<^sub>0")
  where "\<^bold>B\<^sub>2\<^sub>1\<^sub>0 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>1. f (g\<^sub>1 x\<^sub>1) g\<^sub>2"
definition B211_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'a) \<Rightarrow> ('e \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'c" ("\<^bold>B\<^sub>2\<^sub>1\<^sub>1")
  where "\<^bold>B\<^sub>2\<^sub>1\<^sub>1 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>1 x\<^sub>2. f (g\<^sub>1 x\<^sub>1) (g\<^sub>2 x\<^sub>2)"
definition B212_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'a) \<Rightarrow> ('e \<Rightarrow> 'f \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'c" ("\<^bold>B\<^sub>2\<^sub>1\<^sub>2")
  where "\<^bold>B\<^sub>2\<^sub>1\<^sub>2 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>1 x\<^sub>2 y\<^sub>2. f (g\<^sub>1 x\<^sub>1) (g\<^sub>2 x\<^sub>2 y\<^sub>2)"
definition B220_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'e \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'c" ("\<^bold>B\<^sub>2\<^sub>2\<^sub>0")
  where "\<^bold>B\<^sub>2\<^sub>2\<^sub>0 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>1 y\<^sub>1. f (g\<^sub>1 x\<^sub>1 y\<^sub>1) g\<^sub>2"
definition B221_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'e \<Rightarrow> 'a) \<Rightarrow> ('f \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'c" ("\<^bold>B\<^sub>2\<^sub>2\<^sub>1")
  where "\<^bold>B\<^sub>2\<^sub>2\<^sub>1 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>1 y\<^sub>1 x\<^sub>2. f (g\<^sub>1 x\<^sub>1 y\<^sub>1) (g\<^sub>2 x\<^sub>2)"
definition B222_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'e \<Rightarrow> 'a) \<Rightarrow> ('f \<Rightarrow> 'g \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'c" ("\<^bold>B\<^sub>2\<^sub>2\<^sub>2")
  where "\<^bold>B\<^sub>2\<^sub>2\<^sub>2 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>1 y\<^sub>1 x\<^sub>2 y\<^sub>2. f (g\<^sub>1 x\<^sub>1 y\<^sub>1) (g\<^sub>2 x\<^sub>2 y\<^sub>2)"
(*... and so on*)
definition B3000_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd" ("\<^bold>B\<^sub>3\<^sub>0\<^sub>0\<^sub>0")
  where "\<^bold>B\<^sub>3\<^sub>0\<^sub>0\<^sub>0 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 g\<^sub>3. f g\<^sub>1 g\<^sub>2 g\<^sub>3"
(*...*)
definition B3111_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('e \<Rightarrow> 'a) \<Rightarrow> ('f \<Rightarrow> 'b) \<Rightarrow> ('g \<Rightarrow> 'c) \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'd" ("\<^bold>B\<^sub>3\<^sub>1\<^sub>1\<^sub>1")
  where "\<^bold>B\<^sub>3\<^sub>1\<^sub>1\<^sub>1 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 g\<^sub>3 x\<^sub>1 x\<^sub>2 x\<^sub>3. f (g\<^sub>1 x\<^sub>1) (g\<^sub>2 x\<^sub>2) (g\<^sub>3 x\<^sub>3)"
(*...*)
definition B3222_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('e \<Rightarrow> 'f \<Rightarrow> 'a) \<Rightarrow> ('g \<Rightarrow> 'h \<Rightarrow> 'b) \<Rightarrow> ('i \<Rightarrow> 'j \<Rightarrow> 'c) \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'h \<Rightarrow> 'i \<Rightarrow> 'j \<Rightarrow> 'd" ("\<^bold>B\<^sub>3\<^sub>2\<^sub>2\<^sub>2")
  where "\<^bold>B\<^sub>3\<^sub>2\<^sub>2\<^sub>2 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 g\<^sub>3 x\<^sub>1 y\<^sub>1 x\<^sub>2 y\<^sub>2 x\<^sub>3 y\<^sub>3. f (g\<^sub>1 x\<^sub>1 y\<^sub>1) (g\<^sub>2 x\<^sub>2 y\<^sub>2) (g\<^sub>3 x\<^sub>3 y\<^sub>3)"
(*... and so on*)

declare B10_comb_def[comb_defs] B11_comb_def[comb_defs] B12_comb_def[comb_defs] B13_comb_def[comb_defs] B14_comb_def[comb_defs]
        B200_comb_def[comb_defs] B201_comb_def[comb_defs] B202_comb_def[comb_defs] 
        B210_comb_def[comb_defs] B211_comb_def[comb_defs] B212_comb_def[comb_defs]
        B220_comb_def[comb_defs] B221_comb_def[comb_defs] B222_comb_def[comb_defs]
        B3000_comb_def[comb_defs] B3111_comb_def[comb_defs] B3222_comb_def[comb_defs]

notation B11_comb ("\<^bold>B") (*the traditional \<^bold>B combinator corresponds to \<^bold>B\<^sub>1\<^sub>1*)
lemma "\<^bold>B f g = (\<lambda>x. f (g x))" unfolding comb_defs ..

(*Let \<^bold>A represent function application as a combinator. The family of \<^bold>A\<^sub>m (with n > 1) represent each 
 the (function) application of an m-ary function to m arguments. These combinators ("appliers") are
 in fact special cases of the "compositors" \<^bold>B\<^sub>m\<^sub>Z (with Z an m-array of zeroes)*)
notation B10_comb ("\<^bold>A") (*explicit function application (@) or reverse-pipe (<|)*)
lemma "\<^bold>A f x = f x" unfolding comb_defs ..
notation B200_comb ("\<^bold>A\<^sub>2") (* a convenient binary extension of \<^bold>A*)
lemma "\<^bold>A\<^sub>2 f x y = f x y" unfolding comb_defs ..

notation B201_comb ("\<^bold>D") (* aliasing \<^bold>B\<^sub>2\<^sub>0\<^sub>1 as \<^bold>D combinator (cf. Smullyan's "dove")*)
lemma "\<^bold>D f x g y = f x (g y)" unfolding comb_defs ..
notation B202_comb ("\<^bold>E") (* aliasing \<^bold>B\<^sub>2\<^sub>0\<^sub>2 as \<^bold>E combinator (cf. Smullyan's "eagle")*)
lemma "\<^bold>E f x g y z = f x (g y z)" unfolding comb_defs ..


(*We refer to the next family of combinators \<^bold>\<Phi>\<^sub>m\<^sub>n as (input-)merging compositors. They compose a given
 m-ary function 'f' with m (possibly identical) n-ary functions 'g\<^sub>i\<^sub>\<le>\<^sub>m', thus returning an n-ary function.
 These combinators are quite convenient and appear often in the literature, e.g., as "trains" in 
 array languages like APL and BQN, and also as term-builders in higher-order unification algorithms. 
 Later we will introduce special notation for them, and write "f \<circ>\<^sub>n \<langle>g\<^sub>1, ... g\<^sub>m\<rangle>" for "\<^bold>\<Phi>\<^sub>m\<^sub>n f g\<^sub>1 ... g\<^sub>m".*)
notation(input) B11_comb ("\<^bold>\<Phi>\<^sub>1\<^sub>1") 
notation(input) B12_comb ("\<^bold>\<Phi>\<^sub>1\<^sub>2") (* \<^bold>\<Phi>\<^sub>1\<^sub>n corresponds in fact to \<^bold>B\<^sub>1\<^sub>n *)
notation(input) B13_comb ("\<^bold>\<Phi>\<^sub>1\<^sub>3") 
notation(input) B14_comb ("\<^bold>\<Phi>\<^sub>1\<^sub>4") 
definition \<Phi>21_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'a) \<Rightarrow> ('d \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'c" ("\<^bold>\<Phi>\<^sub>2\<^sub>1")
  where "\<^bold>\<Phi>\<^sub>2\<^sub>1 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x. f (g\<^sub>1 x) (g\<^sub>2 x)" (*cf. "\<Phi>\<^sub>1" in Curry 1931; "liftA2" in Haskell; "monadic fork" in APL)*)
definition \<Phi>22_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'e \<Rightarrow> 'a) \<Rightarrow> ('d \<Rightarrow> 'e \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'c" ("\<^bold>\<Phi>\<^sub>2\<^sub>2")
  where "\<^bold>\<Phi>\<^sub>2\<^sub>2 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x y. f (g\<^sub>1 x y) (g\<^sub>2 x y)" (*cf. "\<Phi>\<^sub>2" in Curry 1931; "dyadic fork" in APL *)
(*...and so on *)
definition \<Phi>31_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('e \<Rightarrow> 'a) \<Rightarrow> ('e \<Rightarrow> 'b) \<Rightarrow> ('e \<Rightarrow> 'c) \<Rightarrow> 'e \<Rightarrow> 'd" ("\<^bold>\<Phi>\<^sub>3\<^sub>1")
  where "\<^bold>\<Phi>\<^sub>3\<^sub>1 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 g\<^sub>3 x. f (g\<^sub>1 x) (g\<^sub>2 x) (g\<^sub>3 x)"
definition \<Phi>32_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('e \<Rightarrow> 'f \<Rightarrow> 'a) \<Rightarrow> ('e \<Rightarrow> 'f \<Rightarrow> 'b) \<Rightarrow> ('e \<Rightarrow> 'f \<Rightarrow> 'c) \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'd" ("\<^bold>\<Phi>\<^sub>3\<^sub>2")
  where "\<^bold>\<Phi>\<^sub>3\<^sub>2 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 g\<^sub>3 x y. f (g\<^sub>1 x y) (g\<^sub>2 x y) (g\<^sub>3 x y)"
(*...and so on *)

declare \<Phi>21_comb_def[comb_defs] \<Phi>22_comb_def[comb_defs] 
        \<Phi>31_comb_def[comb_defs] \<Phi>32_comb_def[comb_defs]


(*The family of \<^bold>\<Psi>\<^sub>m combinators prepend a unary function (as a 'preprocessor') to each of the m inputs 
 of a given m-ary function (thus returning an m-ary function). *)
notation(input) B11_comb ("\<^bold>\<Psi>\<^sub>1") (* \<^bold>\<Psi>\<^sub>1 corresponds in fact to \<^bold>B\<^sub>1\<^sub>1 (aka \<^bold>B) *)
definition \<Psi>2_comb :: "('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'b" ("\<^bold>\<Psi>\<^sub>2")
  where "\<^bold>\<Psi>\<^sub>2 \<equiv> \<lambda>f g x y. f (g x) (g y)" (*cf. "\<Psi>" in Curry 1931; "on" in Haskell Data.Function package*)
definition \<Psi>3_comb :: "('a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'b" ("\<^bold>\<Psi>\<^sub>3")
  where "\<^bold>\<Psi>\<^sub>3 \<equiv> \<lambda>f g x y z. f (g x) (g y) (g z)"
definition \<Psi>4_comb :: "('a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'b" ("\<^bold>\<Psi>\<^sub>4")
  where "\<^bold>\<Psi>\<^sub>4 \<equiv> \<lambda>f g x y z u. f (g x) (g y) (g z) (g u)"
(*... and so on*)

declare \<Psi>2_comb_def[comb_defs] \<Psi>3_comb_def[comb_defs] \<Psi>4_comb_def[comb_defs]


(*The next family of combinators \<^bold>K\<^sub>m\<^sub>n are called 'projectors' (or more traditionally: 'cancellators'). 
 They take m arguments and return the n-th one (thus ignoring or 'cancelling' all others)*)
definition K11_comb::"'a \<Rightarrow> 'a" ("\<^bold>K\<^sub>1\<^sub>1")
  where "\<^bold>K\<^sub>1\<^sub>1 \<equiv> \<lambda>x. x"
definition K21_comb::"'a \<Rightarrow> 'b \<Rightarrow> 'a" ("\<^bold>K\<^sub>2\<^sub>1")
  where "\<^bold>K\<^sub>2\<^sub>1 \<equiv> \<lambda>x y. x"
definition K22_comb::"'a \<Rightarrow> 'b \<Rightarrow> 'b" ("\<^bold>K\<^sub>2\<^sub>2")
  where "\<^bold>K\<^sub>2\<^sub>2 \<equiv> \<lambda>x y. y"
definition K31_comb::"'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'a" ("\<^bold>K\<^sub>3\<^sub>1")
  where "\<^bold>K\<^sub>3\<^sub>1 \<equiv> \<lambda>x y z. x"
definition K32_comb::"'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'b" ("\<^bold>K\<^sub>3\<^sub>2")
  where "\<^bold>K\<^sub>3\<^sub>2 \<equiv> \<lambda>x y z. y"
definition K33_comb::"'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c" ("\<^bold>K\<^sub>3\<^sub>3")
  where "\<^bold>K\<^sub>3\<^sub>3 \<equiv> \<lambda>x y z. z"

declare K11_comb_def[comb_defs] K21_comb_def[comb_defs] 
        K31_comb_def[comb_defs] K32_comb_def[comb_defs] K33_comb_def[comb_defs]

notation K11_comb ("\<^bold>I") (*the identity combinator \<^bold>I corresponds to \<^bold>K\<^sub>1\<^sub>1*)
lemma "\<^bold>I = (\<lambda>x. x)" unfolding K11_comb_def ..
notation K21_comb ("\<^bold>K") (*the traditional \<^bold>K combinator is \<^bold>K\<^sub>2\<^sub>1*)
lemma "\<^bold>K = (\<lambda>x y. x)" unfolding K21_comb_def ..


(*The following family of combinators \<^bold>C\<^sub>N are called "permutators" where N is a sequence of numbers
(of size m for m-ary input function) indicating the permutation on the arguments of the function. *)
(*Binary permutators (2 in total)*)
notation(input) B200_comb ("\<^bold>C\<^sub>1\<^sub>2") (*i.e. \<^bold>A\<^sub>2 *)
definition C21_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c" ("\<^bold>C\<^sub>2\<^sub>1")
  where "\<^bold>C\<^sub>2\<^sub>1 \<equiv> \<lambda>f x\<^sub>1 x\<^sub>2. f x\<^sub>2 x\<^sub>1"
(*Ternary permutators (6 in total)*)
notation B3000_comb ("\<^bold>C\<^sub>1\<^sub>2\<^sub>3")  (* \<^bold>C\<^sub>1\<^sub>2\<^sub>3 is the same as \<^bold>A\<^sub>3 (leaves arguments unchanged)*) 
notation C21_comb ("\<^bold>C\<^sub>2\<^sub>1\<^sub>3")  (* \<^bold>C\<^sub>2\<^sub>1\<^sub>3 is the same as \<^bold>C\<^sub>2\<^sub>1 (flipping the first two arguments) *)
definition C132_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> 'b \<Rightarrow> 'd" ("\<^bold>C\<^sub>1\<^sub>3\<^sub>2")
  where "\<^bold>C\<^sub>1\<^sub>3\<^sub>2 \<equiv> \<lambda>f x\<^sub>1 x\<^sub>2 x\<^sub>3. f x\<^sub>1 x\<^sub>3 x\<^sub>2"
definition C231_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'd" ("\<^bold>C\<^sub>2\<^sub>3\<^sub>1")
  where "\<^bold>C\<^sub>2\<^sub>3\<^sub>1 \<equiv> \<lambda>f x\<^sub>1 x\<^sub>2 x\<^sub>3. f x\<^sub>2 x\<^sub>3 x\<^sub>1"
definition C312_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> 'd" ("\<^bold>C\<^sub>3\<^sub>1\<^sub>2")
  where "\<^bold>C\<^sub>3\<^sub>1\<^sub>2 \<equiv> \<lambda>f x\<^sub>1 x\<^sub>2 x\<^sub>3. f x\<^sub>3 x\<^sub>1 x\<^sub>2"
definition C321_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'c \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'd" ("\<^bold>C\<^sub>3\<^sub>2\<^sub>1")
  where "\<^bold>C\<^sub>3\<^sub>2\<^sub>1 \<equiv> \<lambda>f x\<^sub>1 x\<^sub>2 x\<^sub>3. f x\<^sub>3 x\<^sub>2 x\<^sub>1"
(*Quaternary permutators (24 in total) we add some below (more on demand)*)
notation C21_comb ("\<^bold>C\<^sub>2\<^sub>1\<^sub>3\<^sub>4")  (* \<^bold>C\<^sub>2\<^sub>1\<^sub>3\<^sub>4 is the same as \<^bold>C\<^sub>2\<^sub>1 (flipping the first two arguments) *)
definition C1324_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> 'b \<Rightarrow> 'd \<Rightarrow> 'e" ("\<^bold>C\<^sub>1\<^sub>3\<^sub>2\<^sub>4")
  where "\<^bold>C\<^sub>1\<^sub>3\<^sub>2\<^sub>4 \<equiv> \<lambda>f x\<^sub>1 x\<^sub>2 x\<^sub>3 x\<^sub>4. f x\<^sub>1 x\<^sub>3 x\<^sub>2 x\<^sub>4"
definition C1423_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'b \<Rightarrow> 'e" ("\<^bold>C\<^sub>1\<^sub>4\<^sub>2\<^sub>3")
  where "\<^bold>C\<^sub>1\<^sub>4\<^sub>2\<^sub>3 \<equiv> \<lambda>f x\<^sub>1 x\<^sub>2 x\<^sub>3 x\<^sub>4. f x\<^sub>1 x\<^sub>4 x\<^sub>2 x\<^sub>3"
definition C2143_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'd \<Rightarrow> 'c \<Rightarrow> 'e"("\<^bold>C\<^sub>2\<^sub>1\<^sub>4\<^sub>3")
  where "\<^bold>C\<^sub>2\<^sub>1\<^sub>4\<^sub>3 \<equiv> \<lambda>f x\<^sub>1 x\<^sub>2 x\<^sub>3 x\<^sub>4. f x\<^sub>2 x\<^sub>1 x\<^sub>4 x\<^sub>3"
definition C2314_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'd \<Rightarrow> 'e" ("\<^bold>C\<^sub>2\<^sub>3\<^sub>1\<^sub>4")
  where "\<^bold>C\<^sub>2\<^sub>3\<^sub>1\<^sub>4 \<equiv> \<lambda>f x\<^sub>1 x\<^sub>2 x\<^sub>3 x\<^sub>4. f x\<^sub>2 x\<^sub>3 x\<^sub>1 x\<^sub>4"
definition C3142_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> 'b \<Rightarrow> 'd \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> 'e" ("\<^bold>C\<^sub>3\<^sub>1\<^sub>4\<^sub>2")
  where "\<^bold>C\<^sub>3\<^sub>1\<^sub>4\<^sub>2 \<equiv> \<lambda>f x\<^sub>1 x\<^sub>2 x\<^sub>3 x\<^sub>4. f x\<^sub>3 x\<^sub>1 x\<^sub>4 x\<^sub>2"
definition C3412_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'e" ("\<^bold>C\<^sub>3\<^sub>4\<^sub>1\<^sub>2")
  where "\<^bold>C\<^sub>3\<^sub>4\<^sub>1\<^sub>2 \<equiv> \<lambda>f x\<^sub>1 x\<^sub>2 x\<^sub>3 x\<^sub>4. f x\<^sub>3 x\<^sub>4 x\<^sub>1 x\<^sub>2"
(*... more*)

declare C21_comb_def[comb_defs] 
      C132_comb_def[comb_defs]  C231_comb_def[comb_defs]      
      C312_comb_def[comb_defs]  C321_comb_def[comb_defs] 
      C1324_comb_def[comb_defs] C1423_comb_def[comb_defs]
      C2143_comb_def[comb_defs] C2314_comb_def[comb_defs]
      C3142_comb_def[comb_defs] C3412_comb_def[comb_defs]

notation C21_comb ("\<^bold>C") (*the traditional flip/transposition (\<^bold>C) combinator is \<^bold>C\<^sub>2\<^sub>1*)
notation C231_comb ("\<^bold>R") (*Right (counterclockwise) rotation of a ternary function*)
notation C312_comb ("\<^bold>L") (*Left (counterclockwise) rotation of a ternary function*)


(*The following family of combinators \<^bold>W\<^sub>m\<^sub>n are called "contractors" ("duplicators"). They take an
 (m*n)-ary function 'f' and contract/merge its arguments m-times, thus returning an n-ary function*)   
definition W21_comb :: "('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("\<^bold>W\<^sub>2\<^sub>1")
  where "\<^bold>W\<^sub>2\<^sub>1 \<equiv> \<lambda>f x. f x x"
definition W22_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c" ("\<^bold>W\<^sub>2\<^sub>2")
  where "\<^bold>W\<^sub>2\<^sub>2 \<equiv> \<lambda>f x y. f x y x y"
definition W23_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd" ("\<^bold>W\<^sub>2\<^sub>3")
  where "\<^bold>W\<^sub>2\<^sub>3 \<equiv> \<lambda>f x y z. f x y z x y z"
definition W31_comb :: "('a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("\<^bold>W\<^sub>3\<^sub>1")
  where "\<^bold>W\<^sub>3\<^sub>1 \<equiv> \<lambda>f x. f x x x"
definition W32_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c" ("\<^bold>W\<^sub>3\<^sub>2")
  where "\<^bold>W\<^sub>3\<^sub>2 \<equiv> \<lambda>f x y. f x y x y x y"

declare W21_comb_def[comb_defs] W31_comb_def[comb_defs] 
        W22_comb_def[comb_defs] W23_comb_def[comb_defs]
        W32_comb_def[comb_defs]

notation W21_comb ("\<^bold>W") (*the traditional \<^bold>W combinator corresponds to \<^bold>W\<^sub>2\<^sub>1*)

lemma "\<^bold>W\<^sub>3\<^sub>1 = \<^bold>B\<^bold>W\<^bold>W" unfolding comb_defs ..


(**** Further combinators that appear in the literature****)

(*The infamous \<^bold>S combinator and its cousin*)
definition S_comb::"('b \<Rightarrow> 'c \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a" ("\<^bold>S")
  where "\<^bold>S \<equiv> \<lambda>f x w. f w (x w)"
definition \<Sigma>_comb::"('c \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a" ("\<^bold>\<Sigma>")
  where "\<^bold>\<Sigma> \<equiv> \<lambda>f x w. f (x w) w "  (* Same as: \<^bold>B \<^bold>S \<^bold>C*)

(*Following ones represent 'reversed' function application*)
definition T_comb::"'b \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<^bold>T")
  where "\<^bold>T \<equiv> \<lambda>x y. y x"  (*unary case; cf. 'Let', 'pipe' (|>) , 'member' (\<in>) *)
definition V_comb::"'b \<Rightarrow> 'c \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<^bold>V")
  where "\<^bold>V \<equiv> \<lambda>x y z. z x y" (*binary case; cf. 'pairing' in \<lambda>-calculus*)

(*The following 'loopy' combinators are very special and deserve further exploration *)
definition O_comb :: "(('a \<Rightarrow> 'b) \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b" ("\<^bold>O") (*Smullyan's Owl *)
  where "\<^bold>O \<equiv> \<lambda>f g. g (f g)"
definition J_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b" ("\<^bold>J") (* TODO: where does this come from?*)
  where "\<^bold>J \<equiv> \<lambda>f y v w. f y (f w v)" 
(*... more*)

declare S_comb_def[comb_defs] \<Sigma>_comb_def[comb_defs]
        T_comb_def[comb_defs] V_comb_def[comb_defs]
        O_comb_def[comb_defs] J_comb_def[comb_defs]


subsection \<open>Combinator notations\<close>

(*We introduce a convenient superscript notation for the \<^bold>C combinator, highlighting its role as a
 transposition operation that flips/swaps the arguments of a (curried) binary function.*)
notation(input) C21_comb ("(_)\<^sup>t")
notation(output) C21_comb ("'(_')\<^sup>t")
(*We extend previous notation for the extended transposition operation that flips/swaps pairwise
  the arguments of a (curried) quaternary function*)
notation(input) C3412_comb ("(_)\<^sup>t\<^sup>2")
notation(output) C3412_comb ("'(_')\<^sup>t\<^sup>2")

(*In a similar spirit, we add superscript notation to \<^bold>C\<^sub>3\<^sub>1\<^sub>2/\<^bold>L and \<^bold>C\<^sub>2\<^sub>3\<^sub>1/\<^bold>R combinators *)
notation(input) C312_comb ("(_)\<^sup>l") (* left (counterclockwise?) rotation*)
notation(output) C312_comb ("'(_')\<^sup>l")
notation(input) C231_comb ("(_)\<^sup>r") (* right (clockwise?) rotation*)
notation(output) C231_comb ("'(_')\<^sup>r")


(*We introduce a convenient infix notation for the \<^bold>\<Phi>\<^sub>m\<^sub>n family of combinators (and their transposes)
  in their role as special generalized forms of function composition.*)

(*For m = 1 we use an infix notation: "\<^bold>B|\<^bold>\<Phi>\<^sub>1\<^sub>1 f g" as "f \<circ> g" and "\<^bold>B\<^sub>1\<^sub>n|\<^bold>\<Phi>\<^sub>1\<^sub>n f g" as "f \<circ>\<^sub>n g" (for n > 1)*)
notation B11_comb (infixl "\<circ>" 55) (* since \<^bold>\<Phi>\<^sub>1\<^sub>1 is \<^bold>B\<^sub>1\<^sub>1 i.e. \<^bold>B *)
notation B12_comb (infixl "\<circ>\<^sub>2" 55) (* since \<^bold>\<Phi>\<^sub>1\<^sub>2 is \<^bold>B\<^sub>1\<^sub>2 (aka. Smullyan's 'blackbird')*)
notation B13_comb (infixl "\<circ>\<^sub>3" 55) (* since \<^bold>\<Phi>\<^sub>1\<^sub>3 is \<^bold>B\<^sub>1\<^sub>3*)
notation B14_comb (infixl "\<circ>\<^sub>4" 55) (* since \<^bold>\<Phi>\<^sub>1\<^sub>4 is \<^bold>B\<^sub>1\<^sub>4*)
abbreviation(input) B11_comb_t (infixr ";" 55)
  where "f ; g \<equiv> g \<circ> f"
abbreviation(input) B12_comb_t (infixr ";\<^sub>2" 55)
  where "f ;\<^sub>2 g \<equiv> g \<circ>\<^sub>2 f"
abbreviation(input) B13_comb_t (infixr ";\<^sub>3" 55)
  where "f ;\<^sub>3 g \<equiv> g \<circ>\<^sub>3 f"
abbreviation(input) B14_comb_t (infixr ";\<^sub>4" 55)
  where "f ;\<^sub>4 g \<equiv> g \<circ>\<^sub>4 f"

(*Checks*)
lemma "f \<circ> g \<circ> h = h ; g ; f" unfolding comb_defs ..
lemma "f \<circ>\<^sub>2 g = g ;\<^sub>2 f" unfolding comb_defs ..


(* For m > 1 we write "f \<circ> \<langle>g\<^sub>1, ... g\<^sub>m\<rangle>" when n = 1, and f \<circ>\<^sub>n \<langle>g\<^sub>1, ... g\<^sub>m\<rangle> when n > 1*)
notation \<Phi>21_comb ("_ \<circ> \<langle>_,_\<rangle>")
notation \<Phi>22_comb ("_ \<circ>\<^sub>2 \<langle>_,_\<rangle>")
notation \<Phi>31_comb ("_ \<circ> \<langle>_,_,_\<rangle>")
notation \<Phi>32_comb ("_ \<circ>\<^sub>2 \<langle>_,_,_\<rangle>")
abbreviation(input) \<Phi>21_transp ("\<langle>_,_\<rangle> ; _")
  where "\<langle>h,k\<rangle> ; g \<equiv> g \<circ> \<langle>h,k\<rangle>"
abbreviation(input) \<Phi>22_transp ("\<langle>_,_\<rangle> ;\<^sub>2 _")
  where "\<langle>h,k\<rangle> ;\<^sub>2 g \<equiv> g \<circ>\<^sub>2 \<langle>h,k\<rangle>"
abbreviation(input) \<Phi>31_transp ("\<langle>_,_,_\<rangle> ; _")
  where "\<langle>h,k,l\<rangle> ; g \<equiv> g \<circ> \<langle>h,k,l\<rangle>"
abbreviation(input) \<Phi>32_transp ("\<langle>_,_,_\<rangle> ;\<^sub>2 _")
  where "\<langle>h,k,l\<rangle> ;\<^sub>2 g \<equiv> g \<circ>\<^sub>2 \<langle>h,k,l\<rangle>"

lemma "g \<circ> \<langle>h,k\<rangle> = \<langle>h,k\<rangle> ; g" by simp
lemma "g \<circ>\<^sub>2 \<langle>h,k\<rangle> = \<langle>h,k\<rangle> ;\<^sub>2 g" by simp
lemma "g \<circ> \<langle>h,k,l\<rangle> = \<langle>h,k,l\<rangle> ; g" by simp
lemma "g \<circ>\<^sub>2 \<langle>h,k,l\<rangle> = \<langle>h,k,l\<rangle> ;\<^sub>2 g" by simp


(*Convenient infix notation for the \<^bold>A and its transpose (\<^bold>T combinator) in their role as function application.*)
lemma "\<^bold>T = \<^bold>A\<^sup>t" unfolding comb_defs .. (*recalling*)

notation(input) T_comb (infixl "|>" 54) (*the beloved 'pipe' *)
notation(input) B10_comb (infixr "<|" 54) (*note lower prio than composition*)

lemma "a |> f = f a" unfolding comb_defs ..
lemma "a |> f |> g = a |> f ; g" unfolding comb_defs ..
lemma "a |> f |> g = g \<circ> f <| a" unfolding comb_defs ..


subsection \<open>Combinator interrelations\<close> (*TODO: clean up, organize and expand*)

(*\<^bold>\<Phi>\<^sub>m\<^sub>n can be defined in terms of \<^bold>B\<^sub>m\<^sub>n\<^sub>n and \<^bold>W, using the schema: \<^bold>\<Phi>\<^sub>m\<^sub>n = (\<^bold>\<Phi>\<^sub>1\<^sub>(\<^sub>m\<^sub>+\<^sub>1\<^sub>) \<^bold>W\<^sub>m\<^sub>n) \<^bold>B\<^sub>m\<^sub>n\<^sub>n*)
lemma "\<^bold>\<Phi>\<^sub>2\<^sub>1 = (\<^bold>\<Phi>\<^sub>1\<^sub>3 \<^bold>W\<^sub>2\<^sub>1) \<^bold>B\<^sub>2\<^sub>1\<^sub>1" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>2\<^sub>2 = (\<^bold>\<Phi>\<^sub>1\<^sub>3 \<^bold>W\<^sub>2\<^sub>2) \<^bold>B\<^sub>2\<^sub>2\<^sub>2" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>3\<^sub>1 = (\<^bold>\<Phi>\<^sub>1\<^sub>4 \<^bold>W\<^sub>3\<^sub>1) \<^bold>B\<^sub>3\<^sub>1\<^sub>1\<^sub>1" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>3\<^sub>2 = (\<^bold>\<Phi>\<^sub>1\<^sub>4 \<^bold>W\<^sub>3\<^sub>2) \<^bold>B\<^sub>3\<^sub>2\<^sub>2\<^sub>2" unfolding comb_defs ..
(*...*)

(*Some properties*)
lemma "\<^bold>A x = x" unfolding comb_defs ..
lemma "\<^bold>B \<^bold>A x = x" unfolding comb_defs ..
(*...*)
lemma "\<^bold>B \<^bold>I x = x" unfolding comb_defs ..
lemma "\<^bold>B x \<^bold>I = x" unfolding comb_defs ..
lemma comb1_simp: "\<^bold>B \<^bold>C \<^bold>K  = \<^bold>B \<^bold>K " unfolding comb_defs ..
lemma comb2_simp: "(\<^bold>B \<^bold>C) ((\<^bold>B \<^bold>C) x) = x" unfolding comb_defs ..
lemma comb3_simp: "(\<^bold>B x) \<^bold>I = x" unfolding comb_defs ..
lemma comb4_simp: "\<^bold>C (\<^bold>C x) = x" unfolding comb_defs ..
lemma "\<^bold>W f = \<^bold>S f \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>W f = \<^bold>\<Sigma> f \<^bold>I" unfolding comb_defs ..
(********************************************)

(*Transposed/reversed variants for (some of) the previous combinators*)
lemma "\<^bold>A\<^sub>2\<^sup>l = (\<lambda>x y f. f x y)" unfolding comb_defs ..
lemma "\<^bold>B\<^sup>t = (\<lambda>f g x. g (f x))" unfolding comb_defs ..
lemma "\<^bold>B\<^sub>1\<^sub>2\<^sup>t = (\<lambda>f g x y. g (f x y))" unfolding comb_defs ..
lemma "\<^bold>\<Psi>\<^sub>2\<^sup>t = (\<lambda>f g x y. g (f x) (f y))" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>2\<^sub>1\<^sup>l = (\<lambda>h\<^sub>1 h\<^sub>2 f x. f (h\<^sub>1 x) (h\<^sub>2 x))" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>2\<^sub>2\<^sup>l = (\<lambda>h\<^sub>1 h\<^sub>2 f x y. f (h\<^sub>1 x y) (h\<^sub>2 x y))" unfolding comb_defs ..

lemma Tcomb_def2: "\<^bold>T = \<^bold>I\<^sup>t" unfolding comb_defs ..
lemma Tcomb_def3: "\<^bold>T = \<^bold>A\<^sup>t" unfolding comb_defs ..
lemma Icomb_def2: "\<^bold>I = \<^bold>T\<^sup>t" unfolding comb_defs ..
lemma Acomb_def3: "\<^bold>A = \<^bold>T\<^sup>t" unfolding comb_defs ..
lemma "\<^bold>I = \<^bold>A" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>2\<^sub>1 = \<^bold>B (\<^bold>B \<^bold>S) \<^bold>B" unfolding comb_defs ..

lemma "\<^bold>A\<^sub>2 f = f" unfolding comb_defs ..
lemma "\<^bold>V\<^sup>r f = f" unfolding comb_defs ..
lemma Vcomb_def2: "\<^bold>V = \<^bold>A\<^sub>2\<^sup>l" unfolding comb_defs ..
lemma Vcomb_def3: "\<^bold>V = \<^bold>I\<^sup>l" unfolding comb_defs ..
lemma "\<^bold>I = \<^bold>V\<^sup>r" unfolding comb_defs ..
lemma "\<^bold>V\<^sup>r = \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>V = \<^bold>I\<^sup>l" unfolding comb_defs ..
lemma "\<^bold>V\<^sup>l = \<^bold>I\<^sup>r" unfolding comb_defs ..
lemma "\<^bold>A\<^sub>2 = \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>A\<^sub>2 = \<^bold>I\<^sup>l\<^sup>r" unfolding comb_defs ..

lemma "X\<^sup>t\<^sup>l = X\<^sup>r\<^sup>t" unfolding comb_defs ..
lemma "\<^bold>I\<^sup>t\<^sup>l = \<^bold>I\<^sup>r\<^sup>t" unfolding comb_defs ..
lemma "\<^bold>I\<^sup>l\<^sup>t = \<^bold>I\<^sup>t\<^sup>r" unfolding comb_defs ..

lemma "\<^bold>B\<^sub>2\<^sub>2\<^sub>0 h g = (\<^bold>B\<^sub>2\<^sub>2\<^sub>1 h g \<^bold>I)\<^sup>r" unfolding comb_defs ..

(*...*)

(*We can show (via \<lambda>-conversion) that the combinators S and K can be used to define all others*)
lemma "\<^bold>B = \<^bold>S (\<^bold>K \<^bold>S) \<^bold>K" unfolding comb_defs ..
lemma "\<^bold>C = \<^bold>S (\<^bold>S (\<^bold>K (\<^bold>S (\<^bold>K \<^bold>S) \<^bold>K)) \<^bold>S) (\<^bold>K \<^bold>K)" unfolding comb_defs ..
lemma "\<^bold>C = \<^bold>S (\<^bold>B \<^bold>B \<^bold>S) (\<^bold>K \<^bold>K)" unfolding comb_defs ..
lemma "\<^bold>I = \<^bold>S \<^bold>K \<^bold>K" unfolding comb_defs ..
lemma "\<^bold>W = \<^bold>S \<^bold>S (\<^bold>S \<^bold>K)" unfolding comb_defs ..
lemma "\<^bold>W = \<^bold>\<Sigma> \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>W = \<^bold>C \<^bold>S \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>W = \<^bold>C \<^bold>\<Sigma> \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>I = \<^bold>W \<^bold>K" unfolding comb_defs ..
lemma "\<^bold>A\<^sup>t = \<^bold>S (\<^bold>K (\<^bold>S (\<^bold>S \<^bold>K \<^bold>K))) \<^bold>K"  unfolding comb_defs ..
lemma "\<^bold>A\<^sup>t = \<^bold>I\<^sup>t" unfolding comb_defs ..
(*...*)

(*\<^bold>S can itself be defined in terms of other combinators*)
lemma "\<^bold>S = \<^bold>B (\<^bold>B (\<^bold>B \<^bold>W) \<^bold>C) (\<^bold>B \<^bold>B)" unfolding comb_defs ..
lemma "\<^bold>S = \<^bold>B (\<^bold>B \<^bold>W)(\<^bold>B \<^bold>B \<^bold>C)" unfolding comb_defs ..
lemma "\<^bold>S = \<^bold>B \<^bold>\<Sigma> \<^bold>C" unfolding comb_defs ..
lemma "\<^bold>S = \<^bold>B (\<^bold>T \<^bold>C) \<^bold>B \<^bold>\<Sigma>" unfolding comb_defs ..

lemma "\<^bold>\<Sigma> = \<^bold>B (\<^bold>B \<^bold>W) \<^bold>B" unfolding comb_defs .. 
lemma "\<^bold>\<Sigma> = \<^bold>B \<^bold>S \<^bold>C" unfolding comb_defs ..
lemma "\<^bold>\<Sigma> = \<^bold>B (\<^bold>T \<^bold>C) \<^bold>B \<^bold>S" unfolding comb_defs ..

(*...*)

(*The rotation combinators (left and right) commute (wrt function composition)*)
lemma "\<^bold>I = \<^bold>B \<^bold>L (\<^bold>B \<^bold>L \<^bold>L)" unfolding comb_defs ..
lemma "\<^bold>I = \<^bold>B \<^bold>R (\<^bold>B \<^bold>R \<^bold>R)" unfolding comb_defs ..
lemma "\<^bold>R = \<^bold>B \<^bold>L \<^bold>L" unfolding comb_defs ..
lemma "\<^bold>L = \<^bold>B \<^bold>R \<^bold>R" unfolding comb_defs ..
lemma "\<^bold>B \<^bold>R \<^bold>L = \<^bold>B \<^bold>L \<^bold>R" unfolding comb_defs ..

lemma "\<^bold>D = \<^bold>B \<^bold>B" unfolding comb_defs ..
lemma "\<^bold>O = \<^bold>S \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>W = \<^bold>\<Sigma> \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>B\<^sub>1\<^sub>2 = \<^bold>B \<^bold>B \<^bold>B" unfolding comb_defs ..
lemma "\<^bold>\<Sigma> = \<^bold>B\<^sub>1\<^sub>2 \<^bold>W \<^bold>B" unfolding comb_defs ..

end