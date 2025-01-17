theory combinators (*  A theory of generalized 'many-dimensional' combinators  *)
  imports Main
begin

no_notation (*hides notation from the library, so we can reintroduce those symbols later on*)
  Fun.comp (infixl "\<circ>" 55) and Fun.comp (infixl "o" 55)


section \<open>Many-dimensional combinators\<close>
(*We introduce several convenient definitions for families of (arity-extended variants of) combinators.*)

named_theorems comb_defs (*container for combinator-related definitions*)


subsection \<open>Appliers and identity\<close>
(*The first family of combinators \<^bold>A\<^sub>m will be called "appliers". They take m + 1 arguments, and return
 the application of the first argument (an m-ary function) to the remaining ones.*)

definition A1_comb :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("\<^bold>A\<^sub>1")
  where "\<^bold>A\<^sub>1 \<equiv> \<lambda>f g. f g"  (* (unary) function application (@); cf. reverse-pipe (<|) *)
definition A2_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c" ("\<^bold>A\<^sub>2")
  where "\<^bold>A\<^sub>2 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2. f g\<^sub>1 g\<^sub>2" (* function application (binary case) *)
definition A3_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd" ("\<^bold>A\<^sub>3")
  where "\<^bold>A\<^sub>3 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 g\<^sub>3. f g\<^sub>1 g\<^sub>2 g\<^sub>3" (* function application (ternary case) *)

notation A1_comb ("\<^bold>A") (* default notation for unary case *)

(*The identity combinator \<^bold>I (suitably typed) generalizes all \<^bold>A\<^sub>m combinators (via polymorphism and \<eta>-reduction).*)
definition I_comb :: "'a \<Rightarrow> 'a" ("\<^bold>I")
  where "\<^bold>I \<equiv> \<lambda>x. x"

notation I_comb ("\<^bold>A\<^sub>0") (* identity \<^bold>I can be interpreted as a 'degenerate' case (m = 0) of an applier*)

lemma "\<^bold>A\<^sub>1 = \<^bold>I" unfolding A1_comb_def I_comb_def ..
lemma "\<^bold>A\<^sub>2 = \<^bold>I" unfolding A2_comb_def I_comb_def ..
lemma "\<^bold>A\<^sub>3 = \<^bold>I" unfolding A3_comb_def I_comb_def ..
(*...and so on*)

declare A1_comb_def[comb_defs] A2_comb_def[comb_defs] A3_comb_def[comb_defs] I_comb_def[comb_defs]


subsection \<open>Compositors\<close>

(*The family of combinators \<^bold>B\<^sub>N are called "compositors" (with N an m-sized sequence of arities).
 They compose their first argument 'f' (an m-ary function) with m functions 'g\<^sub>i\<^sub>\<le>\<^sub>m' (each of arity N\<^sub>i).
 Thus, the returned function has arity: \<Sigma>\<^sub>i\<^sub>\<le>\<^sub>m N\<^sub>i *)
abbreviation(input) B0_comb :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("\<^bold>B\<^sub>0")  
  where "\<^bold>B\<^sub>0 \<equiv> \<^bold>A\<^sub>1"  (* composing with a nullary function corresponds to (unary) function application*)
definition B1_comb :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'b" ("\<^bold>B\<^sub>1")
  where "\<^bold>B\<^sub>1 \<equiv> \<lambda>f g x. f (g x)" (* the traditional \<^bold>B combinator*)
definition B2_comb :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'b" ("\<^bold>B\<^sub>2")
  where "\<^bold>B\<^sub>2 \<equiv> \<lambda>f g x y. f (g x y)" (* cf. Smullyan's "blackbird" combinator *)
definition B3_comb :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'b" ("\<^bold>B\<^sub>3")
  where "\<^bold>B\<^sub>3 \<equiv> \<lambda>f g x y z. f (g x y z)"
definition B4_comb :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'b" ("\<^bold>B\<^sub>4")
  where "\<^bold>B\<^sub>4 \<equiv> \<lambda>f g x y z w. f (g x y z w)"
(*... and so on*)
abbreviation(input) B00_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c" ("\<^bold>B\<^sub>0\<^sub>0")  
  where "\<^bold>B\<^sub>0\<^sub>0 \<equiv> \<^bold>A\<^sub>2"  (* composing with two nullary functions corresponds to binary function application*)
definition B01_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> ('d \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'c" ("\<^bold>B\<^sub>0\<^sub>1")
  where "\<^bold>B\<^sub>0\<^sub>1 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>2. f g\<^sub>1 (g\<^sub>2 x\<^sub>2)"       (* \<^bold>D combinator (cf. Smullyan's "dove")*)
definition B02_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> ('d \<Rightarrow> 'e \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'c" ("\<^bold>B\<^sub>0\<^sub>2")
  where "\<^bold>B\<^sub>0\<^sub>2 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>2 y\<^sub>2. f g\<^sub>1 (g\<^sub>2 x\<^sub>2 y\<^sub>2)" (* \<^bold>E combinator (cf. Smullyan's "eagle")*)
(*... and so on*)
definition B10_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'd \<Rightarrow> 'c" ("\<^bold>B\<^sub>1\<^sub>0")
  where "\<^bold>B\<^sub>1\<^sub>0 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>1. f (g\<^sub>1 x\<^sub>1) g\<^sub>2"
definition B11_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'a) \<Rightarrow> ('e \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'c" ("\<^bold>B\<^sub>1\<^sub>1")
  where "\<^bold>B\<^sub>1\<^sub>1 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>1 x\<^sub>2. f (g\<^sub>1 x\<^sub>1) (g\<^sub>2 x\<^sub>2)"
definition B12_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'a) \<Rightarrow> ('e \<Rightarrow> 'f \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'c" ("\<^bold>B\<^sub>1\<^sub>2")
  where "\<^bold>B\<^sub>1\<^sub>2 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>1 x\<^sub>2 y\<^sub>2. f (g\<^sub>1 x\<^sub>1) (g\<^sub>2 x\<^sub>2 y\<^sub>2)"
(*... and so on*)
definition B20_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'e \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'c" ("\<^bold>B\<^sub>2\<^sub>0")
  where "\<^bold>B\<^sub>2\<^sub>0 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>1 y\<^sub>1. f (g\<^sub>1 x\<^sub>1 y\<^sub>1) g\<^sub>2"
definition B21_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'e \<Rightarrow> 'a) \<Rightarrow> ('f \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'f \<Rightarrow> 'e \<Rightarrow> 'c" ("\<^bold>B\<^sub>2\<^sub>1")
  where "\<^bold>B\<^sub>2\<^sub>1 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>1 x\<^sub>2 y\<^sub>1. f (g\<^sub>1 x\<^sub>1 y\<^sub>1) (g\<^sub>2 x\<^sub>2)"
definition B22_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'e \<Rightarrow> 'a) \<Rightarrow> ('f \<Rightarrow> 'g \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'f \<Rightarrow> 'e \<Rightarrow> 'g \<Rightarrow> 'c" ("\<^bold>B\<^sub>2\<^sub>2")
  where "\<^bold>B\<^sub>2\<^sub>2 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>1 x\<^sub>2 y\<^sub>1 y\<^sub>2. f (g\<^sub>1 x\<^sub>1 y\<^sub>1) (g\<^sub>2 x\<^sub>2 y\<^sub>2)"
(*... and so on*)
abbreviation(input) B000_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd"("\<^bold>B\<^sub>0\<^sub>0\<^sub>0")  
  where "\<^bold>B\<^sub>0\<^sub>0\<^sub>0 \<equiv> \<^bold>A\<^sub>3"  (* composing with three nullary functions corresponds to ternary function application*)
(*... and so on*)
definition B111_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('e \<Rightarrow> 'a) \<Rightarrow> ('f \<Rightarrow> 'b) \<Rightarrow> ('g \<Rightarrow> 'c) \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'd" ("\<^bold>B\<^sub>1\<^sub>1\<^sub>1")
  where "\<^bold>B\<^sub>1\<^sub>1\<^sub>1 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 g\<^sub>3 x\<^sub>1 x\<^sub>2 x\<^sub>3. f (g\<^sub>1 x\<^sub>1) (g\<^sub>2 x\<^sub>2) (g\<^sub>3 x\<^sub>3)"
(*... and so on*)
definition B222_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('e \<Rightarrow> 'f \<Rightarrow> 'a) \<Rightarrow> ('g \<Rightarrow> 'h \<Rightarrow> 'b) \<Rightarrow> ('i \<Rightarrow> 'j \<Rightarrow> 'c) \<Rightarrow> 'e \<Rightarrow> 'g \<Rightarrow> 'i \<Rightarrow> 'f \<Rightarrow> 'h \<Rightarrow> 'j \<Rightarrow> 'd" ("\<^bold>B\<^sub>2\<^sub>2\<^sub>2")
  where "\<^bold>B\<^sub>2\<^sub>2\<^sub>2 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 g\<^sub>3 x\<^sub>1 x\<^sub>2 x\<^sub>3 y\<^sub>1 y\<^sub>2 y\<^sub>3. f (g\<^sub>1 x\<^sub>1 y\<^sub>1) (g\<^sub>2 x\<^sub>2 y\<^sub>2) (g\<^sub>3 x\<^sub>3 y\<^sub>3)"
(*... and so on*)

notation B1_comb ("\<^bold>B") (*the traditional \<^bold>B combinator corresponds to \<^bold>B\<^sub>1*)

declare B1_comb_def[comb_defs] B2_comb_def[comb_defs] B3_comb_def[comb_defs] B4_comb_def[comb_defs]        
        B01_comb_def[comb_defs] B02_comb_def[comb_defs] 
        B10_comb_def[comb_defs] B11_comb_def[comb_defs] B12_comb_def[comb_defs] 
        B20_comb_def[comb_defs] B21_comb_def[comb_defs] B22_comb_def[comb_defs]
        B111_comb_def[comb_defs] B222_comb_def[comb_defs]

(* Alternative notations for known "compositors" in the literature *)
notation B01_comb ("\<^bold>D") (* aliasing \<^bold>B\<^sub>0\<^sub>1 as \<^bold>D (cf. Smullyan's "dove" combinator)*)
notation B02_comb ("\<^bold>E") (* aliasing \<^bold>B\<^sub>0\<^sub>2 as \<^bold>E (cf. Smullyan's "eagle" combinator)*)
(*TODO: find others*)


subsection \<open>Permutators\<close>

(*The family of combinators \<^bold>C\<^sub>N are called "permutators", where N an m-sized sequence of (different) 
 numbers indicating a permutation on the arguments of the first argument (an m-ary function).*)
(*Binary permutators (2 in total)*)
abbreviation(input) C12_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c" ("\<^bold>C\<^sub>1\<^sub>2")  
  where "\<^bold>C\<^sub>1\<^sub>2 \<equiv> \<^bold>A\<^sub>2"           (*trivial case (no permutation): binary function application *)
definition C21_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c" ("\<^bold>C\<^sub>2\<^sub>1")
  where "\<^bold>C\<^sub>2\<^sub>1 \<equiv> \<lambda>f x\<^sub>1 x\<^sub>2. f x\<^sub>2 x\<^sub>1"
(*Ternary permutators (6 in total)*)
abbreviation(input) C123_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd" ("\<^bold>C\<^sub>1\<^sub>2\<^sub>3")  
  where "\<^bold>C\<^sub>1\<^sub>2\<^sub>3 \<equiv> \<^bold>A\<^sub>3"          (*trivial case (no permutation): ternary function application *)
abbreviation(input) C213_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> 'd" ("\<^bold>C\<^sub>2\<^sub>1\<^sub>3")  
  where "\<^bold>C\<^sub>2\<^sub>1\<^sub>3 \<equiv> \<^bold>C\<^sub>2\<^sub>1"         (*permutation \<^bold>C\<^sub>2\<^sub>1\<^sub>3 corresponds to \<^bold>C\<^sub>2\<^sub>1 (flipping the first two arguments) *)
definition C132_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> 'b \<Rightarrow> 'd" ("\<^bold>C\<^sub>1\<^sub>3\<^sub>2")
  where "\<^bold>C\<^sub>1\<^sub>3\<^sub>2 \<equiv> \<lambda>f x\<^sub>1 x\<^sub>2 x\<^sub>3. f x\<^sub>1 x\<^sub>3 x\<^sub>2"
definition C231_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'd" ("\<^bold>C\<^sub>2\<^sub>3\<^sub>1")
  where "\<^bold>C\<^sub>2\<^sub>3\<^sub>1 \<equiv> \<lambda>f x\<^sub>1 x\<^sub>2 x\<^sub>3. f x\<^sub>2 x\<^sub>3 x\<^sub>1"
definition C312_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> 'd" ("\<^bold>C\<^sub>3\<^sub>1\<^sub>2")
  where "\<^bold>C\<^sub>3\<^sub>1\<^sub>2 \<equiv> \<lambda>f x\<^sub>1 x\<^sub>2 x\<^sub>3. f x\<^sub>3 x\<^sub>1 x\<^sub>2"
definition C321_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'c \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'd" ("\<^bold>C\<^sub>3\<^sub>2\<^sub>1")
  where "\<^bold>C\<^sub>3\<^sub>2\<^sub>1 \<equiv> \<lambda>f x\<^sub>1 x\<^sub>2 x\<^sub>3. f x\<^sub>3 x\<^sub>2 x\<^sub>1"
(*Quaternary permutators (24 in total) we define some below (the rest are added on demand)*)
abbreviation(input) C2134_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e" ("\<^bold>C\<^sub>2\<^sub>1\<^sub>3\<^sub>4")  
  where "\<^bold>C\<^sub>2\<^sub>1\<^sub>3\<^sub>4 \<equiv> \<^bold>C\<^sub>2\<^sub>1"    (*permutation \<^bold>C\<^sub>2\<^sub>1\<^sub>3\<^sub>4 corresponds to \<^bold>C\<^sub>2\<^sub>1 (flipping the first two arguments) *)
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
  where "\<^bold>C\<^sub>3\<^sub>4\<^sub>1\<^sub>2 \<equiv> \<lambda>f x\<^sub>1 x\<^sub>2 x\<^sub>3 x\<^sub>4. f x\<^sub>3 x\<^sub>4 x\<^sub>1 x\<^sub>2" (* note that arguments are flipped pairwise*)
(*... and so on*)

(*Introduce some convenient notations*)
notation C21_comb ("\<^bold>C") (*the traditional flip/transposition (\<^bold>C) combinator is \<^bold>C\<^sub>2\<^sub>1*)
notation C231_comb ("\<^bold>R") (*Right (counterclockwise) rotation of a ternary function*)
notation C312_comb ("\<^bold>L") (*Left (counterclockwise) rotation of a ternary function*)
notation C3412_comb ("\<^bold>C\<^sub>2") (*pairwise flip/transposition of the arguments of a quaternary function*)

declare C21_comb_def[comb_defs] 
      C132_comb_def[comb_defs]  C231_comb_def[comb_defs] C312_comb_def[comb_defs]  C321_comb_def[comb_defs] 
      C1324_comb_def[comb_defs] C1423_comb_def[comb_defs] C2143_comb_def[comb_defs] C2314_comb_def[comb_defs]
      C3142_comb_def[comb_defs] C3412_comb_def[comb_defs]


subsection \<open>Cancellators\<close>

(*The next family of combinators \<^bold>K\<^sub>m\<^sub>n are called "cancellators". They take m arguments and return the
  n-th one (thus ignoring or 'cancelling' all others)*)
abbreviation(input) K11_comb::"'a \<Rightarrow> 'a" ("\<^bold>K\<^sub>1\<^sub>1")  
  where "\<^bold>K\<^sub>1\<^sub>1 \<equiv> \<^bold>I"          (*trivial/degenerate case m = 1: identity combinator \<^bold>I*) 
definition K21_comb::"'a \<Rightarrow> 'b \<Rightarrow> 'a" ("\<^bold>K\<^sub>2\<^sub>1")
  where "\<^bold>K\<^sub>2\<^sub>1 \<equiv> \<lambda>x y. x"    (*the traditional \<^bold>K combinator*)
definition K22_comb::"'a \<Rightarrow> 'b \<Rightarrow> 'b" ("\<^bold>K\<^sub>2\<^sub>2")
  where "\<^bold>K\<^sub>2\<^sub>2 \<equiv> \<lambda>x y. y"
definition K31_comb::"'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'a" ("\<^bold>K\<^sub>3\<^sub>1")
  where "\<^bold>K\<^sub>3\<^sub>1 \<equiv> \<lambda>x y z. x"
definition K32_comb::"'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'b" ("\<^bold>K\<^sub>3\<^sub>2")
  where "\<^bold>K\<^sub>3\<^sub>2 \<equiv> \<lambda>x y z. y"
definition K33_comb::"'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c" ("\<^bold>K\<^sub>3\<^sub>3")
  where "\<^bold>K\<^sub>3\<^sub>3 \<equiv> \<lambda>x y z. z"
(*... and so on*)

notation K21_comb ("\<^bold>K") (* aliasing \<^bold>K\<^sub>2\<^sub>1 as \<^bold>K *)

declare K21_comb_def[comb_defs] K22_comb_def[comb_defs] 
        K31_comb_def[comb_defs] K32_comb_def[comb_defs] K33_comb_def[comb_defs]


subsection \<open>Contractors\<close>

(*The following family of combinators \<^bold>W\<^sub>m\<^sub>n are called "contractors" (aka. "duplicators"). They take an
 (m*n)-ary function 'f' and contract/merge its arguments m-times, thus returning an n-ary function*)
abbreviation(input) W11_comb :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("\<^bold>W\<^sub>1\<^sub>1")  
  where "\<^bold>W\<^sub>1\<^sub>1 \<equiv> \<^bold>A\<^sub>1"          (* for the degenerate case m = 1:  W\<^sub>1\<^sub>n = \<^bold>A\<^sub>n *) 
abbreviation(input) W12_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c" ("\<^bold>W\<^sub>1\<^sub>2")  
  where "\<^bold>W\<^sub>1\<^sub>2 \<equiv> \<^bold>A\<^sub>2"          
abbreviation(input) W13_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd" ("\<^bold>W\<^sub>1\<^sub>3")  
  where "\<^bold>W\<^sub>1\<^sub>3 \<equiv> \<^bold>A\<^sub>3"   
(*... and so on*)
definition W21_comb :: "('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("\<^bold>W\<^sub>2\<^sub>1")
  where "\<^bold>W\<^sub>2\<^sub>1 \<equiv> \<lambda>f x. f x x"
definition W22_comb :: "('a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c" ("\<^bold>W\<^sub>2\<^sub>2")
  where "\<^bold>W\<^sub>2\<^sub>2 \<equiv> \<lambda>f x y. f x x y y"
definition W23_comb :: "('a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd" ("\<^bold>W\<^sub>2\<^sub>3")
  where "\<^bold>W\<^sub>2\<^sub>3 \<equiv> \<lambda>f x y z. f x x y y z z"
(*... and so on*)
definition W31_comb :: "('a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("\<^bold>W\<^sub>3\<^sub>1")
  where "\<^bold>W\<^sub>3\<^sub>1 \<equiv> \<lambda>f x. f x x x"
definition W32_comb :: "('a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c" ("\<^bold>W\<^sub>3\<^sub>2")
  where "\<^bold>W\<^sub>3\<^sub>2 \<equiv> \<lambda>f x y. f x x x y y y"
definition W33_comb :: "('a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd" ("\<^bold>W\<^sub>3\<^sub>3")
  where "\<^bold>W\<^sub>3\<^sub>3 \<equiv> \<lambda>f x y z. f x x x y y y z z z"
(*... and so on*)

notation W21_comb ("\<^bold>W") (*the traditional \<^bold>W combinator corresponds to \<^bold>W\<^sub>2\<^sub>1*)

declare W21_comb_def[comb_defs] W31_comb_def[comb_defs] 
        W22_comb_def[comb_defs] W23_comb_def[comb_defs]
        W32_comb_def[comb_defs]


subsection \<open>Fusers\<close> (*TODO: find a better name*)

(*The families \<^bold>S\<^sub>m (resp. \<^bold>\<Sigma>\<^sub>m) generalize the combinator \<^bold>S (resp. its evil twin \<^bold>\<Sigma>) to higher arities.*)
definition S1_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c" ("\<^bold>S\<^sub>1")
  where "\<^bold>S\<^sub>1 \<equiv> \<lambda>f g x. f x (g x)"
definition S2_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'd" ("\<^bold>S\<^sub>2")
  where "\<^bold>S\<^sub>2 \<equiv> \<lambda>f g x y. f x y (g x y)"
definition S3_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'e" ("\<^bold>S\<^sub>3")
  where "\<^bold>S\<^sub>3 \<equiv> \<lambda>f g x y z. f x y z (g x y z)"
definition \<Sigma>1_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'c" ("\<^bold>\<Sigma>\<^sub>1")
  where "\<^bold>\<Sigma>\<^sub>1 \<equiv> \<lambda>f g x. f (g x) x "  (* same as: \<^bold>B \<^bold>S\<^sub>1 \<^bold>C*)
definition \<Sigma>2_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd" ("\<^bold>\<Sigma>\<^sub>2")
  where "\<^bold>\<Sigma>\<^sub>2 \<equiv> \<lambda>f g x y. f (g x y) x y"  (* same as: \<^bold>B \<^bold>S\<^sub>2 \<^bold>L*)
definition \<Sigma>3_comb  :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e" ("\<^bold>\<Sigma>\<^sub>3")
  where "\<^bold>\<Sigma>\<^sub>3 \<equiv> \<lambda>f g x y z. f (g x y z) x y z"

notation S1_comb ("\<^bold>S")
notation \<Sigma>1_comb ("\<^bold>\<Sigma>")

declare S1_comb_def[comb_defs] S2_comb_def[comb_defs] S3_comb_def[comb_defs]
        \<Sigma>1_comb_def[comb_defs] \<Sigma>2_comb_def[comb_defs] \<Sigma>3_comb_def[comb_defs]


subsection \<open>Miscellaneous\<close>
(* Further combinators that often appear in the literature*)

(*Following ones represent 'reversed' function application*)
definition T_comb::"'b \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<^bold>T")
  where "\<^bold>T \<equiv> \<lambda>x y. y x"  (*unary case; cf. 'Let', 'pipe' (|>) , 'member' (\<in>), Smullyan's "thrush" *)
definition V_comb::"'b \<Rightarrow> 'c \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<^bold>V")
  where "\<^bold>V \<equiv> \<lambda>x y z. z x y" (*binary case; cf. 'pairing' in \<lambda>-calculus, Smullyan's "vireo"*)

(* TODO: where does this one come from?*)
definition J_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b" ("\<^bold>J")
  where "\<^bold>J \<equiv> \<lambda>f y v w. f y (f w v)" 
(*... more*)

declare T_comb_def[comb_defs] V_comb_def[comb_defs] J_comb_def[comb_defs]


subsection \<open>Derived combinator families\<close>

subsubsection \<open>Preprocessors\<close>
(*The family of \<^bold>\<Psi>\<^sub>m combinators below are cases of compositors. They take an m-ary function 'f' and 
 prepend to each of its m inputs  a given unary function 'g' (acting as a "preprocessor"). *)

abbreviation(input) \<Psi>1_comb :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'b" ("\<^bold>\<Psi>\<^sub>1")  
  where "\<^bold>\<Psi>\<^sub>1 \<equiv> \<^bold>B"            (*trivial case m = 1 corresponds to the \<^bold>B combinator *) 
definition \<Psi>2_comb :: "('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'b" ("\<^bold>\<Psi>\<^sub>2")
  where "\<^bold>\<Psi>\<^sub>2 \<equiv> \<lambda>f g x y. f (g x) (g y)" (*cf. "\<Psi>" in Curry 1931; "on" in Haskell Data.Function package*)
definition \<Psi>3_comb :: "('a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'b" ("\<^bold>\<Psi>\<^sub>3")
  where "\<^bold>\<Psi>\<^sub>3 \<equiv> \<lambda>f g x y z. f (g x) (g y) (g z)"
definition \<Psi>4_comb :: "('a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'b" ("\<^bold>\<Psi>\<^sub>4")
  where "\<^bold>\<Psi>\<^sub>4 \<equiv> \<lambda>f g x y z u. f (g x) (g y) (g z) (g u)"
(*... and so on*)

declare \<Psi>2_comb_def[comb_defs] \<Psi>3_comb_def[comb_defs] \<Psi>4_comb_def[comb_defs]


subsubsection \<open>Imitators\<close>
(*The combinators \<^bold>\<Phi>\<^sub>m\<^sub>n are called "imitators". They compose a m-ary function 'f' with m functions 'g\<^sub>i\<^sub>\<le>\<^sub>m'
 (having arity n each) by sharing their input arguments, so as to return an n-ary function.
 They can be seen as a kind of 'input-merging compositors'. These combinators are quite convenient 
 and appear often in the literature, e.g., as "trains" in array languages like APL and BQN, and also
 as "imitation bindings" in higher-order (pre-)unification algorithms, where they take their name from.*)

abbreviation(input) \<Phi>11_comb :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'b" ("\<^bold>\<Phi>\<^sub>1\<^sub>1")  
  where "\<^bold>\<Phi>\<^sub>1\<^sub>1 \<equiv> \<^bold>B\<^sub>1"        (* each \<^bold>\<Phi>\<^sub>1\<^sub>n corresponds in fact to \<^bold>B\<^sub>n *)
abbreviation(input) \<Phi>12_comb :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'b" ("\<^bold>\<Phi>\<^sub>1\<^sub>2")  
  where "\<^bold>\<Phi>\<^sub>1\<^sub>2 \<equiv> \<^bold>B\<^sub>2"            
abbreviation(input) \<Phi>13_comb :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'b" ("\<^bold>\<Phi>\<^sub>1\<^sub>3")  
  where "\<^bold>\<Phi>\<^sub>1\<^sub>3 \<equiv> \<^bold>B\<^sub>3"            
abbreviation(input) \<Phi>14_comb :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'b"  ("\<^bold>\<Phi>\<^sub>1\<^sub>4")  
  where "\<^bold>\<Phi>\<^sub>1\<^sub>4 \<equiv> \<^bold>B\<^sub>4"            
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

declare \<Phi>21_comb_def[comb_defs] \<Phi>22_comb_def[comb_defs] \<Phi>31_comb_def[comb_defs] \<Phi>32_comb_def[comb_defs]


subsubsection \<open>Projectors\<close>
(* The family of projectors \<^bold>O\<^sub>l\<^sub>m\<^sub>n features three parameters: l = total number of arguments;
 m (\<le> l) = the index of the projection (\<le> l); n = the arity of the (projected) m-th argument.
 They appear as "projection bindings" in higher-order (pre-)unification algorithms. *)

abbreviation(input) O110_comb :: "'a \<Rightarrow> 'a" ("\<^bold>O\<^sub>1\<^sub>1\<^sub>0")  
  where "\<^bold>O\<^sub>1\<^sub>1\<^sub>0 \<equiv> \<^bold>I"       (*trivial case corresponds to the identity combinator \<^bold>I *) 
definition O111_comb :: "(('a \<Rightarrow> 'b) \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b" ("\<^bold>O\<^sub>1\<^sub>1\<^sub>1") (* Smullyan's "owl" *)
  where "\<^bold>O\<^sub>1\<^sub>1\<^sub>1 \<equiv> \<lambda>h f. f (h f)"
definition O112_comb :: "(('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a) \<Rightarrow> (('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'c" ("\<^bold>O\<^sub>1\<^sub>1\<^sub>2")
  where "\<^bold>O\<^sub>1\<^sub>1\<^sub>2 \<equiv> \<lambda>h\<^sub>1 h\<^sub>2 f. f (h\<^sub>1 f) (h\<^sub>2 f)"
definition O113_comb :: "(('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a) \<Rightarrow> (('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'b) 
     \<Rightarrow> (('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'd" ("\<^bold>O\<^sub>1\<^sub>1\<^sub>3")
  where "\<^bold>O\<^sub>1\<^sub>1\<^sub>3 \<equiv> \<lambda>h\<^sub>1 h\<^sub>2 h\<^sub>3 f. f (h\<^sub>1 f) (h\<^sub>2 f) (h\<^sub>3 f)"
(*...and so on *)
abbreviation(input) O210_comb :: "'a \<Rightarrow> 'b \<Rightarrow> 'a" ("\<^bold>O\<^sub>2\<^sub>1\<^sub>0")  
  where "\<^bold>O\<^sub>2\<^sub>1\<^sub>0 \<equiv> \<^bold>K\<^sub>2\<^sub>1"       (*trivial case corresponds to the combinator \<^bold>K\<^sub>2\<^sub>1 (i.e. \<^bold>K) *) 
definition O211_comb :: "(('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'b"  ("\<^bold>O\<^sub>2\<^sub>1\<^sub>1")
  where "\<^bold>O\<^sub>2\<^sub>1\<^sub>1 \<equiv> \<lambda>h x y. x (h x y)"
definition O212_comb :: "(('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'd \<Rightarrow> 'a) 
      \<Rightarrow> (('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'd \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'd \<Rightarrow> 'c" ("\<^bold>O\<^sub>2\<^sub>1\<^sub>2")
  where "\<^bold>O\<^sub>2\<^sub>1\<^sub>2 \<equiv> \<lambda>h\<^sub>1 h\<^sub>2 x y. x (h\<^sub>1 x y) (h\<^sub>2 x y)"
(*...and so on *)
abbreviation(input) O220_comb :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"("\<^bold>O\<^sub>2\<^sub>2\<^sub>0")  
  where "\<^bold>O\<^sub>2\<^sub>2\<^sub>0 \<equiv> \<^bold>K\<^sub>2\<^sub>2"       (*trivial case corresponds to the combinator \<^bold>K\<^sub>2\<^sub>2 *) 
definition O221_comb :: "('a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'c"  ("\<^bold>O\<^sub>2\<^sub>2\<^sub>1")
  where "\<^bold>O\<^sub>2\<^sub>2\<^sub>1 \<equiv> \<lambda>h x y. y (h x y)"
definition O222_comb :: "('a \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'b) 
      \<Rightarrow> ('a \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'd" ("\<^bold>O\<^sub>2\<^sub>2\<^sub>2")
  where "\<^bold>O\<^sub>2\<^sub>2\<^sub>2 \<equiv> \<lambda>h\<^sub>1 h\<^sub>2 x y. y (h\<^sub>1 x y) (h\<^sub>2 x y)"
(*...and so on *)

declare O111_comb_def[comb_defs] O112_comb_def[comb_defs] O113_comb_def[comb_defs]
        O211_comb_def[comb_defs] O212_comb_def[comb_defs] 
        O221_comb_def[comb_defs] O222_comb_def[comb_defs] 

notation O111_comb ("\<^bold>O") (* aliasing \<^bold>O\<^sub>1\<^sub>1\<^sub>1 as \<^bold>O (cf. Smullyan's "owl" combinator) *)


subsection \<open>Special combinator notations\<close>

(*We introduce a convenient superscript notation for the \<^bold>C\<^sub>2\<^sub>1/\<^bold>C combinator, highlighting its role as a
 transposition operation that flips/swaps the arguments of a (curried) binary function.*)
notation(input) C21_comb ("(_)\<Zcat>")
notation(output) C21_comb ("'(_')\<Zcat>")

(*We introduce a convenient infix notation for the \<^bold>\<Phi>\<^sub>1\<^sub>n family of combinators (and their transposes)
  in their role as special generalized forms of function composition.
 We write "\<^bold>\<Phi>\<^sub>1\<^sub>1 f g" as "f \<circ> g" and "\<^bold>\<Phi>\<^sub>1\<^sub>n f g" as "f \<circ>\<^sub>n g" (for n > 1)*)
notation \<Phi>11_comb (infixl "\<circ>" 55)
notation \<Phi>12_comb (infixl "\<circ>\<^sub>2" 55)
notation \<Phi>13_comb (infixl "\<circ>\<^sub>3" 55)
notation \<Phi>14_comb (infixl "\<circ>\<^sub>4" 55)
abbreviation(input) \<Phi>11_comb_t (infixr ";" 55)
  where "f ; g \<equiv> g \<circ> f"
abbreviation(input) \<Phi>12_comb_t (infixr ";\<^sub>2" 55)
  where "f ;\<^sub>2 g \<equiv> g \<circ>\<^sub>2 f"
abbreviation(input) \<Phi>13_comb_t (infixr ";\<^sub>3" 55)
  where "f ;\<^sub>3 g \<equiv> g \<circ>\<^sub>3 f"
abbreviation(input) \<Phi>14_comb_t (infixr ";\<^sub>4" 55)
  where "f ;\<^sub>4 g \<equiv> g \<circ>\<^sub>4 f"

(*Checks*)
lemma "(f \<circ> g \<circ> h) = (h ; g ; f)" unfolding comb_defs ..
lemma "(f \<circ>\<^sub>2 g) = (g ;\<^sub>2 f)" unfolding comb_defs ..

(*Recalling...*)
lemma "\<^bold>T = \<^bold>A\<Zcat>" unfolding comb_defs .. 

(*Convenient infix notation for the \<^bold>A and its transpose (\<^bold>T combinator) in their role as function application.*)
notation(input) T_comb (infixl "|>" 54) (*the beloved 'pipe' (note lower prio than composition) *)
notation(input) A1_comb (infixr "<|" 54)

lemma "(a |> f) = f a" unfolding comb_defs ..
lemma "(a |> f |> g) = g (f a)" unfolding comb_defs ..
lemma "(a |> f |> g) = (a |> f ; g)" unfolding comb_defs ..
lemma "(a |> f |> g) = (g \<circ> f <| a)" unfolding comb_defs ..


subsection \<open>Combinator interrelations\<close> (*TODO: clean up, organize and expand*)

(*Composing compositors*)

(*\<^bold>\<Phi>\<^sub>m\<^sub>n can be defined by composing \<^bold>\<Phi>\<^sub>m\<^sub>(\<^sub>n\<^sub>-\<^sub>1\<^sub>) with itself*)
lemma "\<^bold>\<Phi>\<^sub>2\<^sub>2 = \<^bold>\<Phi>\<^sub>2\<^sub>1 \<circ> \<^bold>\<Phi>\<^sub>2\<^sub>1" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>3\<^sub>2 = \<^bold>\<Phi>\<^sub>3\<^sub>1 \<circ> \<^bold>\<Phi>\<^sub>3\<^sub>1" unfolding comb_defs ..

(*Moreover, \<^bold>\<Phi>\<^sub>m\<^sub>n is definable by composing \<^bold>W\<^sub>n\<^sub>m and \<^bold>B\<^sub>N, via the following schema: \<^bold>\<Phi>\<^sub>m\<^sub>n = \<^bold>W\<^sub>m\<^sub>n \<circ>\<^sub>m\<^sub>+\<^sub>1 \<^bold>B\<^sub>N 
 (where N is an m-sized array of ns)*)
lemma "\<^bold>\<Phi>\<^sub>1\<^sub>2 = \<^bold>W\<^sub>1\<^sub>2 \<circ>\<^sub>2 \<^bold>B\<^sub>2" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>1\<^sub>3 = \<^bold>W\<^sub>1\<^sub>3 \<circ>\<^sub>2 \<^bold>B\<^sub>3" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>2\<^sub>1 = \<^bold>W\<^sub>2\<^sub>1 \<circ>\<^sub>3 \<^bold>B\<^sub>1\<^sub>1" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>2\<^sub>2 = \<^bold>W\<^sub>2\<^sub>2 \<circ>\<^sub>3 \<^bold>B\<^sub>2\<^sub>2" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>3\<^sub>1 = \<^bold>W\<^sub>3\<^sub>1 \<circ>\<^sub>4 \<^bold>B\<^sub>1\<^sub>1\<^sub>1" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>3\<^sub>2 = \<^bold>W\<^sub>3\<^sub>2 \<circ>\<^sub>4 \<^bold>B\<^sub>2\<^sub>2\<^sub>2" unfolding comb_defs ..
(*...*)

(*TODO: verify \<^bold>B\<^sub>(\<^sub>a\<^sub>+\<^sub>b\<^sub>)\<^sub>(\<^sub>c\<^sub>+\<^sub>d\<^sub>) = \<^bold>B\<^sub>a\<^sub>b \<circ> \<^bold>B\<^sub>c\<^sub>d*)
lemma "\<^bold>B\<^sub>1\<^sub>1 = \<^bold>B\<^sub>1\<^sub>1 \<circ> \<^bold>B\<^sub>0\<^sub>0" unfolding comb_defs ..
lemma "\<^bold>B\<^sub>1\<^sub>1 = \<^bold>B\<^sub>1\<^sub>0 \<circ> \<^bold>B\<^sub>0\<^sub>1" unfolding comb_defs ..
(*...*)
lemma "\<^bold>B\<^sub>1\<^sub>2 = \<^bold>B\<^sub>1\<^sub>2 \<circ> \<^bold>B\<^sub>0\<^sub>0" unfolding comb_defs ..
lemma "\<^bold>B\<^sub>1\<^sub>2 = \<^bold>B\<^sub>1\<^sub>1 \<circ> \<^bold>B\<^sub>0\<^sub>1" unfolding comb_defs ..
(*...*)
lemma "\<^bold>B\<^sub>2\<^sub>0 = \<^bold>B\<^sub>1\<^sub>0 \<circ> \<^bold>B\<^sub>1\<^sub>0" unfolding comb_defs ..
lemma "\<^bold>B\<^sub>2\<^sub>1 = \<^bold>B\<^sub>1\<^sub>1 \<circ> \<^bold>B\<^sub>1\<^sub>0" unfolding comb_defs ..
lemma "\<^bold>B\<^sub>2\<^sub>2 = \<^bold>B\<^sub>1\<^sub>1 \<circ> \<^bold>B\<^sub>1\<^sub>1" unfolding comb_defs ..

(*TODO: verify \<^bold>B\<^sub>(\<^sub>a\<^sub>+\<^sub>d\<^sub>)\<^sub>(\<^sub>b\<^sub>+\<^sub>e\<^sub>)\<^sub>(\<^sub>c\<^sub>+\<^sub>f\<^sub>) = \<^bold>B\<^sub>a\<^sub>b\<^sub>c \<circ> \<^bold>B\<^sub>d\<^sub>e\<^sub>f*)
lemma "\<^bold>B\<^sub>2\<^sub>2\<^sub>2 = \<^bold>B\<^sub>1\<^sub>1\<^sub>1 \<circ> \<^bold>B\<^sub>1\<^sub>1\<^sub>1" unfolding comb_defs ..
(*... more*)


(*Projectors can be defined in terms of \<^bold>S and \<^bold>K *)
lemma "\<^bold>O\<^sub>1\<^sub>1\<^sub>1 = \<^bold>S \<^bold>K\<^sub>1\<^sub>1" unfolding comb_defs ..
lemma "\<^bold>O\<^sub>2\<^sub>1\<^sub>1 = \<^bold>S\<^sub>2 \<^bold>K\<^sub>2\<^sub>1" unfolding comb_defs ..
lemma "\<^bold>O\<^sub>2\<^sub>2\<^sub>1 = \<^bold>S\<^sub>2 \<^bold>K\<^sub>2\<^sub>2" unfolding comb_defs ..
(*... more*)


(***Miscellaneous***)
lemma "\<^bold>B\<^sub>2\<Zcat> \<^bold>A = \<^bold>B" unfolding comb_defs ..
lemma "\<^bold>W\<^sub>3\<^sub>1 = \<^bold>B\<^bold>W\<^bold>W" unfolding comb_defs ..
(*...*)

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
lemma "\<^bold>L \<^bold>A\<^sub>2 = (\<lambda>x y f. f x y)" unfolding comb_defs ..
lemma "\<^bold>B\<Zcat> = (\<lambda>f g x. g (f x))" unfolding comb_defs ..
lemma "\<^bold>B\<^sub>2\<Zcat> = (\<lambda>f g x y. g (f x y))" unfolding comb_defs ..
lemma "\<^bold>\<Psi>\<^sub>2\<Zcat> = (\<lambda>f g x y. g (f x) (f y))" unfolding comb_defs ..
lemma "\<^bold>L \<^bold>\<Phi>\<^sub>2\<^sub>1 = (\<lambda>h\<^sub>1 h\<^sub>2 f x. f (h\<^sub>1 x) (h\<^sub>2 x))" unfolding comb_defs ..
lemma "\<^bold>L \<^bold>\<Phi>\<^sub>2\<^sub>2 = (\<lambda>h\<^sub>1 h\<^sub>2 f x y. f (h\<^sub>1 x y) (h\<^sub>2 x y))" unfolding comb_defs ..

lemma Tcomb_def2: "\<^bold>T = \<^bold>I\<Zcat>" unfolding comb_defs ..
lemma Tcomb_def3: "\<^bold>T = \<^bold>A\<Zcat>" unfolding comb_defs ..
lemma Icomb_def2: "\<^bold>I = \<^bold>T\<Zcat>" unfolding comb_defs ..
lemma Acomb_def3: "\<^bold>A = \<^bold>T\<Zcat>" unfolding comb_defs ..
lemma "\<^bold>I = \<^bold>A" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>2\<^sub>1 = \<^bold>B (\<^bold>B \<^bold>S) \<^bold>B" unfolding comb_defs ..

lemma "\<^bold>A\<^sub>2 f = f" unfolding comb_defs ..
lemma "\<^bold>R \<^bold>V f = f" unfolding comb_defs ..
lemma Vcomb_def2: "\<^bold>V = \<^bold>L \<^bold>A\<^sub>2" unfolding comb_defs ..
lemma Vcomb_def3: "\<^bold>V = \<^bold>L \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>I = \<^bold>R \<^bold>V" unfolding comb_defs ..
lemma "\<^bold>R \<^bold>V = \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>V = \<^bold>L \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>L \<^bold>V = \<^bold>R \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>A\<^sub>2 = \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>A\<^sub>2 = \<^bold>L(\<^bold>R \<^bold>I)" unfolding comb_defs ..

lemma "\<^bold>L(X\<Zcat>) = (\<^bold>R X)\<Zcat>" unfolding comb_defs ..
lemma "\<^bold>L(\<^bold>I\<Zcat>) = (\<^bold>R \<^bold>I)\<Zcat>" unfolding comb_defs ..
lemma "(\<^bold>L \<^bold>I)\<Zcat> = \<^bold>R(\<^bold>I\<Zcat>)" unfolding comb_defs ..

lemma "\<^bold>B\<^sub>2\<^sub>0 h g = (\<^bold>B\<^sub>2\<^sub>1 h g \<^bold>I)\<Zcat>" unfolding comb_defs ..

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
lemma "\<^bold>A\<Zcat> = \<^bold>S (\<^bold>K (\<^bold>S (\<^bold>S \<^bold>K \<^bold>K))) \<^bold>K"  unfolding comb_defs ..
lemma "\<^bold>A\<Zcat> = \<^bold>I\<Zcat>" unfolding comb_defs ..
(*...*)

(*\<^bold>S can itself be defined in terms of other combinators*)
lemma "\<^bold>S = \<^bold>B (\<^bold>B (\<^bold>B \<^bold>W) \<^bold>C) (\<^bold>B \<^bold>B)" unfolding comb_defs ..
lemma "\<^bold>S = \<^bold>B (\<^bold>B \<^bold>W)(\<^bold>B \<^bold>B \<^bold>C)" unfolding comb_defs ..
lemma "\<^bold>S = \<^bold>B \<^bold>\<Sigma> \<^bold>C" unfolding comb_defs ..
lemma "\<^bold>S = \<^bold>B (\<^bold>T \<^bold>C) \<^bold>B \<^bold>\<Sigma>" unfolding comb_defs ..

lemma "\<^bold>\<Sigma> = \<^bold>B (\<^bold>B \<^bold>W) \<^bold>B" unfolding comb_defs .. 
lemma "\<^bold>\<Sigma> = \<^bold>B \<^bold>S \<^bold>C" unfolding comb_defs ..
lemma "\<^bold>\<Sigma>\<^sub>2 = \<^bold>B \<^bold>S\<^sub>2 \<^bold>L" unfolding comb_defs ..
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
lemma "\<^bold>B\<^sub>2 = \<^bold>B \<^bold>B \<^bold>B" unfolding comb_defs ..
lemma "\<^bold>\<Sigma> = \<^bold>B\<^sub>2 \<^bold>W \<^bold>B" unfolding comb_defs ..

end