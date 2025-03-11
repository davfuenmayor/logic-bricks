theory combinators (*  A theory of generalized 'multi-dimensional' combinators  *)
  imports Main
begin

no_notation (*hides notation from the library, so we can reintroduce those symbols later on*)
  Fun.comp (infixl "\<circ>" 55) and Fun.comp (infixl "o" 55)


section \<open>Multi-dimensional combinators\<close>
(*We introduce several convenient definitions for families of (arity-extended variants of) combinators.*)

named_theorems comb_defs (*container for combinator-related definitions*)


subsection \<open>Identity and Appliers\<close>

(*The convenient all-purpose identity combinator*)
definition I_comb :: "'a \<Rightarrow> 'a" ("\<^bold>I")
  where "\<^bold>I \<equiv> \<lambda>x. x"

(*The family of combinators \<^bold>A\<^sub>m are called "appliers". They take m + 1 arguments, and return the 
 application of the first argument (an m-ary function) to the remaining ones.*)
abbreviation(input) A0_comb :: "'a \<Rightarrow> 'a" ("\<^bold>A\<^sub>0")
  where "\<^bold>A\<^sub>0 \<equiv> \<^bold>I" (* degenerate case (m = 0) corresponds to identity \<^bold>I *)
definition A1_comb :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("\<^bold>A\<^sub>1")
  where "\<^bold>A\<^sub>1 \<equiv> \<lambda>f x. f x"  (* (unary) function application (@); cf. reverse-pipe (<|) *)
definition A2_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c" ("\<^bold>A\<^sub>2")
  where "\<^bold>A\<^sub>2 \<equiv> \<lambda>f x\<^sub>1 x\<^sub>2. f x\<^sub>1 x\<^sub>2" (* function application (binary case) *)
definition A3_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd" ("\<^bold>A\<^sub>3")
  where "\<^bold>A\<^sub>3 \<equiv> \<lambda>f x\<^sub>1 x\<^sub>2 x\<^sub>3. f x\<^sub>1 x\<^sub>2 x\<^sub>3" (* function application (ternary case) *)
(*... and so on*)

notation A1_comb ("\<^bold>A") (* default notation for unary case *)

(*The identity combinator \<^bold>I (suitably typed) generalizes all \<^bold>A\<^sub>m combinators (via polymorphism and \<eta>-conversion).*)
lemma "\<^bold>A\<^sub>1 = \<^bold>I" unfolding A1_comb_def I_comb_def ..
lemma "\<^bold>A\<^sub>2 = \<^bold>I" unfolding A2_comb_def I_comb_def ..
lemma "\<^bold>A\<^sub>3 = \<^bold>I" unfolding A3_comb_def I_comb_def ..
(*...and so on*)

(*It is convenient to introduce a family \<^bold>T\<^sub>m of 'reversed appliers' as abbreviations*)
abbreviation T1_comb::"'b \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<^bold>T\<^sub>1")
  where "\<^bold>T\<^sub>1 x f \<equiv> \<^bold>A\<^sub>1 f x"  (*unary case*)
abbreviation T2_comb::"'b \<Rightarrow> 'c \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<^bold>T\<^sub>2")
  where "\<^bold>T\<^sub>2 x y f \<equiv> \<^bold>A\<^sub>2 f x y" (*binary case*)
abbreviation T3_comb ("\<^bold>T\<^sub>3")
  where "\<^bold>T\<^sub>3 x y z f \<equiv> \<^bold>A\<^sub>3 f x y z" (*ternary case*)
(*... and so on*)

(*special notation for unary and binary cases*)
notation T1_comb ("\<^bold>T") (* cf. 'Let', Smullyan's "thrush" *)
notation T2_comb ("\<^bold>V") (* cf. 'pairing' in \<lambda>-calculus, Smullyan's "vireo" *)

(*Convenient 'pipe' notation for the \<^bold>A\<^sub>1 and its reverse \<^bold>T\<^sub>1 in their role as function application.*)
notation(input) A1_comb (infixr "<|" 54)
notation(input) T1_comb (infixl "|>" 54)

declare  I_comb_def[comb_defs] A1_comb_def[comb_defs] A2_comb_def[comb_defs] A3_comb_def[comb_defs]

(*Notation checks*)
lemma "a |> f = f a" unfolding comb_defs ..
lemma "f <| a = f a" unfolding comb_defs ..
lemma "a |> f |> g = g (f a)" unfolding comb_defs ..
lemma "g <| f <| a = g (f a)" unfolding comb_defs ..
lemma "(a |> f) <| b = f a b" unfolding comb_defs ..


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
definition B03_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> ('d \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'c" ("\<^bold>B\<^sub>0\<^sub>3")
  where "\<^bold>B\<^sub>0\<^sub>3 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>2 y\<^sub>2 z\<^sub>2. f g\<^sub>1 (g\<^sub>2 x\<^sub>2 y\<^sub>2 z\<^sub>2)"
(*... and so on*)
definition B10_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'd \<Rightarrow> 'c" ("\<^bold>B\<^sub>1\<^sub>0")
  where "\<^bold>B\<^sub>1\<^sub>0 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>1. f (g\<^sub>1 x\<^sub>1) g\<^sub>2"
definition B11_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'a) \<Rightarrow> ('e \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'c" ("\<^bold>B\<^sub>1\<^sub>1")
  where "\<^bold>B\<^sub>1\<^sub>1 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>1 x\<^sub>2. f (g\<^sub>1 x\<^sub>1) (g\<^sub>2 x\<^sub>2)"
definition B12_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'a) \<Rightarrow> ('e \<Rightarrow> 'f \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'c" ("\<^bold>B\<^sub>1\<^sub>2")
  where "\<^bold>B\<^sub>1\<^sub>2 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>1 x\<^sub>2 y\<^sub>2. f (g\<^sub>1 x\<^sub>1) (g\<^sub>2 x\<^sub>2 y\<^sub>2)"
definition B13_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'a) \<Rightarrow> ('e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'c" ("\<^bold>B\<^sub>1\<^sub>3")
  where "\<^bold>B\<^sub>1\<^sub>3 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>1 x\<^sub>2 y\<^sub>2 z\<^sub>2. f (g\<^sub>1 x\<^sub>1) (g\<^sub>2 x\<^sub>2 y\<^sub>2 z\<^sub>2)"
(*... and so on*)
definition B20_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'e \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'c" ("\<^bold>B\<^sub>2\<^sub>0")
  where "\<^bold>B\<^sub>2\<^sub>0 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>1 y\<^sub>1. f (g\<^sub>1 x\<^sub>1 y\<^sub>1) g\<^sub>2"
definition B21_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'e \<Rightarrow> 'a) \<Rightarrow> ('f \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'f \<Rightarrow> 'e \<Rightarrow> 'c" ("\<^bold>B\<^sub>2\<^sub>1")
  where "\<^bold>B\<^sub>2\<^sub>1 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>1 x\<^sub>2 y\<^sub>1. f (g\<^sub>1 x\<^sub>1 y\<^sub>1) (g\<^sub>2 x\<^sub>2)"
definition B22_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'e \<Rightarrow> 'a) \<Rightarrow> ('f \<Rightarrow> 'g \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'f \<Rightarrow> 'e \<Rightarrow> 'g \<Rightarrow> 'c" ("\<^bold>B\<^sub>2\<^sub>2")
  where "\<^bold>B\<^sub>2\<^sub>2 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>1 x\<^sub>2 y\<^sub>1 y\<^sub>2. f (g\<^sub>1 x\<^sub>1 y\<^sub>1) (g\<^sub>2 x\<^sub>2 y\<^sub>2)"
(*... and so on*)
definition B30_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'c" ("\<^bold>B\<^sub>3\<^sub>0")
  where "\<^bold>B\<^sub>3\<^sub>0 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x\<^sub>1 y\<^sub>1 z\<^sub>1. f (g\<^sub>1 x\<^sub>1 y\<^sub>1 z\<^sub>1) g\<^sub>2"
(*... and so on*)
abbreviation(input) B000_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd"("\<^bold>B\<^sub>0\<^sub>0\<^sub>0")  
  where "\<^bold>B\<^sub>0\<^sub>0\<^sub>0 \<equiv> \<^bold>A\<^sub>3"  (* composing with three nullary functions corresponds to ternary function application*)
(*... and so on*)
definition B111_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('e \<Rightarrow> 'a) \<Rightarrow> ('f \<Rightarrow> 'b) \<Rightarrow> ('g \<Rightarrow> 'c) 
                                                                    \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'd" ("\<^bold>B\<^sub>1\<^sub>1\<^sub>1")
  where "\<^bold>B\<^sub>1\<^sub>1\<^sub>1 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 g\<^sub>3 x\<^sub>1 x\<^sub>2 x\<^sub>3. f (g\<^sub>1 x\<^sub>1) (g\<^sub>2 x\<^sub>2) (g\<^sub>3 x\<^sub>3)"
definition B112_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('e \<Rightarrow> 'a) \<Rightarrow> ('f \<Rightarrow> 'b) \<Rightarrow> ('g \<Rightarrow> 'h \<Rightarrow> 'c) 
                                                              \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'h \<Rightarrow> 'd"  ("\<^bold>B\<^sub>1\<^sub>1\<^sub>2")
  where "\<^bold>B\<^sub>1\<^sub>1\<^sub>2 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 g\<^sub>3 x\<^sub>1 x\<^sub>2 x\<^sub>3 y\<^sub>3. f (g\<^sub>1 x\<^sub>1) (g\<^sub>2 x\<^sub>2) (g\<^sub>3 x\<^sub>3 y\<^sub>3)"
(*... and so on*)
definition B222_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('e \<Rightarrow> 'f \<Rightarrow> 'a) \<Rightarrow> ('g \<Rightarrow> 'h \<Rightarrow> 'b) 
                                \<Rightarrow> ('i \<Rightarrow> 'j \<Rightarrow> 'c) \<Rightarrow> 'e \<Rightarrow> 'g \<Rightarrow> 'i \<Rightarrow> 'f \<Rightarrow> 'h \<Rightarrow> 'j \<Rightarrow> 'd" ("\<^bold>B\<^sub>2\<^sub>2\<^sub>2")
  where "\<^bold>B\<^sub>2\<^sub>2\<^sub>2 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 g\<^sub>3 x\<^sub>1 x\<^sub>2 x\<^sub>3 y\<^sub>1 y\<^sub>2 y\<^sub>3. f (g\<^sub>1 x\<^sub>1 y\<^sub>1) (g\<^sub>2 x\<^sub>2 y\<^sub>2) (g\<^sub>3 x\<^sub>3 y\<^sub>3)"
definition B223_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('e \<Rightarrow> 'f \<Rightarrow> 'a) \<Rightarrow> ('g \<Rightarrow> 'h \<Rightarrow> 'b) 
                    \<Rightarrow> ('i \<Rightarrow> 'j \<Rightarrow> 'k \<Rightarrow> 'c) \<Rightarrow> 'e \<Rightarrow> 'g \<Rightarrow> 'i \<Rightarrow> 'f \<Rightarrow> 'h \<Rightarrow> 'j \<Rightarrow> 'k \<Rightarrow> 'd"  ("\<^bold>B\<^sub>2\<^sub>2\<^sub>3")
  where "\<^bold>B\<^sub>2\<^sub>2\<^sub>3 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 g\<^sub>3 x\<^sub>1 x\<^sub>2 x\<^sub>3 y\<^sub>1 y\<^sub>2 y\<^sub>3 z\<^sub>3. f (g\<^sub>1 x\<^sub>1 y\<^sub>1) (g\<^sub>2 x\<^sub>2 y\<^sub>2) (g\<^sub>3 x\<^sub>3 y\<^sub>3 z\<^sub>3)"
(*... and so on*)
definition B333_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'a) \<Rightarrow> ('h \<Rightarrow> 'i \<Rightarrow> 'j \<Rightarrow> 'b) 
         \<Rightarrow> ('k \<Rightarrow> 'l \<Rightarrow> 'm \<Rightarrow> 'c) \<Rightarrow> 'e \<Rightarrow> 'h \<Rightarrow> 'k \<Rightarrow> 'f \<Rightarrow> 'i \<Rightarrow> 'l \<Rightarrow> 'g \<Rightarrow> 'j \<Rightarrow> 'm \<Rightarrow> 'd" ("\<^bold>B\<^sub>3\<^sub>3\<^sub>3")
  where "\<^bold>B\<^sub>3\<^sub>3\<^sub>3 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 g\<^sub>3 x\<^sub>1 x\<^sub>2 x\<^sub>3 y\<^sub>1 y\<^sub>2 y\<^sub>3 z\<^sub>1 z\<^sub>2 z\<^sub>3. f (g\<^sub>1 x\<^sub>1 y\<^sub>1 z\<^sub>1) (g\<^sub>2 x\<^sub>2 y\<^sub>2 z\<^sub>2) (g\<^sub>3 x\<^sub>3 y\<^sub>3 z\<^sub>3)"
  (*... and so on*)
definition B1111_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> ('f \<Rightarrow> 'a) \<Rightarrow> ('g \<Rightarrow> 'b) \<Rightarrow> ('h \<Rightarrow> 'c) \<Rightarrow> ('i \<Rightarrow> 'd)
                                                       \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'h \<Rightarrow> 'i \<Rightarrow> 'e" ("\<^bold>B\<^sub>1\<^sub>1\<^sub>1\<^sub>1")
  where "\<^bold>B\<^sub>1\<^sub>1\<^sub>1\<^sub>1 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 g\<^sub>3 g\<^sub>4 x\<^sub>1 x\<^sub>2 x\<^sub>3 x\<^sub>4. f (g\<^sub>1 x\<^sub>1) (g\<^sub>2 x\<^sub>2) (g\<^sub>3 x\<^sub>3) (g\<^sub>4 x\<^sub>4)"
  (*... and so on*)

(*We introduce a convenient infix notation for the \<^bold>B\<^sub>n family of combinators (and their transposes) in
 their role as arity-extended versions of composition, and write "\<^bold>B\<^sub>n f g" as "f \<circ>\<^sub>n g"*)
notation B1_comb (infixl "\<circ>\<^sub>1" 55)
notation B2_comb (infixl "\<circ>\<^sub>2" 55)
notation B3_comb (infixl "\<circ>\<^sub>3" 55)
notation B4_comb (infixl "\<circ>\<^sub>4" 55)
abbreviation(input) B1_comb_t (infixr ";\<^sub>1" 55)
  where "f ;\<^sub>1 g \<equiv> g \<circ>\<^sub>1 f"
abbreviation(input) B2_comb_t (infixr ";\<^sub>2" 55)
  where "f ;\<^sub>2 g \<equiv> g \<circ>\<^sub>2 f"
abbreviation(input) B3_comb_t (infixr ";\<^sub>3" 55)
  where "f ;\<^sub>3 g \<equiv> g \<circ>\<^sub>3 f"
abbreviation(input) B4_comb_t (infixr ";\<^sub>4" 55)
  where "f ;\<^sub>4 g \<equiv> g \<circ>\<^sub>4 f"

(*Convenient 'default' notation*)
notation B1_comb ("\<^bold>B") 
notation B1_comb (infixl "\<circ>" 55)
abbreviation(input) B1_comb_t' (infixr ";" 55)
  where "f ; g \<equiv> g \<circ> f"

(* Alternative notations for some known compositors in the literature *)
notation B01_comb ("\<^bold>D") (* aliasing \<^bold>B\<^sub>0\<^sub>1 as \<^bold>D (cf. Smullyan's "dove" combinator)*)
notation B02_comb ("\<^bold>E") (* aliasing \<^bold>B\<^sub>0\<^sub>2 as \<^bold>E (cf. Smullyan's "eagle" combinator)*)
(*TODO: find others*)


declare B1_comb_def[comb_defs] B2_comb_def[comb_defs] B3_comb_def[comb_defs] B4_comb_def[comb_defs]        
        B01_comb_def[comb_defs] B02_comb_def[comb_defs] B03_comb_def[comb_defs]
        B10_comb_def[comb_defs] B11_comb_def[comb_defs] B12_comb_def[comb_defs] B13_comb_def[comb_defs] 
        B20_comb_def[comb_defs] B21_comb_def[comb_defs] B22_comb_def[comb_defs] B30_comb_def[comb_defs]
        B111_comb_def[comb_defs] B112_comb_def[comb_defs] 
        B222_comb_def[comb_defs] B223_comb_def[comb_defs] B333_comb_def[comb_defs] B1111_comb_def[comb_defs]

(*Notation checks*)
lemma "f \<circ> g \<circ> h = h ; g ; f" unfolding comb_defs ..
lemma "f \<circ>\<^sub>2 g = g ;\<^sub>2 f" unfolding comb_defs ..
lemma "a |> f |> g = a |> f ; g" unfolding comb_defs ..
lemma "a |> f |> g = g \<circ> f <| a" unfolding comb_defs ..
lemma "a |> f |> g = f ; g <| a" unfolding comb_defs ..

(*Composing compositors*) 
(*In the following cases, we have that  \<^bold>B\<^sub>a\<^sub>b \<circ> \<^bold>B\<^sub>c\<^sub>d = \<^bold>B\<^sub>(\<^sub>a\<^sub>+\<^sub>b\<^sub>)\<^sub>(\<^sub>c\<^sub>+\<^sub>d\<^sub>)*)  (*TODO: find general rule *)
lemma "\<^bold>B\<^sub>1\<^sub>1 \<circ> \<^bold>B\<^sub>0\<^sub>0 = \<^bold>B\<^sub>1\<^sub>1" unfolding comb_defs ..
lemma "\<^bold>B\<^sub>1\<^sub>0 \<circ> \<^bold>B\<^sub>0\<^sub>1 = \<^bold>B\<^sub>1\<^sub>1" unfolding comb_defs ..
lemma "\<^bold>B\<^sub>1\<^sub>2 \<circ> \<^bold>B\<^sub>0\<^sub>0 = \<^bold>B\<^sub>1\<^sub>2" unfolding comb_defs ..
lemma "\<^bold>B\<^sub>1\<^sub>1 \<circ> \<^bold>B\<^sub>0\<^sub>1 = \<^bold>B\<^sub>1\<^sub>2" unfolding comb_defs ..
lemma "\<^bold>B\<^sub>1\<^sub>0 \<circ> \<^bold>B\<^sub>1\<^sub>0 = \<^bold>B\<^sub>2\<^sub>0" unfolding comb_defs ..
lemma "\<^bold>B\<^sub>1\<^sub>1 \<circ> \<^bold>B\<^sub>1\<^sub>0 = \<^bold>B\<^sub>2\<^sub>1" unfolding comb_defs ..
lemma "\<^bold>B\<^sub>1\<^sub>1 \<circ> \<^bold>B\<^sub>1\<^sub>1 = \<^bold>B\<^sub>2\<^sub>2" unfolding comb_defs ..
(*...and so on *)

(*Similarly, below we have that \<^bold>B\<^sub>a\<^sub>b\<^sub>c \<circ> \<^bold>B\<^sub>d\<^sub>e\<^sub>f = \<^bold>B\<^sub>(\<^sub>a\<^sub>+\<^sub>d\<^sub>)\<^sub>(\<^sub>b\<^sub>+\<^sub>e\<^sub>)\<^sub>(\<^sub>c\<^sub>+\<^sub>f\<^sub>) *) (*TODO: find general rule *)
lemma "\<^bold>B\<^sub>0\<^sub>0\<^sub>0 \<circ> \<^bold>B\<^sub>1\<^sub>1\<^sub>1 = \<^bold>B\<^sub>1\<^sub>1\<^sub>1" unfolding comb_defs ..
lemma "\<^bold>B\<^sub>1\<^sub>1\<^sub>1 \<circ> \<^bold>B\<^sub>1\<^sub>1\<^sub>1 = \<^bold>B\<^sub>2\<^sub>2\<^sub>2" unfolding comb_defs ..
lemma "\<^bold>B\<^sub>1\<^sub>1\<^sub>1 \<circ> \<^bold>B\<^sub>1\<^sub>1\<^sub>2 = \<^bold>B\<^sub>2\<^sub>2\<^sub>3" unfolding comb_defs ..
lemma "\<^bold>B\<^sub>1\<^sub>1\<^sub>1 \<circ> \<^bold>B\<^sub>2\<^sub>2\<^sub>2 = \<^bold>B\<^sub>3\<^sub>3\<^sub>3" unfolding comb_defs ..
lemma "\<^bold>B\<^sub>2\<^sub>2\<^sub>2 \<circ> \<^bold>B\<^sub>1\<^sub>1\<^sub>1 = \<^bold>B\<^sub>3\<^sub>3\<^sub>3" unfolding comb_defs ..
(*...and so on *)

(*Note, however, that*)     (*TODO: find exceptions rule *)
lemma "\<^bold>B\<^sub>0\<^sub>1 \<circ> \<^bold>B\<^sub>1\<^sub>0 = \<^bold>B\<^sub>1\<^sub>1" nitpick oops (*countermodel *)
lemma "\<^bold>B\<^sub>0\<^sub>1 \<circ> \<^bold>B\<^sub>1\<^sub>1 = \<^bold>B\<^sub>1\<^sub>2"  nitpick oops (*countermodel *)
lemma "\<^bold>B\<^sub>1\<^sub>1\<^sub>2 \<circ> \<^bold>B\<^sub>1\<^sub>1\<^sub>1 = \<^bold>B\<^sub>2\<^sub>2\<^sub>3" nitpick oops (*countermodel *)


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
definition C1243_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'd \<Rightarrow> 'c \<Rightarrow> 'e" ("\<^bold>C\<^sub>1\<^sub>2\<^sub>4\<^sub>3")
  where "\<^bold>C\<^sub>1\<^sub>2\<^sub>4\<^sub>3 \<equiv> \<lambda>f x\<^sub>1 x\<^sub>2 x\<^sub>3 x\<^sub>4. f x\<^sub>1 x\<^sub>2 x\<^sub>4 x\<^sub>3"
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

(*Introduce some convenient combinator notations*)
notation C21_comb ("\<^bold>C") (*the traditional flip/transposition (\<^bold>C) combinator is \<^bold>C\<^sub>2\<^sub>1*)
notation C3412_comb ("\<^bold>C\<^sub>2") (*pairwise flip/transposition of the arguments of a quaternary function*)
notation C231_comb ("\<^bold>R") (*Right (counterclockwise) rotation of a ternary function*)
notation C312_comb ("\<^bold>L") (*Left (counterclockwise) rotation of a ternary function*)
notation C321_comb ("\<^bold>C''") (*Full reversal of the arguments of a ternary function*)

declare C21_comb_def[comb_defs] 
      C132_comb_def[comb_defs]  C231_comb_def[comb_defs] C312_comb_def[comb_defs]  C321_comb_def[comb_defs] 
      C1243_comb_def[comb_defs] C1324_comb_def[comb_defs] C1423_comb_def[comb_defs] 
      C2143_comb_def[comb_defs] C2314_comb_def[comb_defs] C3142_comb_def[comb_defs] C3412_comb_def[comb_defs]

(*Composing rotation combinators (identity, left & right) works as expected*)
lemma "\<^bold>R \<circ> \<^bold>L = \<^bold>L \<circ> \<^bold>R" unfolding comb_defs ..
lemma "\<^bold>R = \<^bold>L \<circ> \<^bold>L" unfolding comb_defs ..
lemma "\<^bold>L = \<^bold>R \<circ> \<^bold>R" unfolding comb_defs ..
lemma "\<^bold>I = \<^bold>L \<circ> \<^bold>L \<circ> \<^bold>L" unfolding comb_defs ..
lemma "\<^bold>I = \<^bold>R \<circ> \<^bold>R \<circ> \<^bold>R" unfolding comb_defs ..


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
        W32_comb_def[comb_defs] W33_comb_def[comb_defs]


subsection \<open>Fusers\<close> (*TODO: name comes from Schönfinkel's "Verschmelzung". Find a better name? *)

(*The families \<^bold>S\<^sub>m\<^sub>n (resp. \<^bold>\<Sigma>\<^sub>m\<^sub>n) generalize the combinator \<^bold>S (resp. its evil twin \<^bold>\<Sigma>) towards higher arities.*)
definition S11_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c" ("\<^bold>S\<^sub>1\<^sub>1")
  where "\<^bold>S\<^sub>1\<^sub>1 \<equiv> \<lambda>f g x. f x (g x)" (* aka. \<^bold>S (same as \<^bold>B\<^bold>\<Sigma>\<^bold>C) *)
definition S12_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'd" ("\<^bold>S\<^sub>1\<^sub>2")
  where "\<^bold>S\<^sub>1\<^sub>2 \<equiv> \<lambda>f g x y. f x y (g x y)"
definition S13_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'e" ("\<^bold>S\<^sub>1\<^sub>3")
  where "\<^bold>S\<^sub>1\<^sub>3 \<equiv> \<lambda>f g x y z. f x y z (g x y z)"
(*... and so on*)
definition S21_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'd" ("\<^bold>S\<^sub>2\<^sub>1")
  where "\<^bold>S\<^sub>2\<^sub>1 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x. f x (g\<^sub>1 x) (g\<^sub>2 x)"
definition S22_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) 
                                                     \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'e" ("\<^bold>S\<^sub>2\<^sub>2")
  where "\<^bold>S\<^sub>2\<^sub>2 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x y. f x y (g\<^sub>1 x y) (g\<^sub>2 x y)"
definition S23_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd)
                        \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'e) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'f) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'g" ("\<^bold>S\<^sub>2\<^sub>3")
  where "\<^bold>S\<^sub>2\<^sub>3 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 g\<^sub>3 x y z. f x y z (g\<^sub>1 x y z) (g\<^sub>2 x y z) (g\<^sub>3 x y z)"
(*... and so on*)
definition \<Sigma>11_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'c" ("\<^bold>\<Sigma>\<^sub>1\<^sub>1")
  where "\<^bold>\<Sigma>\<^sub>1\<^sub>1 \<equiv> \<lambda>f g x. f (g x) x "  (* aka. \<^bold>\<Sigma> (same as \<^bold>B\<^bold>S\<^bold>C) *)
definition \<Sigma>12_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd" ("\<^bold>\<Sigma>\<^sub>1\<^sub>2")
  where "\<^bold>\<Sigma>\<^sub>1\<^sub>2 \<equiv> \<lambda>f g x y. f (g x y) x y"  (* same as \<^bold>B\<^bold>S\<^sub>1\<^sub>2\<^bold>L*)
definition \<Sigma>13_comb  :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e" ("\<^bold>\<Sigma>\<^sub>1\<^sub>3")
  where "\<^bold>\<Sigma>\<^sub>1\<^sub>3 \<equiv> \<lambda>f g x y z. f (g x y z) x y z"
(*... and so on*)
definition \<Sigma>21_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'd" ("\<^bold>\<Sigma>\<^sub>2\<^sub>1")
  where "\<^bold>\<Sigma>\<^sub>2\<^sub>1 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x. f (g\<^sub>1 x) (g\<^sub>2 x) x"
definition \<Sigma>22_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> 'a) 
                                                     \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e" ("\<^bold>\<Sigma>\<^sub>2\<^sub>2")
  where "\<^bold>\<Sigma>\<^sub>2\<^sub>2 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x y. f (g\<^sub>1 x y) (g\<^sub>2 x y) x y"
definition \<Sigma>23_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g) \<Rightarrow> ('d \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'a) 
                          \<Rightarrow> ('d \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'b) \<Rightarrow> ('d \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'c) \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g" ("\<^bold>\<Sigma>\<^sub>2\<^sub>3")
  where "\<^bold>\<Sigma>\<^sub>2\<^sub>3 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 g\<^sub>3 x y z. f (g\<^sub>1 x y z) (g\<^sub>2 x y z) (g\<^sub>3 x y z) x y z"

notation S11_comb ("\<^bold>S")
notation \<Sigma>11_comb ("\<^bold>\<Sigma>")

declare S11_comb_def[comb_defs] S12_comb_def[comb_defs] S13_comb_def[comb_defs]
        S21_comb_def[comb_defs] S22_comb_def[comb_defs] S23_comb_def[comb_defs]
        \<Sigma>11_comb_def[comb_defs] \<Sigma>12_comb_def[comb_defs] \<Sigma>13_comb_def[comb_defs]


(*\<^bold>S/\<^bold>\<Sigma> can be defined in terms of other combinators*)
lemma "\<^bold>S = \<^bold>B (\<^bold>B (\<^bold>B \<^bold>W) \<^bold>C) (\<^bold>B \<^bold>B)" unfolding comb_defs ..
lemma "\<^bold>S = \<^bold>B (\<^bold>B \<^bold>W)(\<^bold>B \<^bold>B \<^bold>C)" unfolding comb_defs ..
lemma "\<^bold>\<Sigma> = \<^bold>B (\<^bold>B \<^bold>W) \<^bold>B" unfolding comb_defs .. 
(*and interdefined*)
lemma "\<^bold>S = \<^bold>B \<^bold>\<Sigma> \<^bold>C" unfolding comb_defs ..
lemma "\<^bold>\<Sigma> = \<^bold>B \<^bold>S \<^bold>C" unfolding comb_defs ..
lemma "\<^bold>S = \<^bold>B (\<^bold>T \<^bold>C) \<^bold>B \<^bold>\<Sigma>" unfolding comb_defs ..
lemma "\<^bold>\<Sigma> = \<^bold>B (\<^bold>T \<^bold>C) \<^bold>B \<^bold>S" unfolding comb_defs ..
lemma "\<^bold>\<Sigma>\<^sub>1\<^sub>2 = \<^bold>B \<^bold>S\<^sub>1\<^sub>2 \<^bold>L" unfolding comb_defs ..


subsection \<open>Further convenient combinators\<close>

subsubsection \<open>Preprocessors\<close>
(*The family of \<^bold>\<Psi>\<^sub>m combinators below are special cases of compositors. They take an m-ary function 
 'f' and prepend to each of its m inputs  a given unary function 'g' (acting as a "preprocessor"). *)

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
 and appear often in the literature, e.g., as "trains" in array languages like APL and BQN, and in 
 "imitation bindings" in higher-order (pre-)unification algorithms (from where they get their name).*)

(*Conveniently introduce a (degenerate) case m = 0 as abbreviation, where \<^bold>\<Phi>\<^sub>0\<^sub>n corresponds to \<^bold>K\<^sub>(\<^sub>n\<^sub>+\<^sub>1\<^sub>)\<^sub>1 *)
abbreviation(input) \<Phi>01_comb :: "'a \<Rightarrow> 'b \<Rightarrow> 'a" ("\<^bold>\<Phi>\<^sub>0\<^sub>1")  
  where "\<^bold>\<Phi>\<^sub>0\<^sub>1 \<equiv> \<^bold>K\<^sub>2\<^sub>1"
abbreviation(input) \<Phi>02_comb :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'a" ("\<^bold>\<Phi>\<^sub>0\<^sub>2")  
  where "\<^bold>\<Phi>\<^sub>0\<^sub>2 \<equiv> \<^bold>K\<^sub>3\<^sub>1"
(*...and so on *)

(* Each combinator \<^bold>\<Phi>\<^sub>1\<^sub>n corresponds in fact to \<^bold>B\<^sub>n *)
abbreviation(input) \<Phi>11_comb :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'b" ("\<^bold>\<Phi>\<^sub>1\<^sub>1")  
  where "\<^bold>\<Phi>\<^sub>1\<^sub>1 \<equiv> \<^bold>B\<^sub>1"        
abbreviation(input) \<Phi>12_comb :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'b" ("\<^bold>\<Phi>\<^sub>1\<^sub>2")  
  where "\<^bold>\<Phi>\<^sub>1\<^sub>2 \<equiv> \<^bold>B\<^sub>2"            
abbreviation(input) \<Phi>13_comb :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'b" ("\<^bold>\<Phi>\<^sub>1\<^sub>3")  
  where "\<^bold>\<Phi>\<^sub>1\<^sub>3 \<equiv> \<^bold>B\<^sub>3"            
abbreviation(input) \<Phi>14_comb :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'b"  ("\<^bold>\<Phi>\<^sub>1\<^sub>4")  
  where "\<^bold>\<Phi>\<^sub>1\<^sub>4 \<equiv> \<^bold>B\<^sub>4" 
(*...and so on *)

(* Combinators \<^bold>\<Phi>\<^sub>m\<^sub>n with m > 1 have their idiosyncratic definition *)
definition \<Phi>21_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'a) \<Rightarrow> ('d \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'c" ("\<^bold>\<Phi>\<^sub>2\<^sub>1")
  where "\<^bold>\<Phi>\<^sub>2\<^sub>1 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x. f (g\<^sub>1 x) (g\<^sub>2 x)" (*cf. "\<Phi>\<^sub>1" in Curry 1931; "liftA2" in Haskell; "monadic fork" in APL)*)
definition \<Phi>22_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'e \<Rightarrow> 'a) \<Rightarrow> ('d \<Rightarrow> 'e \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'c" ("\<^bold>\<Phi>\<^sub>2\<^sub>2")
  where "\<^bold>\<Phi>\<^sub>2\<^sub>2 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 x y. f (g\<^sub>1 x y) (g\<^sub>2 x y)" (*cf. "\<Phi>\<^sub>2" in Curry 1931; "dyadic fork" in APL *)
(*...and so on *)
definition \<Phi>31_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('e \<Rightarrow> 'a) \<Rightarrow> ('e \<Rightarrow> 'b) \<Rightarrow> ('e \<Rightarrow> 'c) \<Rightarrow> 'e \<Rightarrow> 'd" ("\<^bold>\<Phi>\<^sub>3\<^sub>1")
  where "\<^bold>\<Phi>\<^sub>3\<^sub>1 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 g\<^sub>3 x. f (g\<^sub>1 x) (g\<^sub>2 x) (g\<^sub>3 x)"
definition \<Phi>32_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('e \<Rightarrow> 'f \<Rightarrow> 'a) \<Rightarrow> ('e \<Rightarrow> 'f \<Rightarrow> 'b) 
                                                      \<Rightarrow> ('e \<Rightarrow> 'f \<Rightarrow> 'c) \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'd" ("\<^bold>\<Phi>\<^sub>3\<^sub>2")
  where "\<^bold>\<Phi>\<^sub>3\<^sub>2 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 g\<^sub>3 x y. f (g\<^sub>1 x y) (g\<^sub>2 x y) (g\<^sub>3 x y)"
definition \<Phi>33_comb :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'a) \<Rightarrow> ('e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'b)
                                         \<Rightarrow> ('e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'c) \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'd"  ("\<^bold>\<Phi>\<^sub>3\<^sub>3")
  where "\<^bold>\<Phi>\<^sub>3\<^sub>3 \<equiv> \<lambda>f g\<^sub>1 g\<^sub>2 g\<^sub>3 x y z. f (g\<^sub>1 x y z) (g\<^sub>2 x y z) (g\<^sub>3 x y z)"
(*...and so on *)

declare \<Phi>21_comb_def[comb_defs] \<Phi>22_comb_def[comb_defs] 
        \<Phi>31_comb_def[comb_defs] \<Phi>32_comb_def[comb_defs] \<Phi>33_comb_def[comb_defs]

(*\<^bold>\<Phi>\<^sub>m\<^sub>(\<^sub>i\<^sub>+\<^sub>j\<^sub>) can be defined as: \<^bold>\<Phi>\<^sub>m\<^sub>i \<circ> \<^bold>\<Phi>\<^sub>m\<^sub>j*)
lemma "\<^bold>\<Phi>\<^sub>1\<^sub>2 = \<^bold>\<Phi>\<^sub>1\<^sub>1 \<circ> \<^bold>\<Phi>\<^sub>1\<^sub>1" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>1\<^sub>3 = \<^bold>\<Phi>\<^sub>1\<^sub>1 \<circ> \<^bold>\<Phi>\<^sub>1\<^sub>2" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>1\<^sub>3 = \<^bold>\<Phi>\<^sub>1\<^sub>2 \<circ> \<^bold>\<Phi>\<^sub>1\<^sub>1" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>2\<^sub>2 = \<^bold>\<Phi>\<^sub>2\<^sub>1 \<circ> \<^bold>\<Phi>\<^sub>2\<^sub>1" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>3\<^sub>2 = \<^bold>\<Phi>\<^sub>3\<^sub>1 \<circ> \<^bold>\<Phi>\<^sub>3\<^sub>1" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>3\<^sub>3 = \<^bold>\<Phi>\<^sub>3\<^sub>1 \<circ> \<^bold>\<Phi>\<^sub>3\<^sub>2" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>3\<^sub>3 = \<^bold>\<Phi>\<^sub>3\<^sub>2 \<circ> \<^bold>\<Phi>\<^sub>3\<^sub>1" unfolding comb_defs ..
(*...and so on *)

(*Moreover, \<^bold>\<Phi>\<^sub>m\<^sub>n is definable by composing \<^bold>W\<^sub>m\<^sub>n and \<^bold>B\<^sub>N, via the following schema: \<^bold>\<Phi>\<^sub>m\<^sub>n = \<^bold>W\<^sub>m\<^sub>n \<circ>\<^sub>m\<^sub>+\<^sub>1 \<^bold>B\<^sub>N 
 (where N is an m-sized array of ns)*)
lemma "\<^bold>\<Phi>\<^sub>1\<^sub>1 = \<^bold>W\<^sub>1\<^sub>1 \<circ>\<^sub>2 \<^bold>B\<^sub>1" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>1\<^sub>2 = \<^bold>W\<^sub>1\<^sub>2 \<circ>\<^sub>2 \<^bold>B\<^sub>2" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>1\<^sub>3 = \<^bold>W\<^sub>1\<^sub>3 \<circ>\<^sub>2 \<^bold>B\<^sub>3" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>2\<^sub>1 = \<^bold>W\<^sub>2\<^sub>1 \<circ>\<^sub>3 \<^bold>B\<^sub>1\<^sub>1" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>2\<^sub>2 = \<^bold>W\<^sub>2\<^sub>2 \<circ>\<^sub>3 \<^bold>B\<^sub>2\<^sub>2" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>3\<^sub>1 = \<^bold>W\<^sub>3\<^sub>1 \<circ>\<^sub>4 \<^bold>B\<^sub>1\<^sub>1\<^sub>1" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>3\<^sub>2 = \<^bold>W\<^sub>3\<^sub>2 \<circ>\<^sub>4 \<^bold>B\<^sub>2\<^sub>2\<^sub>2" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>3\<^sub>3 = \<^bold>W\<^sub>3\<^sub>3 \<circ>\<^sub>4 \<^bold>B\<^sub>3\<^sub>3\<^sub>3" unfolding comb_defs ..
(*...and so on *)


subsubsection \<open>Projectors\<close>
(* The family of projectors \<^bold>\<Pi>\<^sub>l\<^sub>m\<^sub>n features three parameters: l = total number of arguments;
 m (\<le> l) = the index of the projection (\<le> l); n = the arity of the (projected) m-th argument.
 They are used to construct "projection bindings" in higher-order (pre-)unification algorithms. *)

abbreviation(input) \<Pi>110_comb :: "'a \<Rightarrow> 'a" ("\<^bold>\<Pi>\<^sub>1\<^sub>1\<^sub>0")  
  where "\<^bold>\<Pi>\<^sub>1\<^sub>1\<^sub>0 \<equiv> \<^bold>I"       (*trivial case corresponds to the identity combinator \<^bold>I *) 
definition \<Pi>111_comb :: "(('a \<Rightarrow> 'b) \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b" ("\<^bold>\<Pi>\<^sub>1\<^sub>1\<^sub>1") (* Smullyan's "owl" *)
  where "\<^bold>\<Pi>\<^sub>1\<^sub>1\<^sub>1 \<equiv> \<lambda>h x. x (h x)"
definition \<Pi>112_comb :: "(('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a) \<Rightarrow> (('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'c" ("\<^bold>\<Pi>\<^sub>1\<^sub>1\<^sub>2")
  where "\<^bold>\<Pi>\<^sub>1\<^sub>1\<^sub>2 \<equiv> \<lambda>h\<^sub>1 h\<^sub>2 x. x (h\<^sub>1 x) (h\<^sub>2 x)"
definition \<Pi>113_comb :: "(('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a) \<Rightarrow> (('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'b) 
     \<Rightarrow> (('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'd" ("\<^bold>\<Pi>\<^sub>1\<^sub>1\<^sub>3")
  where "\<^bold>\<Pi>\<^sub>1\<^sub>1\<^sub>3 \<equiv> \<lambda>h\<^sub>1 h\<^sub>2 h\<^sub>3 x. x (h\<^sub>1 x) (h\<^sub>2 x) (h\<^sub>3 x)"
(*...and so on *)
abbreviation(input) \<Pi>210_comb :: "'a \<Rightarrow> 'b \<Rightarrow> 'a" ("\<^bold>\<Pi>\<^sub>2\<^sub>1\<^sub>0")  
  where "\<^bold>\<Pi>\<^sub>2\<^sub>1\<^sub>0 \<equiv> \<^bold>K\<^sub>2\<^sub>1"       (*trivial case corresponds to the combinator \<^bold>K\<^sub>2\<^sub>1 (i.e. \<^bold>K) *) 
definition \<Pi>211_comb :: "(('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'b"  ("\<^bold>\<Pi>\<^sub>2\<^sub>1\<^sub>1")
  where "\<^bold>\<Pi>\<^sub>2\<^sub>1\<^sub>1 \<equiv> \<lambda>h x y. x (h x y)"
definition \<Pi>212_comb :: "(('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'd \<Rightarrow> 'a) 
      \<Rightarrow> (('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'd \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'd \<Rightarrow> 'c" ("\<^bold>\<Pi>\<^sub>2\<^sub>1\<^sub>2")
  where "\<^bold>\<Pi>\<^sub>2\<^sub>1\<^sub>2 \<equiv> \<lambda>h\<^sub>1 h\<^sub>2 x y. x (h\<^sub>1 x y) (h\<^sub>2 x y)"
(*...and so on *)
abbreviation(input) \<Pi>220_comb :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"("\<^bold>\<Pi>\<^sub>2\<^sub>2\<^sub>0")  
  where "\<^bold>\<Pi>\<^sub>2\<^sub>2\<^sub>0 \<equiv> \<^bold>K\<^sub>2\<^sub>2"       (*trivial case corresponds to the combinator \<^bold>K\<^sub>2\<^sub>2 *) 
definition \<Pi>221_comb :: "('a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'c"  ("\<^bold>\<Pi>\<^sub>2\<^sub>2\<^sub>1")
  where "\<^bold>\<Pi>\<^sub>2\<^sub>2\<^sub>1 \<equiv> \<lambda>h x y. y (h x y)"
definition \<Pi>222_comb :: "('a \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'b) 
      \<Rightarrow> ('a \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'd" ("\<^bold>\<Pi>\<^sub>2\<^sub>2\<^sub>2")
  where "\<^bold>\<Pi>\<^sub>2\<^sub>2\<^sub>2 \<equiv> \<lambda>h\<^sub>1 h\<^sub>2 x y. y (h\<^sub>1 x y) (h\<^sub>2 x y)"
(*...and so on *)

declare \<Pi>111_comb_def[comb_defs] \<Pi>112_comb_def[comb_defs] \<Pi>113_comb_def[comb_defs]
        \<Pi>211_comb_def[comb_defs] \<Pi>212_comb_def[comb_defs] 
        \<Pi>221_comb_def[comb_defs] \<Pi>222_comb_def[comb_defs] 

notation \<Pi>111_comb ("\<^bold>O") (* aliasing \<^bold>\<Pi>\<^sub>1\<^sub>1\<^sub>1 as \<^bold>O (cf. Smullyan's "owl" combinator) *)

(*Projectors \<^bold>\<Pi>\<^sub>l\<^sub>m\<^sub>n can be defined as: \<^bold>S\<^sub>n\<^sub>l \<^bold>K\<^sub>l\<^sub>m *)
lemma "\<^bold>\<Pi>\<^sub>1\<^sub>1\<^sub>1 = \<^bold>S\<^sub>1\<^sub>1 \<^bold>K\<^sub>1\<^sub>1" unfolding comb_defs ..
lemma "\<^bold>\<Pi>\<^sub>1\<^sub>1\<^sub>2 = \<^bold>S\<^sub>2\<^sub>1 \<^bold>K\<^sub>1\<^sub>1" unfolding comb_defs ..
lemma "\<^bold>\<Pi>\<^sub>2\<^sub>1\<^sub>1 = \<^bold>S\<^sub>1\<^sub>2 \<^bold>K\<^sub>2\<^sub>1" unfolding comb_defs ..
lemma "\<^bold>\<Pi>\<^sub>2\<^sub>1\<^sub>2 = \<^bold>S\<^sub>2\<^sub>2 \<^bold>K\<^sub>2\<^sub>1" unfolding comb_defs ..
lemma "\<^bold>\<Pi>\<^sub>2\<^sub>2\<^sub>1 = \<^bold>S\<^sub>1\<^sub>2 \<^bold>K\<^sub>2\<^sub>2" unfolding comb_defs ..
lemma "\<^bold>\<Pi>\<^sub>2\<^sub>2\<^sub>2 = \<^bold>S\<^sub>2\<^sub>2 \<^bold>K\<^sub>2\<^sub>2" unfolding comb_defs ..
(*...and so on *)


subsection \<open>Combinator interrelations\<close>

(*We can show (via \<lambda>-conversion) that the combinators S and K can be used to define all others*)
lemma "\<^bold>B = \<^bold>S (\<^bold>K \<^bold>S) \<^bold>K" unfolding comb_defs ..
lemma "\<^bold>C = \<^bold>S (\<^bold>S (\<^bold>K (\<^bold>S (\<^bold>K \<^bold>S) \<^bold>K)) \<^bold>S) (\<^bold>K \<^bold>K)" unfolding comb_defs ..
lemma "\<^bold>C = \<^bold>S (\<^bold>B \<^bold>B \<^bold>S) (\<^bold>K \<^bold>K)" unfolding comb_defs ..
lemma "\<^bold>I = \<^bold>S \<^bold>K \<^bold>K" unfolding comb_defs ..
lemma "\<^bold>W = \<^bold>S \<^bold>S (\<^bold>S \<^bold>K)" unfolding comb_defs ..
lemma "\<^bold>W = \<^bold>C \<^bold>S \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>I = \<^bold>W \<^bold>K" unfolding comb_defs ..
lemma "\<^bold>T = \<^bold>S (\<^bold>K (\<^bold>S (\<^bold>S \<^bold>K \<^bold>K))) \<^bold>K"  unfolding comb_defs ..
lemma "\<^bold>O = \<^bold>S \<^bold>I" unfolding comb_defs ..
(*...*)

(***Miscellaneous***)   (*TODO: organize and expand*)
lemma "\<^bold>S = \<^bold>\<Phi>\<^sub>2\<^sub>1 \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>\<Phi>\<^sub>2\<^sub>1 = \<^bold>B (\<^bold>B \<^bold>S) \<^bold>B" unfolding comb_defs ..
lemma "\<^bold>\<Sigma> = \<^bold>B\<^sub>2 \<^bold>W \<^bold>B" unfolding comb_defs ..
lemma "\<^bold>W = \<^bold>\<Sigma> \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>W\<^sub>3\<^sub>1 = \<^bold>W \<circ> \<^bold>W" unfolding comb_defs ..

lemma "\<^bold>B \<^bold>A = \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>C \<^bold>B\<^sub>2 \<^bold>A = \<^bold>B" unfolding comb_defs ..
lemma "\<^bold>B \<^bold>C \<^bold>K  = \<^bold>B \<^bold>K " unfolding comb_defs ..
lemma "\<^bold>C (\<^bold>C x) = x" unfolding comb_defs ..
lemma "\<^bold>W f = \<^bold>S f \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>W f = \<^bold>\<Sigma> f \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>T = \<^bold>C \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>T = \<^bold>C \<^bold>A" unfolding comb_defs ..

lemma "\<^bold>V = \<^bold>L \<^bold>A\<^sub>2" unfolding comb_defs ..
lemma "\<^bold>V = \<^bold>L \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>I = \<^bold>R \<^bold>V" unfolding comb_defs ..
lemma "\<^bold>R \<^bold>V = \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>V = \<^bold>L \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>L \<^bold>V = \<^bold>R \<^bold>I" unfolding comb_defs ..
lemma "\<^bold>A\<^sub>2 = \<^bold>L(\<^bold>R \<^bold>I)" unfolding comb_defs ..
lemma "\<^bold>L (\<^bold>C \<^bold>I) = \<^bold>C (\<^bold>R \<^bold>I)" unfolding comb_defs ..
lemma "\<^bold>C (\<^bold>L \<^bold>I) = \<^bold>R (\<^bold>C \<^bold>I)" unfolding comb_defs ..

end