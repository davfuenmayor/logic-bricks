theory diagrams
 imports rels
begin

section \<open>Commutative diagrams\<close>

subsection \<open>Basic diagrams\<close>

subsubsection \<open>For functions\<close>

(*A commutative triangle states that a function 'factorizes' as a composition of two given functions*)
definition triangle :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> o" ("_-FACTOR") 
  where "triangle \<equiv> \<^bold>B\<^sub>1\<^sub>2 \<Q> \<^bold>I (;)"

(*Commutative triangles are often read as "h factors through f and g", and diagrammatically represented as *)
lemma "h-FACTOR f g = (h = f ; g)" unfolding triangle_def comb_defs ..
abbreviation(input) triangleDiagram (" \<sqdot> \<midarrow>_\<rightarrow> \<sqdot> // \<setminus> \<down>_ // _\<rightarrow> \<sqdot>")
  where "\<sqdot> \<midarrow>f\<rightarrow> \<sqdot> 
          \<setminus>     \<down>g
            h\<rightarrow> \<sqdot>   \<equiv> h-FACTOR f g"

declare triangle_def[func_defs]

(*We say that an endofunction is idempotent when it is identical to the composition with itself, or,
 in other words, when it factors through itself.*)
definition idempotent::"Set('a \<Rightarrow> 'a)"
  where "idempotent \<equiv> \<^bold>W\<^sub>3\<^sub>1 triangle"

declare idempotent_def[func_defs]

lemma "idempotent f =  \<sqdot> \<midarrow>f\<rightarrow> \<sqdot> 
                        \<setminus>     \<down>f
                          f\<rightarrow> \<sqdot>  " unfolding func_defs comb_defs ..

lemma "idempotent f = (\<forall>x. f x = f (f x))" unfolding func_defs comb_defs by metis
lemma "idempotent f = (f = (f ; f))" unfolding func_defs comb_defs ..
lemma "idempotent = \<^bold>W (\<Q> \<circ> (\<^bold>W \<^bold>B))" unfolding func_defs comb_defs by fastforce


definition square :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> o"
  where "square \<equiv> \<^bold>B\<^sub>2\<^sub>2 \<Q> (;) (;)"

abbreviation(input) squareDiagram (" \<sqdot> \<midarrow>_\<rightarrow> \<sqdot> // _\<down> \<down>_ // \<sqdot> \<midarrow>_\<rightarrow> \<sqdot>") 
  where " \<sqdot> \<midarrow>j\<rightarrow> \<sqdot> 
         i\<down>      \<down>l
          \<sqdot> \<midarrow>k\<rightarrow> \<sqdot>   \<equiv> square i j k l"

declare square_def[func_defs]

lemma " \<sqdot> \<midarrow>j\<rightarrow> \<sqdot> 
       i\<down>      \<down>l
        \<sqdot> \<midarrow>k\<rightarrow> \<sqdot>   = (i ; k = j ; l)" unfolding func_defs comb_defs ..

lemma " \<sqdot> \<midarrow>j\<rightarrow> \<sqdot> 
       i\<down>      \<down>l
        \<sqdot> \<midarrow>k\<rightarrow> \<sqdot>   =  \<sqdot> \<midarrow> j \<rightarrow> \<sqdot> 
                      \<setminus>       \<down>l
                        i;k\<rightarrow> \<sqdot>  " unfolding func_defs comb_defs ..


subsubsection \<open>For relations\<close>

(*A commutative triangle states that a relation 'factorizes' as a composition of two given relations*)
definition relTriangle::"Rel('a,'b) \<Rightarrow> Rel('a,'c) \<Rightarrow> Rel('c,'b) \<Rightarrow> o" ("_-FACTOR\<^sup>r") 
  where "relTriangle \<equiv> \<^bold>B\<^sub>1\<^sub>2 \<Q> \<^bold>I (;\<^sup>r)"

(*Analogously to functions, we can represent this as a diagram (read as "H factors through F and G")*)
lemma "H-FACTOR\<^sup>r F G = (H = F ;\<^sup>r G)" unfolding relTriangle_def comb_defs ..
abbreviation(input) relTriangleDiagram (" \<sqdot> \<midarrow>_\<rightarrow> \<sqdot> // \<setminus> \<down>_ // _\<rightarrow> \<sqdot>") 
  where "\<sqdot> \<midarrow>F\<rightarrow> \<sqdot> 
          \<setminus>     \<down>G
            H\<rightarrow> \<sqdot>   \<equiv> H-FACTOR\<^sup>r F G"

declare relTriangle_def[rel_defs]

(*Functional and relational triangle diagrams correspond as expected*)
lemma triangle_funrel: "totalFunction i \<Longrightarrow> totalFunction j \<Longrightarrow> totalFunction k \<Longrightarrow>
                           triangle (asFun i) (asFun j) (asFun k) = relTriangle i j k" unfolding rel_defs func_defs comb_defs by (metis (full_types))
lemma triangle_relfun: "relTriangle (asRel i) (asRel j) (asRel k) =    triangle i j k" unfolding rel_defs func_defs comb_defs by metis


(*We say that an endorelation is idempotent when it is identical to the composition with itself, or,
 in other words, when it factors through itself.*)
definition relIdempotent::"Set(ERel('a))"
  where "relIdempotent \<equiv> \<^bold>W\<^sub>3\<^sub>1 relTriangle"

declare relIdempotent_def[rel_defs]

lemma "relIdempotent R =  \<sqdot> \<midarrow>R\<rightarrow> \<sqdot> 
                           \<setminus>     \<down>R
                             R\<rightarrow> \<sqdot>  " unfolding rel_defs comb_defs ..

lemma "relIdempotent R = (\<forall>a c. R a c \<leftrightarrow> (\<exists>b. R a b \<and> R b c))" unfolding rel_defs func_defs comb_defs by metis
lemma "relIdempotent R = (R = (R ;\<^sup>r R))" unfolding rel_defs comb_defs ..
lemma "relIdempotent = \<^bold>W (\<Q> \<circ> (\<^bold>W (\<circ>\<^sup>r)))" unfolding rel_defs comb_defs by fastforce

(*The relational notions correspond to their functional counterparts as expected*)
lemma idempotent_funRel: "idempotent f = relIdempotent (asRel f)" 
  unfolding rel_defs func_defs comb_defs apply auto apply metis apply (rule ext) by (metis (full_types))
lemma idempotent_relFun: "totalFunction R \<Longrightarrow> relIdempotent R = idempotent (asFun R)"
  unfolding rel_defs func_defs comb_defs apply auto apply (metis (mono_tags, lifting)) apply (rule ext)+ apply auto by (metis someI)+


definition relSquare::"Rel('a,'b) \<Rightarrow> Rel('a,'c) \<Rightarrow> Rel('b,'d) \<Rightarrow> Rel('c,'d) \<Rightarrow> o"
  where "relSquare \<equiv> \<^bold>B\<^sub>2\<^sub>2 \<Q> (;\<^sup>r) (;\<^sup>r)"

abbreviation(input) relSquareDiagram (" \<sqdot> \<midarrow>_\<rightarrow> \<sqdot> // _\<down> \<down>_ // \<sqdot> \<midarrow>_\<rightarrow> \<sqdot>") 
  where " \<sqdot> \<midarrow>j\<rightarrow> \<sqdot> 
         i\<down>      \<down>l
          \<sqdot> \<midarrow>k\<rightarrow> \<sqdot>   \<equiv> relSquare i j k l"

declare relSquare_def[rel_defs]

lemma " \<sqdot> \<midarrow>j\<rightarrow> \<sqdot> 
       i\<down>      \<down>l
        \<sqdot> \<midarrow>k\<rightarrow> \<sqdot>   = (i ;\<^sup>r k = j ;\<^sup>r l)" unfolding rel_defs comb_defs ..

lemma " \<sqdot> \<midarrow>j\<rightarrow> \<sqdot> 
       i\<down>      \<down>l
        \<sqdot> \<midarrow>k\<rightarrow> \<sqdot>   =  \<sqdot> \<midarrow> j  \<rightarrow> \<sqdot> 
                      \<setminus>        \<down>l
                       i ;\<^sup>r k\<rightarrow> \<sqdot>  " unfolding rel_defs comb_defs ..

(*Beware: Composition in relational squares must always be read along the principal (NW–SE) diagonal!*)
lemma "relSquare i j k l = (i ;\<^sup>r k = j ;\<^sup>r l)" unfolding rel_defs comb_defs by meson
lemma "relSquare i j k l = ((k\<^sup>\<smile>) ;\<^sup>r (i\<^sup>\<smile>) = (l\<^sup>\<smile>) ;\<^sup>r (j\<^sup>\<smile>))" unfolding rel_defs func_defs comb_defs by meson
lemma "relSquare i j k l \<Longrightarrow> ((i\<^sup>\<smile>) ;\<^sup>r j = k ;\<^sup>r (l\<^sup>\<smile>))" nitpick oops (*countermodel: wrong diagonal!*)
lemma "relSquare i j k l \<Longrightarrow> ((j\<^sup>\<smile>) ;\<^sup>r i = l ;\<^sup>r (k\<^sup>\<smile>))" nitpick oops (*countermodel: wrong diagonal!*)

(*An alternative definition in terms of pullbacks*)
lemma relSquare_def2: "relSquare = \<^bold>C\<^sub>3\<^sub>4\<^sub>1\<^sub>2 (\<^bold>B\<^sub>2\<^sub>2 \<Q> (relPullback \<circ> transpose) (relPullback \<circ> transpose))" 
  unfolding rel_defs comb_defs unfolding func_defs comb_defs apply (rule ext)+ by meson

(*Relational and functional squares correspond as expected*)
lemma square_funrel: "totalFunction i \<Longrightarrow> totalFunction j \<Longrightarrow> totalFunction k \<Longrightarrow> totalFunction l \<Longrightarrow>
                         square (asFun i) (asFun j) (asFun k) (asFun l) = relSquare i j k l" unfolding rel_defs func_defs comb_defs by (metis (no_types, opaque_lifting) some_equality)
lemma square_relfun: "relSquare (asRel i) (asRel j) (asRel k) (asRel l) =    square i j k l" unfolding rel_defs func_defs comb_defs by metis


subsection \<open>Splittings\<close>

subsubsection \<open>For functions\<close>

(*We say of two functions f and g that they form a splitting (of the identity \<^bold>I) when g 'undoes' the
 'effect' of f. In some literature, g (f) is called a left (right) inverse of f (g). We adopt another
 common (arguably less confusing) wording by referring to f (g) as the section (retraction) of g (f). *)
definition splitting::"Rel(('a \<Rightarrow> 'b),('b \<Rightarrow> 'a))"
  where "splitting \<equiv> \<^bold>I-FACTOR"

declare splitting_def[func_defs]

(*A section f followed by the corresponding retraction g takes us back where we started*)
lemma "splitting f g = \<sqdot> \<midarrow>f\<rightarrow> \<sqdot> 
                        \<setminus>     \<down>g
                          \<^bold>I\<rightarrow> \<sqdot>  " unfolding func_defs comb_defs ..

(*We say that an endofunction is involutive when it is self-inverse (i.e. it forms a splitting with itself)*)
definition involutive::"Set('a \<Rightarrow> 'a)" 
  where "involutive \<equiv> \<^bold>W splitting"

declare involutive_def[func_defs] 

lemma "involutive f = (\<forall>x. x = f (f x))" unfolding func_defs comb_defs by metis
lemma "involutive f = (\<^bold>I = f ; f)" unfolding func_defs comb_defs ..
lemma "involutive = (\<Q> \<^bold>I) \<circ> (\<^bold>W \<^bold>B)" unfolding func_defs comb_defs ..

(*Identity is the only function which is both involutive and idempotent*)
lemma "(involutive f \<and> idempotent f) = (f = \<^bold>I)"
  unfolding func_defs comb_defs by auto


subsubsection \<open>For relations\<close>

(*Analogously to functions, we can say of two relations S and R that they form a splitting (of the
 identity \<Q>). Similarly, we call S (R) the section (retraction) of R (S).*)
definition relSplitting::"Rel(Rel('a,'b),Rel('b,'a))"
  where "relSplitting \<equiv> \<Q>-FACTOR\<^sup>r"

declare relSplitting_def[rel_defs]

(*A section S followed by the corresponding retraction R takes us back where we started*)
lemma "relSplitting S R = \<sqdot> \<midarrow>S\<rightarrow> \<sqdot> 
                           \<setminus>     \<down>R
                            \<Q> \<rightarrow> \<sqdot>  " unfolding rel_defs comb_defs by auto

(*If a relation R (S) has a section (retraction) then it is right (left) total*)
lemma "\<exists>(relSplitting\<^sup>\<smile> R) \<Longrightarrow> rightTotal R" unfolding rel_defs func_defs comb_defs by metis
lemma "\<exists>(relSplitting  S) \<Longrightarrow>  leftTotal S" unfolding rel_defs func_defs comb_defs by metis

(*If a relation is both right-total and right-unique (surjective partial function) then it always 
 has a section, and moreover, when it has a retraction then that retraction is unique*)
lemma exist_section:     "rightTotal R \<Longrightarrow> rightUnique R \<Longrightarrow> \<exists>(relSplitting\<^sup>\<smile> R)" unfolding rel_defs comb_defs func_defs by metis
lemma unique_retraction: "rightTotal S \<Longrightarrow> rightUnique S \<Longrightarrow> !(relSplitting S)" unfolding rel_defs comb_defs func_defs apply auto apply (rule ext)+ by metis

(*If a relation is both left-total and left-unique (injective nondeterministic function) then it has
 a retraction, and moreover, when it has a section it is unique*)
lemma exist_retraction: "leftTotal S \<Longrightarrow> leftUnique S \<Longrightarrow> \<exists>(relSplitting S)" unfolding rel_defs comb_defs func_defs by metis
lemma unique_section:   "leftTotal R \<Longrightarrow> leftUnique R \<Longrightarrow> !(relSplitting\<^sup>\<smile> R)" unfolding rel_defs comb_defs func_defs apply auto apply (rule ext)+ by metis

lemma splitting_trans: "relSplitting R T \<Longrightarrow> relSplitting (T\<^sup>\<smile>) (R\<^sup>\<smile>)" unfolding rel_defs comb_defs func_defs by metis

(*We say that an endorelation is involutive when it is self-inverse (i.e. it forms a splitting with itself)*)
definition relInvolutive::"Set(ERel('a))" 
  where "relInvolutive \<equiv> \<^bold>W relSplitting"

declare relInvolutive_def[rel_defs] 

lemma "relInvolutive R = (\<forall>a c. (a = c) \<leftrightarrow> (\<exists>b. R a b \<and> R b c))" unfolding rel_defs func_defs comb_defs by metis
lemma "relInvolutive R = (\<Q> = R ;\<^sup>r R)" unfolding rel_defs comb_defs ..
lemma "relInvolutive = (\<Q> \<Q>) \<circ> (\<^bold>W (\<circ>\<^sup>r))" unfolding rel_defs comb_defs ..

(*Equality is the only relation which is both involutive and idempotent*)
lemma "(relInvolutive R \<and> relIdempotent R) = (R = \<Q>)"
  unfolding rel_defs func_defs comb_defs by auto

(*Relational and functional notions correspond as expected*)
lemma involutive_funRel: "involutive f = relInvolutive (asRel f)"
  unfolding rel_defs func_defs comb_defs by metis
lemma involutive_relFun: "totalFunction R \<Longrightarrow> relInvolutive R = involutive (asFun R)"
  unfolding rel_defs func_defs comb_defs apply auto apply (rule ext) apply (metis (full_types)) apply (rule ext)+ by (metis someI)


subsection \<open>Duality\<close>
(*We encode (relational) duality as a relation between functions (relations). It arises by fixing 
 two of the arguments of a (relational) square as parameters (which we refer to as n\<^sub>1 & n\<^sub>2).*)

subsubsection \<open>For functions\<close>

(*Two functions f and g are said to be dual wrt. to a pair of functions n\<^sub>1 & n\<^sub>2 (as parameters) *)
definition dual::"('a\<^sub>1 \<Rightarrow> 'a\<^sub>2) \<Rightarrow> ('b\<^sub>1 \<Rightarrow> 'b\<^sub>2) \<Rightarrow> Rel('a\<^sub>1 \<Rightarrow> 'b\<^sub>1, 'a\<^sub>2 \<Rightarrow> 'b\<^sub>2)" ("_,_-DUAL")
  where "n\<^sub>1,n\<^sub>2-DUAL f g \<equiv>   \<sqdot> \<midarrow>f\<rightarrow> \<sqdot> 
                          n\<^sub>1\<down>      \<down>n\<^sub>2
                            \<sqdot> \<midarrow>g\<rightarrow> \<sqdot>  "

(*We can also lift the previous notion of duality to apply to n-ary functions*)
definition dual2::"('a\<^sub>1 \<Rightarrow> 'a\<^sub>2) \<Rightarrow> ('b\<^sub>1 \<Rightarrow> 'b\<^sub>2) \<Rightarrow> Rel('e \<Rightarrow> 'a\<^sub>1 \<Rightarrow> 'b\<^sub>1, 'e \<Rightarrow> 'a\<^sub>2 \<Rightarrow> 'b\<^sub>2)" ("_,_-DUAL\<^sub>2")
  where "n\<^sub>1,n\<^sub>2-DUAL\<^sub>2 \<equiv> \<^bold>\<Phi>\<^sub>\<forall> (n\<^sub>1,n\<^sub>2-DUAL)"
definition dual3::"('a\<^sub>1 \<Rightarrow> 'a\<^sub>2) \<Rightarrow> ('b\<^sub>1 \<Rightarrow> 'b\<^sub>2) \<Rightarrow> Rel('e\<^sub>1 \<Rightarrow> 'e\<^sub>2 \<Rightarrow> 'a\<^sub>1 \<Rightarrow> 'b\<^sub>1, 'e\<^sub>1 \<Rightarrow> 'e\<^sub>2 \<Rightarrow> 'a\<^sub>2 \<Rightarrow> 'b\<^sub>2)" ("_,_-DUAL\<^sub>3")
  where "n\<^sub>1,n\<^sub>2-DUAL\<^sub>3 \<equiv> \<^bold>\<Phi>\<^sub>\<forall> (n\<^sub>1,n\<^sub>2-DUAL\<^sub>2)"
(*  ...  n\<^sub>1,n\<^sub>2-DUAL\<^sub>n \<equiv> \<^bold>\<Phi>\<^sub>\<forall> n\<^sub>1,n\<^sub>2-DUAL\<^sub>n\<^sub>-\<^sub>1 *)

declare dual_def[func_defs] dual2_def[func_defs] dual3_def[func_defs]

lemma "n\<^sub>1,n\<^sub>2-DUAL\<^sub>2 f g = (\<forall>x y. g x (n\<^sub>1 y) = n\<^sub>2 (f x y))" unfolding func_defs comb_defs by metis
lemma "n\<^sub>1,n\<^sub>2-DUAL\<^sub>3 f g = (\<forall>x y z. g x y (n\<^sub>1 z) = n\<^sub>2 (f x y z))" unfolding func_defs comb_defs by metis

(*Note that if both n\<^sub>1 & n\<^sub>2 are involutive, then the dual relation is symmetric*)
lemma dual_symm: "involutive n\<^sub>1 \<Longrightarrow> involutive n\<^sub>2 \<Longrightarrow> n\<^sub>1,n\<^sub>2-DUAL f g = n\<^sub>1,n\<^sub>2-DUAL f g" unfolding func_defs comb_defs by simp
lemma dual2_symm: "involutive n\<^sub>1 \<Longrightarrow> involutive n\<^sub>2 \<Longrightarrow> n\<^sub>1,n\<^sub>2-DUAL\<^sub>2 f g = n\<^sub>1,n\<^sub>2-DUAL\<^sub>2 f g" unfolding func_defs comb_defs by simp

(*This notion does NOT correspond with the so-called "De Morgan duality" (although they are not unrelated)*)
lemma "\<not>,\<not>-DUAL\<^sub>2 (\<and>) (\<or>)" nitpick oops (*countermodel*)

(*We add a (convenient?) diagram for duality of binary functions (for unary functions it is just the square)*)
abbreviation(input) dual2Diagram (" \<sqdot> \<Midarrow>_\<rightarrow> \<sqdot> // _\<down> \<down>_ // \<sqdot> \<Midarrow>_\<rightarrow> \<sqdot>") 
  where "  \<sqdot> \<Midarrow> f \<rightarrow> \<sqdot> 
         n\<^sub>1\<down>        \<down>n\<^sub>2
           \<sqdot> \<Midarrow> g \<rightarrow> \<sqdot>   \<equiv> n\<^sub>1,n\<^sub>2-DUAL\<^sub>2 f g"

(*Some examples of dual pairs of binary operations (recall that negation and complement are involutive)*)
lemma " \<sqdot> \<Midarrow> (\<and>) \<rightarrow> \<sqdot> 
      \<not>\<down>           \<down>\<not>
        \<sqdot> \<Midarrow> (\<rightarrow>) \<rightarrow> \<sqdot>  " unfolding func_defs comb_defs by simp

lemma " \<sqdot> \<Midarrow> (\<or>) \<rightarrow> \<sqdot> 
      \<not>\<down>           \<down>\<not>
        \<sqdot> \<Midarrow> (\<rightharpoonup>) \<rightarrow> \<sqdot>  " unfolding func_defs comb_defs by auto

lemma " \<sqdot> \<Midarrow> (\<Rightarrow>) \<rightarrow> \<sqdot> 
      \<midarrow>\<down>           \<down>\<midarrow>
        \<sqdot> \<Midarrow> (\<inter>) \<rightarrow> \<sqdot>  " unfolding func_defs comb_defs by simp

lemma " \<sqdot> \<Midarrow>  (\<setminus>)  \<rightarrow>  \<sqdot> 
      \<midarrow>\<down>             \<down>\<midarrow>
        \<sqdot> \<Midarrow>(\<midarrow>\<circ>\<^sub>2(\<inter>))\<rightarrow> \<sqdot>  " unfolding func_defs comb_defs by simp


subsubsection \<open>For relations\<close>

(*Two relations R and T are said to be dual wrt. to a pair of relations n\<^sub>1 & n\<^sub>2 (as parameters) *)
definition relDual::"Rel('a\<^sub>1,'a\<^sub>2) \<Rightarrow> Rel('b\<^sub>1,'b\<^sub>2) \<Rightarrow> Rel(Rel('a\<^sub>1,'b\<^sub>1), Rel('a\<^sub>2,'b\<^sub>2))" ("_,_-DUAL\<^sup>r")
  where "n\<^sub>1,n\<^sub>2-DUAL\<^sup>r R T \<equiv>   \<sqdot> \<midarrow>R\<rightarrow> \<sqdot> 
                           n\<^sub>1\<down>      \<down>n\<^sub>2
                             \<sqdot> \<midarrow>T\<rightarrow> \<sqdot>   "

declare  relDual_def[rel_defs]

lemma "n\<^sub>1,n\<^sub>2-DUAL  f g = (n\<^sub>1 ; g = f ; n\<^sub>2)" unfolding func_defs comb_defs ..
lemma "n\<^sub>1,n\<^sub>2-DUAL\<^sup>r R T = (n\<^sub>1 ;\<^sup>r T = R ;\<^sup>r n\<^sub>2)" unfolding rel_defs func_defs comb_defs ..


(*The notion of dual for relations corresponds to the counterpart notion for functions.*)
lemma "n\<^sub>1,n\<^sub>2-DUAL f g = (asRel n\<^sub>1),(asRel n\<^sub>2)-DUAL\<^sup>r (asRel f) (asRel g)" 
  unfolding rel_defs func_defs comb_defs by metis
lemma "totalFunction n\<^sub>1 \<Longrightarrow> totalFunction n\<^sub>2 \<Longrightarrow> totalFunction R \<Longrightarrow> totalFunction T 
            \<Longrightarrow> n\<^sub>1,n\<^sub>2-DUAL\<^sup>r R T = (asFun n\<^sub>1),(asFun n\<^sub>2)-DUAL (asFun R) (asFun T)"
  unfolding rel_defs func_defs comb_defs apply auto by (metis (full_types))+

(*Existence of sections and retractions influences existence and uniqueness of duals. As a corollary, 
  if n\<^sub>1 (resp. n\<^sub>2) is involutive, then the dual relation is well-defined (exists and is unique).*)
lemma "relSplitting n\<^sub>1 m \<Longrightarrow> n\<^sub>1,n\<^sub>2-DUAL\<^sup>r R (m ;\<^sup>r R ;\<^sup>r n\<^sub>2)" 
  unfolding rel_defs func_defs comb_defs by metis
lemma "relSplitting m n\<^sub>2 \<Longrightarrow> n\<^sub>1,n\<^sub>2-DUAL\<^sup>r (n\<^sub>1 ;\<^sup>r T ;\<^sup>r m) T" 
  unfolding rel_defs func_defs comb_defs by metis
lemma "\<exists>m. relSplitting m n\<^sub>1 \<Longrightarrow> !(n\<^sub>1,n\<^sub>2-DUAL\<^sup>r R)" 
  unfolding relDual_def by (smt (verit, del_insts) B12_comb_def B22_comb_def I_comb_def relComp_assoc relComp_id2 relSplitting_def relSquare_def relTriangle_def unique_def)
lemma "\<exists>m. relSplitting n\<^sub>2 m \<Longrightarrow> !((n\<^sub>1,n\<^sub>2-DUAL\<^sup>r)\<^sup>\<smile> T)"
  unfolding rel_defs func_defs comb_defs apply auto apply (rule ext)+ by (smt (verit, best))

(*Moreover, if both n\<^sub>1 & n\<^sub>2 are involutive, then the dual relation is symmetric.*)
lemma relDual_symm: "relInvolutive n\<^sub>1 \<Longrightarrow> relInvolutive n\<^sub>2 \<Longrightarrow> n\<^sub>1,n\<^sub>2-DUAL\<^sup>r R T = n\<^sub>1,n\<^sub>2-DUAL\<^sup>r T R" 
  unfolding rel_defs func_defs comb_defs apply auto apply (rule ext)+ apply (smt (z3)) apply (rule ext)+ by (smt (z3))

end