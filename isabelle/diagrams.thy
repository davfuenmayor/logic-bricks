section \<open>Commutative diagrams\<close>
text \<open>Commutative diagrams are convenient tools in mathematics that show how different paths of 
 functions or maps between objects lead to the same result.\<close>

theory diagrams
 imports relations
begin

subsection \<open>Basic Diagrams\<close>

subsubsection \<open>For Functions\<close>

text \<open>A commutative triangle states that a function "factorizes" as a composition of two given functions.\<close>
definition triangle :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> o" ("_-FACTOR") 
  where "triangle \<equiv> \<^bold>B\<^sub>1\<^sub>2 \<Q> \<^bold>I (\<ggreater>)"

text \<open>Commutative triangles are often read as "h factors through f and g", and diagrammatically represented as:\<close>
lemma "h-FACTOR f g = (h = f \<ggreater> g)" unfolding triangle_def comb_defs ..
abbreviation(input) triangleDiagram (" \<sqdot> \<midarrow>_\<rightarrow> \<sqdot> // \<setminus> \<down>_ // _\<rightarrow> \<sqdot>")
  where "\<sqdot> \<midarrow>f\<rightarrow> \<sqdot> 
          \<setminus>     \<down>g
            h\<rightarrow> \<sqdot>   \<equiv> h-FACTOR f g"

declare triangle_def[func_defs]

text \<open>We say that an endofunction is idempotent when it is identical to the composition with itself, or,
 in other words, when it factors through itself.\<close>
definition idempotent::"Set('a \<Rightarrow> 'a)"
  where "idempotent \<equiv> \<^bold>W\<^sub>3\<^sub>1 triangle"

declare idempotent_def[func_defs]

lemma "idempotent f =  \<sqdot> \<midarrow>f\<rightarrow> \<sqdot> 
                        \<setminus>     \<down>f
                          f\<rightarrow> \<sqdot>  " unfolding func_defs comb_defs ..

lemma "idempotent f = (\<forall>x. f x = f (f x))" unfolding func_defs comb_defs by metis
lemma "idempotent f = (f = (f \<ggreater> f))" unfolding func_defs comb_defs ..
lemma idempotent_def2: "idempotent = \<^bold>W (\<^bold>W \<^bold>B \<ggreater> \<Q>)" unfolding func_defs comb_defs by auto
lemma idempotent_def3: "idempotent = \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<subseteq>) range FP" unfolding func_defs comb_defs by metis
lemma "idempotent f = (range f \<subseteq> FP f)" unfolding idempotent_def3 comb_defs ..

definition square :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> o"
  where "square \<equiv> \<^bold>B\<^sub>2\<^sub>2 \<Q> (\<ggreater>) (\<ggreater>)"

abbreviation(input) squareDiagram (" \<sqdot> \<midarrow>_\<rightarrow> \<sqdot> // _\<down> \<down>_ // \<sqdot> \<midarrow>_\<rightarrow> \<sqdot>") 
  where " \<sqdot> \<midarrow>j\<rightarrow> \<sqdot> 
         i\<down>      \<down>l
          \<sqdot> \<midarrow>k\<rightarrow> \<sqdot>   \<equiv> square i j k l"

declare square_def[func_defs]

lemma " \<sqdot> \<midarrow>j\<rightarrow> \<sqdot> 
       i\<down>      \<down>l
        \<sqdot> \<midarrow>k\<rightarrow> \<sqdot>   = (i \<ggreater> k = j \<ggreater> l)" unfolding func_defs comb_defs ..

lemma " \<sqdot> \<midarrow>j\<rightarrow> \<sqdot> 
       i\<down>      \<down>l
        \<sqdot> \<midarrow>k\<rightarrow> \<sqdot>   =  \<sqdot> \<midarrow> j \<rightarrow> \<sqdot> 
                      \<setminus>       \<down>l
                        i\<ggreater>k\<rightarrow> \<sqdot>  " unfolding func_defs comb_defs ..


subsubsection \<open>For Relations\<close>

text \<open>A commutative triangle states that a relation "factorizes" as a composition of two given relations.\<close>
definition relTriangle::"Rel('a,'b) \<Rightarrow> Rel('a,'c) \<Rightarrow> Rel('c,'b) \<Rightarrow> o" ("_-FACTOR\<^sup>r") 
  where "relTriangle \<equiv> \<^bold>B\<^sub>1\<^sub>2 \<Q> \<^bold>I (;\<^sup>r)"

text \<open>Analogously to functions, we can represent this as a diagram (read as "H factors through F and G".)\<close>
lemma "H-FACTOR\<^sup>r F G = (H = F ;\<^sup>r G)" unfolding relTriangle_def comb_defs ..
abbreviation(input) relTriangleDiagram (" \<sqdot> \<midarrow>_\<rightarrow> \<sqdot> // \<setminus> \<down>_ // _\<rightarrow> \<sqdot>") 
  where "\<sqdot> \<midarrow>F\<rightarrow> \<sqdot> 
          \<setminus>     \<down>G
            H\<rightarrow> \<sqdot>   \<equiv> H-FACTOR\<^sup>r F G"

declare relTriangle_def[rel_defs]

text \<open>Functional and relational triangle diagrams correspond as expected.\<close>
lemma triangle_funrel: "totalFunction i \<Longrightarrow> totalFunction j \<Longrightarrow> totalFunction k \<Longrightarrow>
                           triangle (asFun i) (asFun j) (asFun k) = relTriangle i j k" unfolding rel_defs func_defs comb_defs by (metis (full_types))
lemma triangle_relfun: "relTriangle (asRel i) (asRel j) (asRel k) =    triangle i j k" unfolding rel_defs func_defs comb_defs by metis


text \<open>We say that an endorelation is idempotent when it is identical to the composition with itself, or,
 in other words, when it factors through itself.\<close>
definition relIdempotent::"Set(ERel('a))"
  where "relIdempotent \<equiv> \<^bold>W\<^sub>3\<^sub>1 relTriangle"

declare relIdempotent_def[rel_defs]

lemma "relIdempotent R =  \<sqdot> \<midarrow>R\<rightarrow> \<sqdot> 
                           \<setminus>     \<down>R
                             R\<rightarrow> \<sqdot>  " unfolding rel_defs comb_defs ..

lemma "relIdempotent R = (\<forall>a c. R a c \<leftrightarrow> (\<exists>b. R a b \<and> R b c))" unfolding rel_defs func_defs comb_defs by metis
lemma "relIdempotent R = (R = (R ;\<^sup>r R))" unfolding rel_defs comb_defs ..
lemma "relIdempotent = \<^bold>W ((\<^bold>W (;\<^sup>r)) \<ggreater> \<Q>)" unfolding rel_defs comb_defs by fastforce

text \<open>The relational notions correspond to their functional counterparts as expected.\<close>
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

text \<open>Beware: Composition in relational squares must always be read along the principal (NW–SE) diagonal!\<close>
lemma "relSquare i j k l = (i ;\<^sup>r k = j ;\<^sup>r l)" unfolding rel_defs comb_defs by meson
lemma "relSquare i j k l = ((k\<^sup>\<smile>) ;\<^sup>r (i\<^sup>\<smile>) = (l\<^sup>\<smile>) ;\<^sup>r (j\<^sup>\<smile>))" unfolding rel_defs func_defs comb_defs by meson
proposition "relSquare i j k l \<Longrightarrow> ((i\<^sup>\<smile>) ;\<^sup>r j = k ;\<^sup>r (l\<^sup>\<smile>))" nitpick \<comment> \<open>countermodel: wrong diagonal!\<close> oops
proposition "relSquare i j k l \<Longrightarrow> ((j\<^sup>\<smile>) ;\<^sup>r i = l ;\<^sup>r (k\<^sup>\<smile>))" nitpick \<comment> \<open>countermodel: wrong diagonal!\<close> oops

text \<open>An alternative definition in terms of pullbacks.\<close>
lemma relSquare_def2: "relSquare = \<^bold>C\<^sub>3\<^sub>4\<^sub>1\<^sub>2 (\<^bold>B\<^sub>2\<^sub>2 \<Q> (transpose \<ggreater> relPullback) (transpose \<ggreater> relPullback))" 
  unfolding rel_defs comb_defs unfolding func_defs comb_defs apply (rule ext)+ by meson

text \<open>Relational and functional squares correspond as expected.\<close>
lemma square_funrel: "totalFunction i \<Longrightarrow> totalFunction j \<Longrightarrow> totalFunction k \<Longrightarrow> totalFunction l \<Longrightarrow>
                         square (asFun i) (asFun j) (asFun k) (asFun l) = relSquare i j k l" unfolding rel_defs func_defs comb_defs by (metis (no_types, opaque_lifting) some_equality)
lemma square_relfun: "relSquare (asRel i) (asRel j) (asRel k) (asRel l) =    square i j k l" unfolding rel_defs func_defs comb_defs by metis


subsection \<open>Splittings\<close>

subsubsection \<open>For Functions\<close>

text \<open>We say of two functions f and g that they form a splitting (of the identity \<open>\<^bold>I\<close>) when g "undoes the
 effect" of f. In some literature, g (f) is called a left (right) inverse of f (g). We adopt another
 common (arguably less confusing) wording by referring to f (g) as the section (retraction) of g (f).\<close>
definition splitting::"Rel(('a \<Rightarrow> 'b),('b \<Rightarrow> 'a))"
  where "splitting \<equiv> \<^bold>I-FACTOR"

declare splitting_def[func_defs]

text \<open>A section f followed by the corresponding retraction g takes us back where we started.\<close>
lemma "splitting f g = \<sqdot> \<midarrow>f\<rightarrow> \<sqdot> 
                        \<setminus>     \<down>g
                          \<^bold>I\<rightarrow> \<sqdot>  " unfolding func_defs comb_defs ..

text \<open>We say that an endofunction is involutive when it is self-inverse (i.e. it forms a splitting with itself).\<close>
definition involutive::"Set('a \<Rightarrow> 'a)" 
  where "involutive \<equiv> \<^bold>W splitting"

declare involutive_def[func_defs] 

lemma "involutive f = (\<forall>x. x = f (f x))" unfolding func_defs comb_defs by metis
lemma "involutive f = (\<^bold>I = f \<ggreater> f)" unfolding func_defs comb_defs ..
lemma "involutive = \<^bold>W \<^bold>B \<ggreater> \<Q> \<^bold>I" unfolding func_defs comb_defs ..

text \<open>Identity is the only function which is both involutive and idempotent.\<close>
lemma "(involutive f \<and> idempotent f) = (f = \<^bold>I)"
  unfolding func_defs comb_defs by auto

text \<open>For involutive functions the notions of image and preimage coincide.\<close>
lemma invol_image: "involutive f \<Longrightarrow> image f = preimage f" unfolding func_defs comb_defs by metis
  
text \<open>For involutive functions the image (or preimage) operation is self-residuated wrt. \<open>(\<subseteq>)\<close>.\<close>
lemma invol_resid: "involutive f \<Longrightarrow> (image f A \<subseteq> B) = (A \<subseteq> image f B)"
  unfolding func_defs comb_defs by metis

text \<open>Some famous involutive functions:\<close>
lemma neg_invol: "involutive (\<not>)" unfolding func_defs comb_defs by simp
lemma compl_invol: "involutive \<midarrow>" unfolding func_defs comb_defs by simp
lemma complR_invol: "involutive \<midarrow>\<^sup>r" unfolding func_defs rel_defs comb_defs by simp
lemma dualop_invol: "involutive dualop" unfolding func_defs rel_defs comb_defs by simp


subsubsection \<open>For Relations\<close>

text \<open>Analogously to functions, we can say of two relations S and R that they form a splitting (of the
 identity \<open>\<Q>\<close>). Similarly, we call S (R) the section (retraction) of R (S).\<close>
definition relSplitting::"Rel(Rel('a,'b),Rel('b,'a))"
  where "relSplitting \<equiv> \<Q>-FACTOR\<^sup>r"

declare relSplitting_def[rel_defs]

text \<open>A section S followed by the corresponding retraction R takes us back where we started.\<close>
lemma "relSplitting S R = \<sqdot> \<midarrow>S\<rightarrow> \<sqdot> 
                           \<setminus>     \<down>R
                            \<Q> \<rightarrow> \<sqdot>  " unfolding rel_defs comb_defs by auto

text \<open>If a relation R (S) has a section (retraction) then it is right (left) total.\<close>
lemma "\<exists>(relSplitting\<^sup>\<smile> R) \<Longrightarrow> rightTotal R" unfolding rel_defs func_defs comb_defs by metis
lemma "\<exists>(relSplitting  S) \<Longrightarrow>  leftTotal S" unfolding rel_defs func_defs comb_defs by metis

text \<open>If a relation is both right-total and right-unique (surjective partial function) then it always 
 has a section, and moreover, when it has a retraction then that retraction is unique\<close>
lemma exist_section:     "rightTotal R \<Longrightarrow> rightUnique R \<Longrightarrow> \<exists>(relSplitting\<^sup>\<smile> R)" unfolding rel_defs comb_defs func_defs by metis
lemma unique_retraction: "rightTotal S \<Longrightarrow> rightUnique S \<Longrightarrow> unique(relSplitting S)" unfolding rel_defs comb_defs func_defs apply auto apply (rule ext)+ by metis

text \<open>If a relation is both left-total and left-unique (injective nondeterministic function) then it has
 a retraction, and moreover, when it has a section it is unique.\<close>
lemma exist_retraction: "leftTotal S \<Longrightarrow> leftUnique S \<Longrightarrow> \<exists>(relSplitting S)" unfolding rel_defs comb_defs func_defs by metis
lemma unique_section:   "leftTotal R \<Longrightarrow> leftUnique R \<Longrightarrow> unique(relSplitting\<^sup>\<smile> R)" unfolding rel_defs comb_defs func_defs apply auto apply (rule ext)+ by metis

lemma splitting_trans: "relSplitting R T \<Longrightarrow> relSplitting (T\<^sup>\<smile>) (R\<^sup>\<smile>)" unfolding rel_defs comb_defs func_defs by metis

text \<open>We say that an endorelation is involutive when it is self-inverse (i.e. it forms a splitting with itself).\<close>
definition relInvolutive::"Set(ERel('a))" 
  where "relInvolutive \<equiv> \<^bold>W relSplitting"

declare relInvolutive_def[rel_defs] 

lemma "relInvolutive R = (\<forall>a c. (a = c) \<leftrightarrow> (\<exists>b. R a b \<and> R b c))" unfolding rel_defs func_defs comb_defs by metis
lemma "relInvolutive R = (\<Q> = R ;\<^sup>r R)" unfolding rel_defs comb_defs ..
lemma "relInvolutive = \<^bold>W (;\<^sup>r) \<ggreater> \<Q> \<Q>" unfolding rel_defs comb_defs ..

text \<open>Equality is the only relation which is both involutive and idempotent.\<close>
lemma "(relInvolutive R \<and> relIdempotent R) = (R = \<Q>)"
  unfolding rel_defs func_defs comb_defs by auto

text \<open>Relational and functional notions correspond as expected.\<close>
lemma involutive_funRel: "involutive f = relInvolutive (asRel f)"
  unfolding rel_defs func_defs comb_defs by metis
lemma involutive_relFun: "totalFunction R \<Longrightarrow> relInvolutive R = involutive (asFun R)"
  unfolding rel_defs func_defs comb_defs apply auto apply (rule ext) apply (metis (full_types)) apply (rule ext)+ by (metis someI)


subsection \<open>Duality\<close>
text \<open>We encode (relational) duality as a relation between functions (relations). It arises by fixing 
 two of the arguments of a (relational) square as parameters (which we refer to as \<open>n\<^sub>1\<close> and \<open>n\<^sub>2\<close>).\<close>

subsubsection \<open>For Functions\<close>

text \<open>Two functions f and g are said to be dual wrt. to a pair of functions \<open>n\<^sub>1\<close> and \<open>n\<^sub>2\<close> (as parameters).\<close>
definition dual::"('a\<^sub>1 \<Rightarrow> 'a\<^sub>2) \<Rightarrow> ('b\<^sub>1 \<Rightarrow> 'b\<^sub>2) \<Rightarrow> Rel('a\<^sub>1 \<Rightarrow> 'b\<^sub>1, 'a\<^sub>2 \<Rightarrow> 'b\<^sub>2)" ("_,_-DUAL")
  where "n\<^sub>1,n\<^sub>2-DUAL f g \<equiv>   \<sqdot> \<midarrow>f\<rightarrow> \<sqdot> 
                          n\<^sub>1\<down>      \<down>n\<^sub>2
                            \<sqdot> \<midarrow>g\<rightarrow> \<sqdot>  "
declare dual_def[func_defs]


subsubsection \<open>For Relations\<close>

text \<open>Two relations R and T are said to be dual wrt. to a pair of relations \<open>n\<^sub>1\<close> and \<open>n\<^sub>2\<close> (as parameters).\<close>
definition relDual::"Rel('a\<^sub>1,'a\<^sub>2) \<Rightarrow> Rel('b\<^sub>1,'b\<^sub>2) \<Rightarrow> Rel(Rel('a\<^sub>1,'b\<^sub>1), Rel('a\<^sub>2,'b\<^sub>2))" ("_,_-DUAL\<^sup>r")
  where "n\<^sub>1,n\<^sub>2-DUAL\<^sup>r R T \<equiv>   \<sqdot> \<midarrow>R\<rightarrow> \<sqdot> 
                           n\<^sub>1\<down>      \<down>n\<^sub>2
                             \<sqdot> \<midarrow>T\<rightarrow> \<sqdot>   "

declare  relDual_def[rel_defs]

lemma "n\<^sub>1,n\<^sub>2-DUAL  f g = (n\<^sub>1 \<ggreater> g = f \<ggreater> n\<^sub>2)" unfolding func_defs comb_defs ..
lemma "n\<^sub>1,n\<^sub>2-DUAL\<^sup>r R T = (n\<^sub>1 ;\<^sup>r T = R ;\<^sup>r n\<^sub>2)" unfolding rel_defs func_defs comb_defs ..


text \<open>The notion of dual for relations corresponds to the counterpart notion for functions.\<close>
lemma "n\<^sub>1,n\<^sub>2-DUAL f g = (asRel n\<^sub>1),(asRel n\<^sub>2)-DUAL\<^sup>r (asRel f) (asRel g)" 
  unfolding rel_defs func_defs comb_defs by metis
lemma "totalFunction n\<^sub>1 \<Longrightarrow> totalFunction n\<^sub>2 \<Longrightarrow> totalFunction R \<Longrightarrow> totalFunction T 
            \<Longrightarrow> n\<^sub>1,n\<^sub>2-DUAL\<^sup>r R T = (asFun n\<^sub>1),(asFun n\<^sub>2)-DUAL (asFun R) (asFun T)"
  unfolding rel_defs func_defs comb_defs apply auto by (metis (full_types))+

text \<open>Existence of sections and retractions influences existence and uniqueness of duals. As a corollary, 
  if \<open>n\<^sub>1\<close> (resp. \<open>n\<^sub>2\<close>) is involutive, then the dual relation is well-defined (exists and is unique).\<close>
lemma "relSplitting n\<^sub>1 m \<Longrightarrow> n\<^sub>1,n\<^sub>2-DUAL\<^sup>r R (m ;\<^sup>r R ;\<^sup>r n\<^sub>2)" 
  unfolding rel_defs func_defs comb_defs by metis
lemma "relSplitting m n\<^sub>2 \<Longrightarrow> n\<^sub>1,n\<^sub>2-DUAL\<^sup>r (n\<^sub>1 ;\<^sup>r T ;\<^sup>r m) T" 
  unfolding rel_defs func_defs comb_defs by metis
lemma "\<exists>m. relSplitting m n\<^sub>1 \<Longrightarrow> unique(n\<^sub>1,n\<^sub>2-DUAL\<^sup>r R)" 
  unfolding relDual_def unfolding rel_defs func_defs comb_defs apply auto apply (rule ext)+ by (smt (verit, best))
lemma "\<exists>m. relSplitting n\<^sub>2 m \<Longrightarrow> unique((n\<^sub>1,n\<^sub>2-DUAL\<^sup>r)\<^sup>\<smile> T)"
  unfolding rel_defs func_defs comb_defs apply auto apply (rule ext)+ by (smt (verit, best))

text \<open>Moreover, if both \<open>n\<^sub>1\<close> and \<open>n\<^sub>2\<close> are involutive, then the dual relation is symmetric.\<close>
lemma relDual_symm: "relInvolutive n\<^sub>1 \<Longrightarrow> relInvolutive n\<^sub>2 \<Longrightarrow> n\<^sub>1,n\<^sub>2-DUAL\<^sup>r R T = n\<^sub>1,n\<^sub>2-DUAL\<^sup>r T R" 
  unfolding rel_defs func_defs comb_defs apply auto apply (rule ext)+ apply (smt (z3)) apply (rule ext)+ by (smt (z3))

end