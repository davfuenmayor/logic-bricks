section \<open>Endorelations\<close>
text \<open>Endorelations are particular cases of relations where the relata have the same type.\<close>

theory endorelations (* A basic theory of endorelations *)
imports relations
begin

named_theorems endorel_defs

subsection \<open>Intervals and Powers\<close>

subsubsection \<open>Intervals\<close>

text \<open>We now conveniently encode a notion of "interval" (wrt given relation R) as the set of elements 
  that lie between or "interpolate" a given pair of points (seen as "boundaries").\<close>
definition interval::"ERel('a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> Set('a)" ("_-interval")
  where "interval \<equiv> \<^bold>W interpolants"
text \<open>And also introduce a convenient dual notion.\<close>
definition dualInterval::"ERel('a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> Set('a)" ("_-dualInterval")
  where "dualInterval \<equiv> \<^bold>W dualInterpolants"

declare interval_def[endorel_defs] dualInterval_def[endorel_defs]

lemma "R-interval a b     = (\<lambda>c. R a c \<and> R c b)" unfolding endorel_defs rel_defs func_defs comb_defs ..
lemma "R-dualInterval a b = (\<lambda>c. R a c \<or> R c b)" unfolding endorel_defs rel_defs func_defs comb_defs ..


subsubsection \<open>Powers\<close>

text \<open>The set of all powers (via iterated composition) for a given endorelation can be defined in two 
 ways, depending whether we want to include the "zero-power" (i.e. \<open>R\<^sup>0 = \<Q>\<close>) or not.\<close>
definition relPower::"ERel(ERel('a))"
  where "relPower \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 indSet\<^sub>1 \<Q> (\<circ>\<^sup>r)"
definition relPower0::"ERel(ERel('a))"
  where "relPower0 \<equiv> \<^bold>B (indSet\<^sub>1 (\<Q> \<Q>)) (\<circ>\<^sup>r)"

declare relPower_def[endorel_defs] relPower0_def[endorel_defs]

lemma "relPower R = indSet\<^sub>1 {R} ((\<circ>\<^sup>r) R)" unfolding endorel_defs comb_defs ..
lemma relPower_def2: "relPower R T = (\<forall>S. (\<forall>H. S H \<rightarrow> S (R \<circ>\<^sup>r H)) \<rightarrow> S R \<rightarrow> S T)" unfolding endorel_defs func_defs comb_defs by auto

lemma "relPower0 R = indSet\<^sub>1 {\<Q>} ((\<circ>\<^sup>r) R)" unfolding endorel_defs comb_defs ..
lemma relPower0_def2: "relPower0 R T = (\<forall>S. (\<forall>H. S H \<rightarrow> S (R \<circ>\<^sup>r H)) \<rightarrow> S \<Q> \<rightarrow> S T)" unfolding endorel_defs func_defs comb_defs by auto

text \<open>Definitions work as intended:\<close>
proposition "relPower R \<Q>" nitpick \<comment> \<open>countermodel found\<close> oops
lemma "relPower R R" unfolding relPower_def2 by simp
lemma "relPower R (R \<circ>\<^sup>r R)" unfolding relPower_def2 by simp
lemma "relPower R (R \<circ>\<^sup>r R \<circ>\<^sup>r R \<circ>\<^sup>r R \<circ>\<^sup>r R \<circ>\<^sup>r R \<circ>\<^sup>r R)" unfolding relPower_def2 by (simp add: relComp_assoc)
lemma "relPower0 R \<Q>" unfolding relPower0_def2 by simp
lemma "relPower0 R R" unfolding relPower0_def2 by (metis relComp_id2)
lemma "relPower0 R (R \<circ>\<^sup>r R)" unfolding relPower0_def2 by (metis relComp_id2)
lemma "relPower0 R (R \<circ>\<^sup>r R \<circ>\<^sup>r R \<circ>\<^sup>r R \<circ>\<^sup>r R \<circ>\<^sup>r R \<circ>\<^sup>r R)" unfolding relPower0_def2 by (metis (no_types, lifting) relComp_assoc relComp_id2)

lemma relPower_ind:  "relPower  R T \<Longrightarrow> relPower  R (R \<circ>\<^sup>r T)" by (metis relPower_def2)
lemma relPower0_ind: "relPower0 R T \<Longrightarrow> relPower0 R (R \<circ>\<^sup>r T)" using relPower0_def2 by blast



subsection \<open>Properties and Operations\<close>

subsubsection \<open>Reflexivity and Irreflexivity\<close>

text \<open>Relations are called reflexive (aka. diagonal) resp. irreflexive (aka. antidiagonal) when they are
 larger than identity/equality resp. smaller than difference/disequality.\<close>
definition reflexive::"Set(ERel('a))"
  where \<open>reflexive   \<equiv> (\<subseteq>\<^sup>r) \<Q>\<close>
definition irreflexive::"Set(ERel('a))"
  where \<open>irreflexive \<equiv> (\<supseteq>\<^sup>r) \<D>\<close>

declare reflexive_def[endorel_defs] irreflexive_def[endorel_defs]

lemma \<open>reflexive R   = \<Q> \<subseteq>\<^sup>r R\<close> unfolding endorel_defs ..
lemma \<open>irreflexive R = R \<subseteq>\<^sup>r \<D>\<close> unfolding endorel_defs ..

text \<open>Both properties are "complementary" in the expected way.\<close>
lemma reflexive_compl:     "reflexive R\<^sup>\<midarrow> = irreflexive R" unfolding endorel_defs rel_defs func_defs comb_defs by auto
lemma irreflexive_compl: "irreflexive R\<^sup>\<midarrow> = reflexive R" unfolding endorel_defs rel_defs func_defs comb_defs by auto

text \<open>An alternative pair of definitions.\<close>
lemma reflexive_def2:     "reflexive = \<forall> \<circ> \<Delta>" unfolding endorel_defs rel_defs func_defs comb_defs by simp
lemma irreflexive_def2: "irreflexive = \<nexists> \<circ> \<Delta>" unfolding endorel_defs rel_defs func_defs comb_defs by auto
lemma "reflexive   R = (\<forall>a. R a a)" unfolding reflexive_def2 comb_defs ..
lemma "irreflexive R = (\<forall>a. \<not>R a a)" unfolding irreflexive_def2 comb_defs by simp

text \<open>We can naturally obtain a reflexive resp. irreflexive relations via the following operators.\<close>
definition reflexiveClosure::"ERel('a) \<Rightarrow> ERel('a)"
  where "reflexiveClosure    \<equiv> (\<union>\<^sup>r) \<Q>"
definition irreflexiveInterior::"ERel('a) \<Rightarrow> ERel('a)"
  where "irreflexiveInterior \<equiv> (\<inter>\<^sup>r) \<D>"

declare reflexiveClosure_def[endorel_defs] irreflexiveInterior_def[endorel_defs]

lemma "reflexiveClosure    R = (R \<union>\<^sup>r \<Q>)" unfolding endorel_defs rel_defs func_defs comb_defs by auto
lemma "irreflexiveInterior R = (R \<inter>\<^sup>r \<D>)" unfolding endorel_defs rel_defs func_defs comb_defs by auto

text \<open>The operators reflexive closure and irreflexive interior are duals wrt. relation-complement.\<close>
lemma "irreflexiveInterior (R\<^sup>\<midarrow>) = (reflexiveClosure R)\<^sup>\<midarrow>" unfolding endorel_defs rel_defs func_defs comb_defs by simp
lemma "reflexiveClosure (R\<^sup>\<midarrow>) = (irreflexiveInterior R)\<^sup>\<midarrow>" unfolding endorel_defs rel_defs func_defs comb_defs by simp

text \<open>All reflexive resp. irreflexive relations arise via their corresponding closure resp. interior operator.\<close>
lemma reflexive_def3: "reflexive = range reflexiveClosure" unfolding endorel_defs rel_defs func_defs comb_defs by blast
lemma irreflexive_def3: "irreflexive = range irreflexiveInterior" unfolding endorel_defs rel_defs func_defs comb_defs by blast

text \<open>We now check that these unary relation-operators are indeed closure resp. interior operators.\<close>
lemma \<open>(\<subseteq>\<^sup>r)-CLOSURE reflexiveClosure\<close> unfolding endorel_defs rel_defs func_defs comb_defs by simp
lemma \<open>(\<subseteq>\<^sup>r)-INTERIOR irreflexiveInterior\<close> unfolding endorel_defs rel_defs func_defs comb_defs by simp

text \<open>Thus, reflexive resp. irreflexive relations are the fixed points of the corresponding operators.\<close>
lemma reflexive_def4:     \<open>reflexive = FP reflexiveClosure\<close> unfolding subrel_defFP endorel_defs comb_defs ..
lemma irreflexive_def4: \<open>irreflexive = FP irreflexiveInterior\<close> unfolding endorel_defs rel_defs func_defs comb_defs by metis

text \<open>The smallest reflexive super-relation resp. largest irreflexive subrelation.\<close>
lemma "reflexiveClosure R = \<Inter>\<^sup>r(\<lambda>T. R \<subseteq>\<^sup>r T \<and> reflexive T)" \<comment> \<open>proof by external provers\<close> oops  (*TODO: reconstruct proof*)
lemma "irreflexiveInterior R = \<Union>\<^sup>r(\<lambda>T. T \<subseteq>\<^sup>r R \<and> irreflexive T)" \<comment> \<open>proof by external provers\<close> oops (*TODO: reconstruct proof*)


subsubsection \<open>Strong-identity, Weak-difference, and Tests\<close>

text \<open>We call relations strong-identities (aka. coreflexive, "tests") resp. weak-differences when they are 
 smaller than identity/equality resp. larger than difference/disequality.\<close>
definition strongIdentity::"Set(ERel('a))" 
  where "strongIdentity \<equiv> (\<supseteq>\<^sup>r) \<Q>"
definition weakDifference::"Set(ERel('a))"
  where "weakDifference \<equiv> (\<subseteq>\<^sup>r) \<D>"

declare strongIdentity_def[endorel_defs] weakDifference_def[endorel_defs]

lemma \<open>strongIdentity   R = R \<subseteq>\<^sup>r \<Q>\<close> unfolding endorel_defs ..
lemma \<open>weakDifference R = \<D> \<subseteq>\<^sup>r R\<close> unfolding endorel_defs ..

text \<open>Elements in strong-identities are only related to themselves (may be related to none).\<close>
lemma strongIdentity_def2: "strongIdentity R = (\<forall>a. R a \<subseteq> {a})" unfolding endorel_defs rel_defs func_defs comb_defs ..
text \<open>Elements in weak-differences are related to (at least) everyone else (may be also related to themselves).\<close>
lemma weakDifference_def2: "weakDifference R = (\<forall>a. \<lbrace>a\<rbrace> \<subseteq> R a)" unfolding endorel_defs rel_defs func_defs comb_defs ..

text \<open>They are "weaker" than identity resp. difference since they may feature anti-diagonal resp. diagonal elements.\<close>
proposition "strongIdentity R \<and> \<not>R a a" nitpick[satisfy] \<comment> \<open>satisfying model found\<close> oops 
proposition "weakDifference R \<and> R a a" nitpick[satisfy] \<comment> \<open>satisfying model found\<close> oops


text \<open>We can naturally obtain strong-identities resp. weak-differences via the following operators.\<close>
definition strongIdentityInterior::"ERel('a) \<Rightarrow> ERel('a)" ("(_)\<^sup>!")
  where "strongIdentityInterior \<equiv> (\<inter>\<^sup>r) \<Q>"
definition weakDifferenceClosure::"ERel('a) \<Rightarrow> ERel('a)" ("(_)\<^sup>?")
  where "weakDifferenceClosure  \<equiv> (\<union>\<^sup>r) \<D>"

declare weakDifferenceClosure_def[endorel_defs] strongIdentityInterior_def[endorel_defs]

lemma "strongIdentityInterior R = (R \<inter>\<^sup>r \<Q>)" unfolding endorel_defs rel_defs func_defs comb_defs by auto
lemma "weakDifferenceClosure  R = (R \<union>\<^sup>r \<D>)" unfolding endorel_defs rel_defs func_defs comb_defs by auto

text \<open>The notions of strong-identity-interior and weak-difference-closure are duals wrt. relation-complement.\<close>
lemma "R\<^sup>\<midarrow>\<^sup>? = R\<^sup>!\<^sup>\<midarrow>" unfolding endorel_defs rel_defs func_defs comb_defs by simp
lemma "R\<^sup>\<midarrow>\<^sup>! = R\<^sup>?\<^sup>\<midarrow>" unfolding endorel_defs rel_defs func_defs comb_defs by auto

text \<open>All strong-identity resp. weak-difference relations arise via their corresponding interior resp. closure operator.\<close>
lemma strongIdentity_def3: "strongIdentity = range strongIdentityInterior" unfolding endorel_defs rel_defs func_defs comb_defs by blast
lemma weakDifference_def3: "weakDifference = range weakDifferenceClosure" unfolding endorel_defs rel_defs func_defs comb_defs by blast

text \<open>We now check that these unary relation-operators are indeed closure resp. interior operators.\<close>
lemma \<open>(\<subseteq>\<^sup>r)-INTERIOR strongIdentityInterior\<close> unfolding endorel_defs rel_defs func_defs comb_defs by simp
lemma \<open>(\<subseteq>\<^sup>r)-CLOSURE weakDifferenceClosure\<close> unfolding endorel_defs rel_defs func_defs comb_defs by simp

text \<open>Thus, strong-identity resp. weak-difference relations are the fixed points of the corresponding operators.\<close>
lemma strongIdentity_def4:     \<open>strongIdentity = FP strongIdentityInterior\<close> unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma weakDifference_def4: \<open>weakDifference = FP weakDifferenceClosure\<close> unfolding subrel_defFP endorel_defs comb_defs ..

text \<open>The largest strong-identity sub-relation resp. smallest weak-difference super-relation.\<close>
lemma "R\<^sup>! = \<Union>\<^sup>r(\<lambda>T. T \<subseteq>\<^sup>r R \<and> strongIdentity T)" \<comment> \<open>proof by external provers\<close> oops (*TODO: reconstruct proof*)
lemma "R\<^sup>? = \<Inter>\<^sup>r(\<lambda>T. R \<subseteq>\<^sup>r T \<and> weakDifference T)" \<comment> \<open>proof by external provers\<close> oops  (*TODO: reconstruct proof*)


text \<open>A convenient way of disguising sets as endorelations (cf. dynamic logics and program algebras).\<close>
definition test::"Set('a) \<Rightarrow> ERel('a)" (*the customary question mark (?) notation omitted to avoid confusions*)
  where "test \<equiv> strongIdentityInterior \<circ> \<^bold>K"
definition dualtest::"Set('a) \<Rightarrow> ERel('a)"
  where "dualtest \<equiv> weakDifferenceClosure \<circ> \<^bold>K"

declare test_def[endorel_defs] dualtest_def[endorel_defs]

lemma test_def2: "test = strongIdentityInterior \<circ> (\<^bold>W (\<times>))" unfolding endorel_defs rel_defs func_defs comb_defs by auto
lemma "test A = (A \<times> A)\<^sup>!" unfolding test_def2 comb_defs ..
lemma "test A = \<Q> \<inter>\<^sup>r (A \<times> A)" unfolding test_def2 endorel_defs comb_defs ..  (* equality (\<Q>) restricted to A*)

lemma dualtest_def2: "dualtest = weakDifferenceClosure \<circ> (\<^bold>W (\<times>))" unfolding endorel_defs rel_defs func_defs comb_defs by auto
lemma "dualtest A = (A \<times> A)\<^sup>?" unfolding dualtest_def2 comb_defs ..
lemma "dualtest A = \<D> \<union>\<^sup>r (A \<times> A)" unfolding dualtest_def2 endorel_defs comb_defs ..

lemma test_def3: "test = strongIdentityInterior \<circ> leftCylinder" unfolding leftCylinder_def test_def ..
lemma dualtest_def3: "dualtest = weakDifferenceClosure \<circ> leftCylinder" unfolding leftCylinder_def dualtest_def ..

lemma test_def4: "test = strongIdentityInterior \<circ> rightCylinder" unfolding endorel_defs rel_defs func_defs comb_defs by auto
lemma dualtest_def4: "dualtest = weakDifferenceClosure \<circ> rightCylinder" unfolding endorel_defs rel_defs func_defs comb_defs by auto

text \<open>Both are duals wrt relation/set complement, as expected.\<close>
lemma test_dual1: "(test A)\<^sup>\<midarrow> = dualtest (\<midarrow>A)" unfolding endorel_defs rel_defs func_defs comb_defs by simp
lemma test_dual2: "(dualtest A)\<^sup>\<midarrow> = test (\<midarrow>A)" unfolding endorel_defs rel_defs func_defs comb_defs by simp

text \<open>Both test resp. dual-test act as (full) inverses of diagonal (assuming strong-identity resp. weak-difference)\<close>
lemma "\<Delta> (test A) = A" unfolding endorel_defs rel_defs func_defs comb_defs by simp
lemma "\<Delta> (dualtest A) = A" unfolding endorel_defs rel_defs func_defs comb_defs by simp
lemma "strongIdentity A \<Longrightarrow> test (\<Delta> A) = A" unfolding endorel_defs rel_defs func_defs comb_defs by auto
lemma "weakDifference A \<Longrightarrow> dualtest (\<Delta> A) = A" unfolding endorel_defs rel_defs func_defs comb_defs by force

text \<open>In fact, all strong-identities resp. weak-differences arise via the test resp- dual-test operators (applied to some set).\<close>
lemma strongIdentity_def5: "strongIdentity = range test" unfolding strongIdentity_def3 endorel_defs rel_defs func_defs comb_defs by fastforce
lemma weakDifference_def5: "weakDifference = range dualtest" unfolding weakDifference_def3 endorel_defs rel_defs func_defs comb_defs by fastforce


subsubsection \<open>Seriality and Quasireflexivity\<close>

text \<open>Following usual practice, we shal call "serial" those endorelations that are left-total.\<close>
abbreviation(input) serial::"Set(ERel('a))"
  where "serial \<equiv> leftTotal"

text \<open>The following "weakening" of reflexivity does not imply seriality (i.e. left-totality).\<close>
definition quasireflexive::"Set(ERel('a))"
  where "quasireflexive \<equiv> leftRange \<sqsubseteq> \<Delta>"

declare quasireflexive_def[endorel_defs]

lemma "quasireflexive R = leftRange R \<subseteq> \<Delta> R" unfolding endorel_defs rel_defs comb_defs ..
lemma "quasireflexive R = (\<forall>x. \<exists>(R x) \<rightarrow> R x x)" unfolding endorel_defs rel_defs func_defs comb_defs ..

text \<open>We have in fact that:\<close>
lemma reflexive_def5: "reflexive R = (serial R \<and> quasireflexive R)" unfolding endorel_defs rel_defs func_defs comb_defs by metis

text \<open>The quasireflexive closure of a relation: elements related to someone else become related to themselves.\<close>
definition quasireflexiveClosure::"ERel('a) \<Rightarrow> ERel('a)"
  where "quasireflexiveClosure \<equiv> \<^bold>W ((\<union>\<^sup>r) \<circ> ((\<inter>\<^sup>r) \<Q>) \<circ> ((\<times>) \<UU>) \<circ> leftRange)"

text \<open>The serial extension of a relation: elements not related to anyone else become related to themselves.\<close>
definition serialExtension::"ERel('a) \<Rightarrow> ERel('a)"
  where "serialExtension \<equiv> \<^bold>W ((\<union>\<^sup>r) \<circ> ((\<inter>\<^sup>r) \<Q>) \<circ> ((\<times>) \<UU>) \<circ> \<midarrow> \<circ> leftRange)"

declare serialExtension_def[endorel_defs] quasireflexiveClosure_def[endorel_defs]

lemma "quasireflexiveClosure R = (R \<union>\<^sup>r (\<Q> \<inter>\<^sup>r (\<UU> \<times> (leftRange R))))" unfolding endorel_defs rel_defs func_defs comb_defs by auto
lemma "serialExtension R = (R \<union>\<^sup>r (\<Q> \<inter>\<^sup>r (\<UU> \<times> \<midarrow>(leftRange R))))" unfolding endorel_defs rel_defs func_defs comb_defs by auto

lemma "serial (serialExtension R)" 
  unfolding endorel_defs rel_defs func_defs comb_defs by auto
lemma "quasireflexive (quasireflexiveClosure R)" 
  unfolding endorel_defs rel_defs func_defs comb_defs by auto


subsubsection \<open>Symmetry, Connectedness, and co.\<close>

text \<open>We introduce two ways of "symmetrizing" a given relation R: The symmetric interior and closure operations.
 The intuition is that the symmetric interior/closure of R intersects/merges R with its converse, thus
 generating R's largest/smallest symmetric sub/super-relation.\<close>
definition symmetricInterior::"ERel('a) \<Rightarrow> ERel('a)"
  where "symmetricInterior \<equiv> \<^bold>S (\<inter>\<^sup>r) \<smile>" \<comment> \<open>aka. symmetric part of R\<close>
definition symmetricClosure::"ERel('a) \<Rightarrow> ERel('a)"
  where "symmetricClosure  \<equiv> \<^bold>S (\<union>\<^sup>r) \<smile>"

declare symmetricInterior_def[endorel_defs] symmetricClosure_def[endorel_defs]

lemma "symmetricInterior R = R \<inter>\<^sup>r (R\<^sup>\<smile>)" unfolding endorel_defs comb_defs ..
lemma "symmetricClosure R = R \<union>\<^sup>r (R\<^sup>\<smile>)" unfolding endorel_defs comb_defs ..

lemma "symmetricInterior R = (\<lambda>x y. R x y \<and> R y x)" unfolding endorel_defs rel_defs func_defs comb_defs ..
lemma "symmetricClosure R  = (\<lambda>x y. R x y \<or> R y x)" unfolding endorel_defs rel_defs func_defs comb_defs ..

lemma symmetricInterior_def2: "symmetricInterior = \<^bold>W \<circ> interval" unfolding endorel_defs rel_defs func_defs comb_defs ..
lemma symmetricClosure_def2:  "symmetricClosure  = \<^bold>W \<circ> dualInterval" unfolding endorel_defs rel_defs func_defs comb_defs ..

lemma "symmetricInterior R a = (\<lambda>x. R-interval a a x)" unfolding endorel_defs rel_defs func_defs comb_defs ..
lemma "symmetricClosure R a = (\<lambda>x. R-dualInterval a a x)" unfolding endorel_defs rel_defs func_defs comb_defs ..

text \<open>The notions of symmetric closure and symmetric interior are duals wrt. relation-complement.\<close>
lemma "symmetricInterior (R\<^sup>\<midarrow>) = (symmetricClosure R)\<^sup>\<midarrow>" unfolding endorel_defs rel_defs func_defs comb_defs by simp
lemma "symmetricClosure (R\<^sup>\<midarrow>) = (symmetricInterior R)\<^sup>\<midarrow>" unfolding endorel_defs rel_defs func_defs comb_defs by simp

text \<open>The properties of (ir)reflexivity and co(ir)reflexivity are preserved by symmetric interior and closure.\<close>
lemma reflexive_si: \<open>reflexive R = reflexive (symmetricInterior R)\<close> unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma weakDifference_si: \<open>weakDifference R = weakDifference (symmetricInterior R)\<close> unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma strongIdentity_sc: \<open>strongIdentity R = strongIdentity (symmetricClosure R)\<close> unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma irreflexive_sc: \<open>irreflexive R = irreflexive (symmetricClosure R)\<close> unfolding endorel_defs rel_defs func_defs comb_defs by metis

text \<open>A relation is symmetric when it is a fixed-point of the symmetric interior or closure.\<close>
definition symmetric::"Set(ERel('a))"
  where \<open>symmetric \<equiv> FP symmetricInterior\<close>

lemma symmetric_defT: "symmetric = FP symmetricClosure" 
  unfolding symmetric_def endorel_defs rel_defs func_defs comb_defs by metis

declare symmetric_def[endorel_defs]

lemma symmetric_def2:  \<open>symmetric = \<^bold>S (\<subseteq>\<^sup>r) \<smile>\<close> unfolding endorel_defs func_defs rel_defs comb_defs by metis
lemma symmetric_defT2: \<open>symmetric = \<^bold>S (\<supseteq>\<^sup>r) \<smile>\<close> unfolding endorel_defs func_defs rel_defs comb_defs by metis

lemma symmetric_reldef:   \<open>symmetric R = R  \<subseteq>\<^sup>r R\<^sup>\<smile>\<close> unfolding symmetric_def2 comb_defs ..
lemma symmetric_reldefT:  \<open>symmetric R = R\<^sup>\<smile> \<subseteq>\<^sup>r R\<close> unfolding symmetric_defT2 rel_defs func_defs comb_defs ..
lemma \<open>symmetric R = (\<forall>a b. R a b \<rightarrow> R b a)\<close> unfolding symmetric_def2 rel_defs func_defs comb_defs ..

lemma "symmetricInterior R = \<Union>\<^sup>r(\<lambda>T. T \<subseteq>\<^sup>r R \<and> symmetric T)" \<comment> \<open>proof by external provers\<close> oops (*TODO: reconstruct proof*)
lemma "symmetricClosure R  = \<Inter>\<^sup>r(\<lambda>T. R \<subseteq>\<^sup>r T \<and> symmetric T)" \<comment> \<open>proof by external provers\<close> oops (*TODO: reconstruct proof*)

lemma "symmetric R\<^sup>\<midarrow> = symmetric R" unfolding endorel_defs rel_defs func_defs comb_defs by metis

text \<open>All symmetric relations arise via their interior or closure operator.\<close>
lemma symmetric_def3:  "symmetric = range symmetricInterior" 
  unfolding symmetric_def2 endorel_defs rel_defs func_defs comb_defs by blast
lemma symmetric_defT3: "symmetric = range symmetricClosure" 
  unfolding symmetric_def2 endorel_defs rel_defs func_defs comb_defs by blast

text \<open>The following operation takes a relation R and returns its "strict" part, which is always an 
  asymmetric sub-relation (though not a maximal one in general).\<close>
definition asymmetricContraction::"ERel('a) \<Rightarrow> ERel('a)" ("(_)\<^sup>#")
  where "asymmetricContraction \<equiv> \<^bold>S (\<inter>\<^sup>r) \<sim>"
text \<open>Analogously, this extends a relation R towards a connected super-relation (not minimal in general).\<close>
definition connectedExpansion::"ERel('a) \<Rightarrow> ERel('a)" ("(_)\<^sup>\<flat>")
  where "connectedExpansion \<equiv> \<^bold>S (\<union>\<^sup>r) \<sim>"

declare asymmetricContraction_def[endorel_defs] connectedExpansion_def[endorel_defs]

lemma "R\<^sup># = R \<inter>\<^sup>r (R\<^sup>\<sim>)" unfolding endorel_defs rel_defs comb_defs ..
lemma "R\<^sup># = (\<lambda>a b. R a b \<and> \<not>R b a)" unfolding endorel_defs rel_defs func_defs comb_defs ..
lemma "R\<^sup>\<flat> = R \<union>\<^sup>r (R\<^sup>\<sim>)" unfolding endorel_defs rel_defs comb_defs ..
lemma "R\<^sup>\<flat> = (\<lambda>a b. R a b \<or> \<not>R b a)" unfolding endorel_defs rel_defs func_defs comb_defs ..


definition asymmetric::"Set(ERel('a))"
  where "asymmetric \<equiv> FP asymmetricContraction"
definition connected::"Set(ERel('a))"
  where \<open>connected \<equiv> FP connectedExpansion\<close>  \<comment> \<open>aka. "linear" or "total" in order theory\<close>

declare asymmetric_def[endorel_defs] connected_def[endorel_defs]

lemma asymmetric_def2:   \<open>asymmetric = \<^bold>S (\<subseteq>\<^sup>r) \<sim>\<close> unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma asymmetric_reldef: \<open>asymmetric R = R  \<subseteq>\<^sup>r R\<^sup>\<sim>\<close> unfolding asymmetric_def2 comb_defs ..
lemma "asymmetric R = (\<forall>a b. R a b \<rightarrow> \<not>R b a)" unfolding asymmetric_def2 rel_defs func_defs comb_defs ..

lemma connected_def2:   \<open>connected =  \<^bold>S (\<supseteq>\<^sup>r) \<sim>\<close> unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma connected_reldef:   \<open>connected R = R\<^sup>\<sim> \<subseteq>\<^sup>r R\<close> unfolding connected_def2 comb_defs rel_defs func_defs ..
lemma \<open>connected R = (\<forall>a b. \<not>R b a \<rightarrow> R a b)\<close> unfolding connected_def2 rel_defs func_defs comb_defs ..

lemma "connected R\<^sup>\<midarrow> = asymmetric R" unfolding connected_def2 asymmetric_def2 rel_defs func_defs comb_defs by auto
lemma "asymmetric R\<^sup>\<midarrow> = connected R" unfolding connected_def2 asymmetric_def2 rel_defs func_defs comb_defs by auto

text \<open>Connectedness resp. asymmetry entail reflexivity resp. irreflexivity.\<close>
lemma "connected R \<Longrightarrow> reflexive R" unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma "asymmetric R \<Longrightarrow> irreflexive R" unfolding endorel_defs rel_defs func_defs comb_defs by metis

lemma connected_def3:  "connected R = \<forall>\<^sup>2(symmetricClosure R)" unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma asymmetric_def3: "asymmetric R = \<nexists>\<^sup>2(symmetricInterior R)" unfolding endorel_defs rel_defs func_defs comb_defs by metis

text \<open>All asymmetric resp. connected relations arise via their corresponding interior resp. closure operator.\<close>
lemma asymmetric_def4: "asymmetric  = range asymmetricContraction" 
  unfolding asymmetric_def2 endorel_defs rel_defs func_defs comb_defs by blast
lemma connected_def4: "connected = range connectedExpansion" 
  unfolding connected_def2 endorel_defs rel_defs func_defs comb_defs by blast

text \<open>An alternative (more intuitive?) definition of connectedness.\<close>
lemma connected_def5: \<open>connected = \<^bold>S (\<squnion>\<^sup>r) \<smile>\<close> unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma connected_reldef5: \<open>connected R = R \<squnion>\<^sup>r R\<^sup>\<smile>\<close> unfolding connected_def5 comb_defs ..
lemma \<open>connected R = (\<forall>a b. R b a \<or> R a b)\<close> unfolding connected_reldef5 rel_defs func_defs comb_defs by auto

text \<open>The asymmetric-contraction and connected-expansion operators are duals wrt. relation-complement.\<close>
lemma "R\<^sup>\<flat>\<^sup>\<midarrow> = R\<^sup>\<midarrow>\<^sup>#" unfolding endorel_defs rel_defs func_defs comb_defs by simp
lemma "R\<^sup>#\<^sup>\<midarrow> = R\<^sup>\<midarrow>\<^sup>\<flat>" unfolding endorel_defs rel_defs func_defs comb_defs by simp


subsubsection \<open>Antisymmetry, Semiconnectedness, and co.\<close>

definition antisymmetric::"Set(ERel('a))"
  where "antisymmetric \<equiv> strongIdentity \<circ> symmetricInterior"
definition semiconnected::"Set(ERel('a))"
  where "semiconnected \<equiv> weakDifference \<circ> symmetricClosure"

declare antisymmetric_def[endorel_defs] semiconnected_def[endorel_defs]

lemma \<open>antisymmetric R = strongIdentity (symmetricInterior R)\<close> unfolding endorel_defs rel_defs comb_defs by auto
lemma \<open>antisymmetric R = symmetricInterior R \<subseteq>\<^sup>r \<Q>\<close> unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma antisymmetric_reldef: \<open>antisymmetric R = R \<inter>\<^sup>r (R\<^sup>\<smile>) \<subseteq>\<^sup>r \<Q>\<close> unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma \<open>antisymmetric R = (\<forall>a b. R a b \<and> R b a \<longrightarrow> a = b)\<close> unfolding antisymmetric_reldef rel_defs func_defs comb_defs ..

lemma \<open>semiconnected R = weakDifference (symmetricClosure R)\<close> unfolding endorel_defs rel_defs comb_defs by auto
lemma \<open>semiconnected R = \<D> \<subseteq>\<^sup>r symmetricClosure R\<close> unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma semiconnected_reldef: "semiconnected R = \<D> \<subseteq>\<^sup>r R \<union>\<^sup>r (R\<^sup>\<smile>)" unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma "semiconnected R = (\<forall>a b. a \<noteq> b \<rightarrow> R a b \<or> R b a)" unfolding semiconnected_reldef rel_defs func_defs comb_defs ..

text \<open>A relation is antisymmetric/semiconnected iff its complement is semiconnected/antisymmetric.\<close>
lemma antisymmetric_defN:  "antisymmetric R = semiconnected R\<^sup>\<midarrow>" unfolding antisymmetric_reldef semiconnected_reldef rel_defs func_defs comb_defs by auto
lemma semiconnected_defN:  "semiconnected R = antisymmetric R\<^sup>\<midarrow>" unfolding antisymmetric_reldef semiconnected_reldef rel_defs func_defs comb_defs by auto

lemma asymmetric_def5: "asymmetric R = (irreflexive R \<and> antisymmetric R)" unfolding endorel_defs rel_defs func_defs comb_defs by meson

text \<open>A relation is called (co)skeletal when its symmetric interior (closure) is the (dis)equality relation,
 inspired by category theory where categories are skeletal when isomorphic objects are identical.\<close>
definition skeletal::"Set(ERel('a))"
  where \<open>skeletal   \<equiv> (\<Q> \<Q>) \<circ> symmetricInterior\<close>  
definition coskeletal::"Set(ERel('a))"
  where \<open>coskeletal \<equiv> (\<Q> \<D>) \<circ> symmetricClosure\<close> 

declare skeletal_def[endorel_defs] coskeletal_def[endorel_defs]

lemma "skeletal   R = (\<Q> = symmetricInterior R)" unfolding endorel_defs comb_defs ..
lemma "coskeletal R = (\<D> = symmetricClosure R)" unfolding endorel_defs comb_defs ..

lemma "skeletal R = coskeletal R\<^sup>\<midarrow>" unfolding endorel_defs rel_defs func_defs comb_defs by (rule iffI, metis (mono_tags, lifting), (rule ext)+, metis)
lemma "coskeletal R = skeletal R\<^sup>\<midarrow>" unfolding endorel_defs rel_defs func_defs comb_defs by (rule iffI, (rule ext)+, metis, metis (mono_tags, lifting))

text \<open>Alternative definitions in terms of other relational properties.\<close>
lemma skeletal_def2:  "skeletal R = (antisymmetric R \<and> reflexive R)"
  using reflexive_si by (smt (verit, del_insts) B1_comb_def W21_comb_def antisymmetric_def reflexive_def reflexive_def2 skeletal_def subrel_antisym strongIdentity_def)
lemma coskeletal_def2:  "coskeletal R = (semiconnected R \<and> irreflexive R)" 
  using irreflexive_sc by (smt (verit, ccfv_threshold) B1_comb_def S11_comb_def W21_comb_def coskeletal_def irreflexive_def irreflexive_def2 semiconnected_reldef subrel_antisym symmetricClosure_def)



subsubsection \<open>Transitivity, Denseness, Quasitransitivity, and co.\<close>

text \<open>Every pair of elements x and y that can be connected by an element z in between are (un)related.\<close>
definition transitive::"Set(ERel('a))"
  where \<open>transitive \<equiv> \<^bold>S (\<supseteq>\<^sup>r) (\<^bold>W (\<circ>\<^sup>r))\<close>
definition antitransitive::"Set(ERel('a))"
  where \<open>antitransitive \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<supseteq>\<^sup>r) \<midarrow>\<^sup>r (\<^bold>W (\<circ>\<^sup>r))\<close>

declare transitive_def[endorel_defs] antitransitive_def[endorel_defs]

lemma transitive_reldef: \<open>transitive R = (R \<circ>\<^sup>r R) \<subseteq>\<^sup>r R\<close> unfolding endorel_defs rel_defs func_defs comb_defs ..
lemma antitransitive_reldef: \<open>antitransitive R = (R \<circ>\<^sup>r R) \<subseteq>\<^sup>r R\<^sup>\<midarrow>\<close> unfolding endorel_defs rel_defs func_defs comb_defs ..

text \<open>Alternative convenient definitions.\<close>
lemma transitive_def2: \<open>transitive R = (\<forall>a b c. R a c \<and> R c b \<rightarrow> R a b)\<close>
  unfolding transitive_def rel_defs func_defs comb_defs by auto
lemma antitransitive_def2: \<open>antitransitive R = (\<forall>a b c. R a c \<and> R c b \<rightarrow> \<not>R a b)\<close>
  unfolding antitransitive_def rel_defs func_defs comb_defs by auto

text \<open>Relationship between antitransitivity and irreflexivity.\<close>
lemma "antitransitive R \<Longrightarrow> irreflexive R" 
  unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma "leftUnique R \<or> rightUnique R \<Longrightarrow> antitransitive R = irreflexive R"
  unfolding endorel_defs rel_defs func_defs comb_defs by metis

text \<open>Every pair of (un)related elements x and y can be connected by an element z in between.\<close>
definition dense::"Set(ERel('a))"
  where \<open>dense \<equiv> \<^bold>S (\<subseteq>\<^sup>r) (\<^bold>W (\<circ>\<^sup>r))\<close>
definition pseudoClique::"Set(ERel('a))" \<comment> \<open>i.e. a graph with diameter 2 (where cliques have diameter 1)\<close>
  where \<open>pseudoClique \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<subseteq>\<^sup>r) \<midarrow>\<^sup>r (\<^bold>W (\<circ>\<^sup>r))\<close>

declare dense_def[endorel_defs] pseudoClique_def[endorel_defs]

lemma dense_reldef: \<open>dense R = R \<subseteq>\<^sup>r (R \<circ>\<^sup>r R)\<close> unfolding endorel_defs comb_defs ..
lemma pseudoClique_reldef: \<open>pseudoClique R = R\<^sup>\<midarrow> \<subseteq>\<^sup>r (R \<circ>\<^sup>r R)\<close> unfolding endorel_defs comb_defs ..

text \<open>The above properties are preserved by transposition:\<close>
lemma transitive_defT: "transitive R = transitive (R\<^sup>\<smile>)" unfolding endorel_defs rel_defs func_defs comb_defs by auto
lemma antitransitive_defT: "antitransitive R = antitransitive (R\<^sup>\<smile>)" unfolding endorel_defs rel_defs func_defs comb_defs by auto
lemma quasiDense_defT: "dense R = dense (R\<^sup>\<smile>)" unfolding endorel_defs rel_defs func_defs comb_defs by auto
lemma quasiClique_defT: "pseudoClique R = pseudoClique (R\<^sup>\<smile>)" unfolding endorel_defs rel_defs func_defs comb_defs by auto

text \<open>The above properties can be stated for the complemented relations in an analogous fashion.\<close>
lemma transitive_compl_reldef: \<open>transitive R\<^sup>\<midarrow> = R  \<subseteq>\<^sup>r (R \<bullet>\<^sup>r R)\<close> unfolding endorel_defs rel_defs func_defs comb_defs by auto
lemma dense_compl_reldef:     \<open>dense R\<^sup>\<midarrow> = (R \<bullet>\<^sup>r R) \<subseteq>\<^sup>r R\<close> unfolding endorel_defs rel_defs func_defs comb_defs by auto
lemma antitransitive_compl_reldef:  \<open>antitransitive R\<^sup>\<midarrow> = R\<^sup>\<midarrow> \<subseteq>\<^sup>r (R \<bullet>\<^sup>r R)\<close> unfolding endorel_defs rel_defs func_defs comb_defs by auto
lemma pseudoClique_compl_reldef: \<open>pseudoClique R\<^sup>\<midarrow> = (R \<bullet>\<^sup>r R) \<subseteq>\<^sup>r R\<^sup>\<midarrow>\<close> unfolding endorel_defs rel_defs func_defs comb_defs by auto

text \<open>We can provide alternative definitions for the above relational properties in terms of intervals.\<close>
lemma \<open>transitive R     = (\<forall>a b. \<exists>(R-interval a b) \<rightarrow> R a b)\<close>  unfolding endorel_defs rel_defs func_defs comb_defs ..
lemma \<open>antitransitive R = (\<forall>a b. \<exists>(R-interval a b) \<rightarrow> R\<^sup>\<midarrow> a b)\<close> unfolding endorel_defs rel_defs func_defs comb_defs ..
lemma \<open>dense R        = (\<forall>a b. R a b  \<rightarrow> \<exists>(R-interval a b))\<close> unfolding endorel_defs rel_defs func_defs comb_defs ..
lemma \<open>pseudoClique R = (\<forall>a b. R\<^sup>\<midarrow> a b \<rightarrow> \<exists>(R-interval a b))\<close> unfolding endorel_defs rel_defs func_defs comb_defs ..

text \<open>The following notions are often discussed in the literature (applied to strict relations/orderings).\<close>
abbreviation(input) \<open>quasiTransitive \<equiv> transitive \<circ> asymmetricContraction\<close>
abbreviation(input) \<open>quasiAntitransitive \<equiv> antitransitive \<circ> asymmetricContraction\<close>

lemma \<open>quasiTransitive R = (\<forall>a b. \<exists>(R\<^sup>#-interval a b) \<rightarrow> R\<^sup># a b)\<close>
  unfolding endorel_defs rel_defs func_defs comb_defs ..
lemma \<open>quasiAntitransitive R = (\<forall>a b. \<exists>(R\<^sup>#-interval a b) \<rightarrow> R\<^sup>#\<^sup>\<midarrow> a b)\<close>
  unfolding endorel_defs rel_defs func_defs comb_defs ..

text \<open>The "quasi" variants are weaker than their counterparts.\<close>
lemma "transitive R \<Longrightarrow> quasiTransitive R" unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma "antitransitive R \<Longrightarrow> quasiAntitransitive R" unfolding endorel_defs rel_defs func_defs comb_defs by metis
text \<open>However, both variants coincide under the right conditions.\<close>
lemma "antisymmetric R \<Longrightarrow> quasiTransitive R = transitive R" unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma "asymmetric R \<Longrightarrow> quasiAntitransitive R = antitransitive R" unfolding endorel_defs rel_defs func_defs comb_defs by metis

lemma quasiTransitive_defT: "quasiTransitive R = quasiTransitive (R\<^sup>\<smile>)" unfolding endorel_defs rel_defs func_defs comb_defs by auto
lemma quasiAntitransitive_defT: "quasiAntitransitive R = quasiAntitransitive (R\<^sup>\<smile>)" unfolding endorel_defs rel_defs func_defs comb_defs by auto

lemma quasitransitive_defN: "quasiTransitive R = quasiTransitive (R\<^sup>\<midarrow>)" unfolding endorel_defs rel_defs func_defs comb_defs by auto
lemma quasiintransitive_defN: "quasiAntitransitive R = quasiAntitransitive (R\<^sup>\<midarrow>)" unfolding endorel_defs rel_defs func_defs comb_defs by auto

text \<open>Symmetry entails both quasi-transitivity and quasi-antitransitivity.\<close>
lemma "symmetric R \<Longrightarrow> quasiTransitive R" unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma "symmetric R \<Longrightarrow> quasiAntitransitive R" unfolding endorel_defs rel_defs func_defs comb_defs by metis

text \<open>The property of transitivity is closed under arbitrary infima (i.e. it is a "closure system").\<close>
lemma "\<Inter>\<^sup>r-closed\<^sub>G transitive" 
  unfolding transitive_def2 endorel_defs rel_defs func_defs comb_defs by metis

text \<open>Natural ways to obtain transitive relations resp. preorders.\<close>
definition transitiveClosure::"ERel('a) \<Rightarrow> ERel('a)" ("_\<^sup>+")
  where "transitiveClosure \<equiv> \<Union>\<^sup>r \<circ> relPower"
definition preorderClosure::"ERel('a) \<Rightarrow> ERel('a)"  ("_\<^sup>*") \<comment> \<open>aka. reflexive-transitive closure\<close>
  where "preorderClosure \<equiv> \<Union>\<^sup>r \<circ> relPower0"

declare transitiveClosure_def [endorel_defs] preorderClosure_def [endorel_defs]

lemma "R\<^sup>+ = \<Union>\<^sup>r(relPower R)" unfolding endorel_defs comb_defs ..
lemma "R\<^sup>* = \<Union>\<^sup>r(relPower0 R)" unfolding endorel_defs comb_defs ..

lemma transitiveClosure_char: "R\<^sup>+ = \<Inter>\<^sup>r(\<lambda>T. transitive T \<and> R \<subseteq>\<^sup>r T)" \<comment> \<open>proof by external provers\<close>
  unfolding transitiveClosure_def relPower_def transitive_def2
  unfolding endorel_defs rel_defs func_defs comb_defs 
  apply (rule ext)+ apply (rule iffI) oops (*TODO: prove*)

lemma "R\<^sup>* = reflexiveClosure (R\<^sup>+)" \<comment> \<open>proof by external provers\<close> oops (*TODO: prove*)


subsubsection \<open>Euclideanness and co.\<close>

text \<open>The relational properties of left-/right- euclideanness. \<close>
definition \<open>rightEuclidean \<equiv> \<^bold>S (\<supseteq>\<^sup>r) (\<^bold>S (\<circ>\<^sup>r) \<smile>)\<close>
definition \<open>leftEuclidean  \<equiv> \<^bold>S (\<supseteq>\<^sup>r) (\<^bold>\<Sigma> (\<circ>\<^sup>r) \<smile>)\<close>

lemma rightEuclidean_reldef: "rightEuclidean R = R \<circ>\<^sup>r (R\<^sup>\<smile>) \<subseteq>\<^sup>r R" unfolding rightEuclidean_def rel_defs func_defs comb_defs ..
lemma leftEuclidean_reldef:  "leftEuclidean  R = (R\<^sup>\<smile>) \<circ>\<^sup>r R \<subseteq>\<^sup>r R" unfolding leftEuclidean_def rel_defs func_defs comb_defs ..

declare rightEuclidean_def[endorel_defs] leftEuclidean_def[endorel_defs]

lemma "rightEuclidean R = (\<forall>a b. (\<exists>c. R c a \<and> R c b) \<rightarrow> R a b)" 
  unfolding endorel_defs rel_defs func_defs comb_defs ..
lemma "leftEuclidean R = (\<forall>a b. (\<exists>c. R a c \<and> R b c) \<rightarrow> R a b)" 
  unfolding endorel_defs rel_defs func_defs comb_defs ..

lemma "leftEuclidean R = rightEuclidean R\<^sup>\<smile>"
   unfolding endorel_defs rel_defs func_defs comb_defs by auto

lemma "symmetric R \<Longrightarrow> rightEuclidean R = leftEuclidean R"
  unfolding endorel_defs rel_defs func_defs comb_defs by meson

text \<open>Alternative convenient definitions.\<close>
lemma rightEuclidean_def2: \<open>rightEuclidean R = (\<forall>a b c. R c a \<and> R c b \<rightarrow> R a b)\<close>
  unfolding endorel_defs rel_defs func_defs comb_defs by blast
lemma leftEuclidean_def2: \<open>leftEuclidean R = (\<forall>a b c. R a c \<and> R b c \<rightarrow> R a b)\<close>
  unfolding endorel_defs rel_defs func_defs comb_defs by blast

text \<open>Some interrelationships.\<close>
lemma "leftEuclidean R \<Longrightarrow> quasiTransitive R" unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma "rightEuclidean R \<Longrightarrow> quasiTransitive R" unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma "connected R \<Longrightarrow> rightEuclidean R \<Longrightarrow> transitive R" unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma "connected R \<Longrightarrow> leftEuclidean R \<Longrightarrow> transitive R" unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma "symmetric R \<Longrightarrow> leftEuclidean R = transitive R" unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma "symmetric R \<Longrightarrow> rightEuclidean R = transitive R" unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma "reflexive R \<Longrightarrow> rightEuclidean R \<Longrightarrow> transitive R" unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma "reflexive R \<Longrightarrow> leftEuclidean R \<Longrightarrow> transitive R" unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma "leftEuclidean R \<Longrightarrow> leftUnique R = antisymmetric R" unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma "rightEuclidean R \<Longrightarrow> rightUnique R = antisymmetric R" unfolding endorel_defs rel_defs func_defs comb_defs by metis


subsubsection \<open>Equivalence, Equality and co.\<close>

text \<open>Equivalence relations are their own kernels (when seen as set-valued functions).\<close>
definition "equivalence \<equiv> FP kernel" 

lemma equivalence_reldef: "equivalence R = (R = R\<^sup>=)" 
  unfolding equivalence_def func_defs comb_defs ..

declare equivalence_def[endorel_defs]

lemma "equivalence R = (\<forall>a b. R a b = (R a = R b))"
  unfolding endorel_defs func_defs comb_defs by metis

text \<open>Alternative, traditional characterization in terms of other relational properties.\<close>
lemma equivalence_char: "equivalence R = (reflexive R \<and> transitive R \<and> symmetric R)"
  unfolding endorel_defs rel_defs func_defs comb_defs apply (rule iffI) apply metis apply (rule ext)+
  apply (rule iffI) apply (rule ext) apply metis by simp

text \<open>In fact, equality \<open>\<Q>\<close> is an equivalence relation (which means that \<open>\<Q>\<close> is identical to its own kernel).\<close>
lemma "equivalence \<Q>" 
  unfolding endorel_defs func_defs comb_defs by fastforce

text \<open>This gives a kind of recursive definition of equality (of which we can make a simplification rule).\<close>
lemma eq_kernel_simp: "\<Q>\<^sup>= = \<Q>" 
  unfolding endorel_defs func_defs comb_defs by fastforce

text \<open>Equality has other alternative definitions. We can also make simplification rules out of them:\<close>

text \<open>The intersection of all reflexive relations.\<close>
lemma eq_refl_simp: "\<Inter>\<^sup>r reflexive = \<Q>\<^sup>=" 
  unfolding biginterR_def2 reflexive_def2 func_defs comb_defs by (metis (mono_tags, opaque_lifting))

text \<open>Leibniz principle of identity of indiscernibles.\<close>
lemma eq_leibniz_simp1: "(\<lambda>a b. \<forall>P. P a \<leftrightarrow> P b) = \<Q>\<^sup>=" \<comment> \<open>symmetric version\<close>
  unfolding func_defs comb_defs by (metis (full_types))
lemma eq_leibniz_simp2: "(\<lambda>a b. \<forall>P. P a \<rightarrow> P b) = \<Q>\<^sup>=" \<comment> \<open>simplified version\<close>
  unfolding func_defs comb_defs by (metis (full_types))

text \<open>By extensionality, the above equation can be written as follows.\<close>
lemma eq_filt_simp1: "(\<lambda>a b. (\<lambda>k. k a) \<subseteq> (\<lambda>c. c b)) = \<Q>\<^sup>=" 
  unfolding func_defs comb_defs by (metis (full_types))

text \<open>Equality also corresponds to identity of generated principal filters.\<close>
lemma eq_filt_simp2: "(\<lambda>a b. (\<lambda>k::Set(Set('a)). k a) = (\<lambda>c. c b)) = \<Q>\<^sup>="
  unfolding func_defs comb_defs by (metis (full_types))
text \<open>Or, in terms of combinators\<close>
lemma eq_filt_simp3: "(\<^bold>T::'a \<Rightarrow> Set(Set('a)))\<^sup>= = \<Q>\<^sup>="
  unfolding func_defs comb_defs by (metis (full_types))

text \<open>Finally, note that:\<close>
lemma "(\<forall>y::'a \<Rightarrow> o. y a = y b) \<Longrightarrow> (\<forall>y::'a \<Rightarrow> 'b. y a = y b)" \<comment> \<open>external provers find a proof\<close> oops
proposition "(\<forall>y::'a \<Rightarrow> 'b. y a = y b) \<Longrightarrow> (\<forall>y::'a \<Rightarrow> o. y a = y b)" nitpick \<comment> \<open>counterexample found\<close> oops


subsubsection \<open>Orderings\<close>

definition "preorder R \<equiv> reflexive R \<and> transitive R"
definition "partial_order R \<equiv> preorder R \<and> antisymmetric R"

declare preorder_def [endorel_defs] partial_order_def [endorel_defs]

lemma preorder_def2: "preorder R = (\<forall>a b. R a b = (\<forall>x. R b x \<rightarrow> R a x))"
  unfolding preorder_def reflexive_def2 transitive_def2 comb_defs by auto

lemma partial_order_def2: "partial_order R = (skeletal R \<and> transitive R)"
  using partial_order_def preorder_def skeletal_def2 by blast

lemma reflexive_symm: "reflexive R\<^sup>\<smile> = reflexive R" unfolding reflexive_def2 rel_defs comb_defs ..
lemma transitive_symm: "transitive R\<^sup>\<smile> = transitive R" unfolding transitive_def2 rel_defs comb_defs by auto
lemma antisymmetric_symm: "antisymmetric R\<^sup>\<smile> = antisymmetric R" unfolding endorel_defs rel_defs func_defs comb_defs by meson
lemma skeletal_symm: "skeletal R\<^sup>\<smile> = skeletal R" unfolding skeletal_def2 by (simp add: antisymmetric_symm reflexive_symm)
lemma preorder_symm: "preorder R\<^sup>\<smile> = preorder R" by (simp add: preorder_def reflexive_symm transitive_symm)
lemma partial_order_symm: "partial_order R\<^sup>\<smile> = partial_order R" by (simp add: antisymmetric_symm partial_order_def preorder_symm)

text \<open>The subset and subrelation relations are partial orders.\<close>
lemma subset_partial_order: "partial_order (\<subseteq>)" 
  unfolding endorel_defs rel_defs func_defs comb_defs by fast
lemma subrel_partial_order: "partial_order (\<subseteq>\<^sup>r)"
  unfolding endorel_defs rel_defs func_defs comb_defs by fast

text \<open>Functional-power is a preorder.\<close>
lemma funPower_preorder: "preorder funPower" \<comment> \<open>proof by external provers\<close>
  unfolding partial_order_def preorder_def apply auto 
   apply (simp add: B1_comb_def I_comb_def W21_comb_def funPower_def2 reflexive_def4)
  oops (*TODO: prove*)

text \<open>Relational-power is a preorder\<close>
lemma relPower_preorder: "preorder relPower"
  unfolding partial_order_def preorder_def apply auto 
   apply (simp add: B1_comb_def W21_comb_def reflexive_def2 relPower_def2)
   unfolding transitive_def2 relPower_def2 by (metis (no_types, opaque_lifting) B2_comb_def relComp_assoc)
lemma relPower0_preorder: "preorder relPower0"
  unfolding partial_order_def preorder_def apply auto 
  apply (smt (verit, best) B1_comb_def W21_comb_def reflexive_def2 relComp_id2 relPower0_def2)
  unfolding transitive_def2 relPower0_def2 by (metis (no_types, opaque_lifting) B2_comb_def relComp_assoc relComp_id1)

text \<open>However, relational-power is not antisymmetric (and thus not partially ordered), because we have:\<close>
proposition "R = T \<circ>\<^sup>r T \<Longrightarrow> T = R \<circ>\<^sup>r R \<Longrightarrow> R = T" nitpick[card 'a=3] \<comment> \<open>countermodel found\<close> oops 


subsection \<open>Endorelation-based Set-Operations\<close>

text \<open>When talking about endorelations (orderings in particular) it is customary to employ the expressions
 "up" and "down" instead of "right" and "left" respectively. Similarly, we use expressions
 like "maximal/greatest" and "minimal/least" to mean "rightmost" and "leftmost" respectively.\<close>

text \<open>We conveniently introduce the following alternative names for left resp. right bounds/images\<close>
notation(input) leftBound ("lowerBound") and leftBound ("_-lowerBound")
            and rightBound ("upperBound") and rightBound ("_-upperBound")
            and leftImage ("downImage") and leftImage ("_-downImage")
            and rightImage ("upImage") and rightImage ("_-upImage")


subsubsection \<open>Least and Greatest Elements\<close>

text \<open>The set of least (leftmost) resp. greatest (rightmost) elements of a set wrt. an endorelation.\<close>
definition least::"ERel('a) \<Rightarrow> SetEOp('a)"
  where \<open>least \<equiv> (\<^bold>S (\<inter>)) \<circ> lowerBound\<close>
definition greatest::"ERel('a) \<Rightarrow> SetEOp('a)"
  where \<open>greatest \<equiv> (\<^bold>S (\<inter>)) \<circ> upperBound\<close>

notation(input) least ("_-least") and greatest ("_-greatest") (*convenient input notation*)

lemma "R-least A = (\<lambda>m. A m \<and> (\<forall>x. A x \<rightarrow> R m x))" unfolding least_def rel_defs func_defs comb_defs ..
lemma "R-greatest A = (\<lambda>m. A m \<and> (\<forall>x. A x \<rightarrow> R x m))" unfolding greatest_def rel_defs func_defs comb_defs ..

declare least_def[endorel_defs] greatest_def[endorel_defs]

lemma greatest_defT: \<open>R-greatest = R\<^sup>\<smile>-least\<close> unfolding endorel_defs rel_defs comb_defs ..
lemma least_defT: \<open>R-least = R\<^sup>\<smile>-greatest\<close> unfolding endorel_defs rel_defs comb_defs ..


subsubsection \<open>Maximal and Minimal Elements\<close>

text \<open>The set of minimal (resp. maximal) elements of a set A wrt. a relation R.\<close>
definition min::"ERel('a) \<Rightarrow> SetEOp('a)"
  where \<open>min \<equiv> least \<circ> connectedExpansion\<close>
definition max::"ERel('a) \<Rightarrow> SetEOp('a)"
  where \<open>max \<equiv> greatest \<circ> connectedExpansion\<close>

notation(input) min ("_-min") and  max ("_-max") (*convenient input notation*)

lemma "R-min A = (\<lambda>m. A m \<and> (\<forall>x. A x \<rightarrow> R\<^sup>\<flat> m x))" unfolding min_def endorel_defs rel_defs func_defs comb_defs ..
lemma "R-max A = (\<lambda>m. A m \<and> (\<forall>x. A x \<rightarrow> R\<^sup>\<flat> x m))" unfolding max_def endorel_defs rel_defs func_defs comb_defs ..

lemma \<open>R-min = (\<lambda>A. \<lambda>m. A m \<and> (\<forall>x. A x \<rightarrow> R x m \<rightarrow> R m x))\<close> unfolding min_def endorel_defs rel_defs func_defs comb_defs by auto
lemma \<open>R-max = (\<lambda>A. \<lambda>m. A m \<and> (\<forall>x. A x \<rightarrow> R m x \<rightarrow> R x m))\<close> unfolding max_def endorel_defs rel_defs func_defs comb_defs by auto

declare min_def[endorel_defs] max_def[endorel_defs]

lemma max_defT: \<open>R-max = R\<^sup>\<smile>-min\<close> unfolding endorel_defs rel_defs func_defs comb_defs ..
lemma min_defT: \<open>R-min = R\<^sup>\<smile>-max\<close> unfolding endorel_defs rel_defs func_defs comb_defs ..

text \<open>Minimal and maximal elements generalize least and greatest elements respectively.\<close>
lemma "R-least A \<subseteq> R-min A"
  unfolding endorel_defs rel_defs func_defs comb_defs by simp
lemma "R-greatest A \<subseteq> R-max A" 
  unfolding endorel_defs rel_defs func_defs comb_defs by simp


subsubsection \<open>Least Upper- and Greatest Lower-Bounds\<close>

text \<open>The (set of) least upper-bound(s) and greatest lower-bound(s) for a given set.\<close>
definition lub::"ERel('a) \<Rightarrow> SetEOp('a)"
  where "lub \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 \<^bold>B least upperBound"
definition glb::"ERel('a) \<Rightarrow> SetEOp('a)"
  where "glb \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 \<^bold>B greatest lowerBound"

notation(input) lub ("_-lub") and  glb ("_-glb") (*convenient input notation*)

lemma "R-lub =    (R-least) \<circ> (R-upperBound)" unfolding lub_def comb_defs ..
lemma "R-glb = (R-greatest) \<circ> (R-lowerBound)" unfolding glb_def endorel_defs comb_defs ..

declare lub_def[endorel_defs] glb_def[endorel_defs]

lemma lub_defT: "R-lub = R\<^sup>\<smile>-glb" 
  unfolding endorel_defs rel_defs func_defs comb_defs ..
lemma glb_defT: "R-glb = R\<^sup>\<smile>-lub" 
  unfolding endorel_defs rel_defs func_defs comb_defs ..

text \<open>Moreover, when it comes to upper/lower bounds, least/greatest and glb/lub elements coincide.\<close>
lemma lub_def3: "R-lub S = R-glb (R-upperBound S)"
  unfolding endorel_defs rel_defs func_defs comb_defs by auto
lemma glb_def3: "R-glb S = R-lub (R-lowerBound S)"
  unfolding endorel_defs rel_defs func_defs comb_defs by auto

lemma lub_prop: "S \<subseteq> R-lowerBound (R-lub S)" unfolding endorel_defs rel_defs func_defs comb_defs by simp
lemma glb_prop: "S \<subseteq> R-upperBound (R-glb S)" unfolding endorel_defs rel_defs func_defs comb_defs by simp

text \<open>Big-union resp. big-intersection of sets and relations corresponds in fact to the lub resp. glb.\<close>
lemma bigunion_lub: "(\<subseteq>)-lub S (\<Union>S)" unfolding endorel_defs rel_defs func_defs comb_defs by blast
lemma biginter_glb: "(\<subseteq>)-glb S (\<Inter>S)" unfolding endorel_defs rel_defs func_defs comb_defs by blast
lemma bigunionR_lub:"(\<subseteq>\<^sup>r)-lub S (\<Union>\<^sup>rS)" unfolding endorel_defs rel_defs func_defs comb_defs by blast
lemma biginterR_glb: "(\<subseteq>\<^sup>r)-glb S (\<Inter>\<^sup>rS)" unfolding endorel_defs rel_defs func_defs comb_defs by blast


subsection \<open>Existence and Uniqueness under Antisymmetry\<close>
text \<open>The following properties hold under the assumption that the given relation R is antisymmetric.\<close>

text \<open>There can be at most one least/greatest element in a set.\<close>
lemma antisymm_least_unique: "antisymmetric R \<Longrightarrow> unique(R-least S)" 
  unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma antisymm_greatest_unique: "antisymmetric R \<Longrightarrow> unique(R-greatest S)"
  unfolding endorel_defs rel_defs func_defs comb_defs by metis

text \<open>If (the) least/greatest elements exist then they are identical to (the) min/max elements.\<close>
lemma antisymm_least_min: "antisymmetric R \<Longrightarrow> \<exists>(R-least S) \<Longrightarrow> (R-least S) = (R-min S)" 
  unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma antisymm_greatest_max: "antisymmetric R \<Longrightarrow> \<exists>(R-greatest S) \<Longrightarrow> (R-greatest S) = (R-max S)"
  unfolding endorel_defs rel_defs func_defs comb_defs by metis

text \<open>If (the) least/greatest elements of a set exist then they are identical to (the) glb/lub.\<close>
lemma antisymm_least_glb: "antisymmetric R \<Longrightarrow> \<exists>(R-least S) \<Longrightarrow> (R-least S) = (R-glb S)"
  unfolding endorel_defs rel_defs func_defs comb_defs by metis
lemma antisymm_greatest_lub: "antisymmetric R \<Longrightarrow> \<exists>(R-greatest S) \<Longrightarrow> (R-greatest S) = (R-lub S)"
  unfolding endorel_defs rel_defs func_defs comb_defs by metis


subsection \<open>Further Properties of Endorelations\<close>

subsubsection \<open>Well-ordering and Well-foundedness\<close>

text \<open>The property of being a well-founded/ordered relation.\<close>
definition wellOrdered::"Set(ERel('a))" ("wellOrdered")
  where "wellOrdered \<equiv> ((\<subseteq>) \<exists>) \<circ> (\<^bold>B \<exists>) \<circ> least"
definition wellFounded::"Set(ERel('a))" ("wellFounded")
  where "wellFounded \<equiv> ((\<subseteq>) \<exists>) \<circ> (\<^bold>B \<exists>) \<circ> min"

declare wellFounded_def[endorel_defs] wellOrdered_def[endorel_defs]

lemma "wellOrdered R = (\<forall>D. \<exists>D \<rightarrow> \<exists>(R-least D))" unfolding endorel_defs func_defs comb_defs .. 
lemma "wellFounded R = (\<forall>D. \<exists>D \<rightarrow> \<exists>(R-min D))" unfolding endorel_defs func_defs comb_defs .. 

(*<*)
lemma "preorder R \<Longrightarrow> wellFounded R \<Longrightarrow> A \<subseteq> R-rightImage(R-min A)" oops (*TODO prove conjecture*)
(*>*)


subsubsection \<open>Limit-completeness\<close>
text \<open>Limit-completeness is an important property of endorelations (orderings in particular). Famously,
 this is the property that characterizes the ordering of real numbers (in contrast to the rationals).\<close>

text \<open>Note that existence of lubs for all sets entails existence of glbs for all sets (and viceversa).\<close>
lemma "\<forall>S. \<exists>(R-lub S) \<Longrightarrow> \<forall>S. \<exists>(R-glb S)" by (simp add: glb_def3)
lemma "\<forall>S. \<exists>(R-glb S) \<Longrightarrow> \<forall>S. \<exists>(R-lub S)" by (simp add: lub_def3)

text \<open>The above results motivate the following definition: An endorelation R is called limit-complete
 when lubs/glbs (wrt R) exist for every set S (note that they must not be necessarily contained in S).\<close>
definition limitComplete::"Set(ERel('a))"
  where "limitComplete \<equiv> \<forall> \<circ> (\<exists> \<circ>\<^sub>2 lub)" 

lemma "limitComplete R = (\<forall>S. \<exists>(R-lub S))" unfolding limitComplete_def comb_defs ..

proposition "limitComplete R \<Longrightarrow> (R-lub S) \<subseteq> S" nitpick \<comment> \<open>countermodel found\<close> oops

text \<open>Transpose/converse definitions.\<close>
lemma limitComplete_def2: "limitComplete =  \<forall> \<circ> (\<exists> \<circ>\<^sub>2 glb)" unfolding limitComplete_def comb_defs by (metis glb_def3 lub_def3)
lemma "limitComplete R = (\<forall>S. \<exists>(R-glb S))" unfolding limitComplete_def2 comb_defs ..

lemma limitComplete_defT: "limitComplete R\<^sup>\<smile> =  limitComplete R"
  unfolding limitComplete_def2 comb_defs by (metis glb_def3 lub_def3 lub_defT)

declare limitComplete_def[endorel_defs]

text \<open>The subset and subrelation relations are indeed limit-complete.\<close>
lemma subset_limitComplete: "limitComplete (\<subseteq>)" unfolding limitComplete_def comb_defs using bigunion_lub by blast
lemma subrel_limitComplete: "limitComplete (\<subseteq>\<^sup>r)" unfolding limitComplete_def comb_defs using bigunionR_lub by blast

end