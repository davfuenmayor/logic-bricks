theory endorels_setops_mini (* A theory of endorelation-based set-operations *)
imports endorels_mini
begin

subsection \<open>Set operations from endorelations\<close>

subsubsection \<open>Least and greatest elements\<close>

(*The set of least resp. greatest elements of a set A wrt. a relation R*)
definition least::"ERel('a) \<Rightarrow> SetEOp('a)" ("_-least")
  where \<open>least \<equiv> (\<^bold>S(\<inter>)) \<circ> lowerBounds\<close>
definition greatest::"ERel('a) \<Rightarrow> SetEOp('a)" ("_-greatest")
  where \<open>greatest \<equiv> (\<^bold>S(\<inter>)) \<circ> upperBounds\<close>

lemma "R-least A = (\<lambda>m. A m \<and> (\<forall>x. A x \<longrightarrow> R m x))" unfolding least_def rel_defs set_defs comb_defs ..
lemma "R-greatest A = (\<lambda>m. A m \<and> (\<forall>x. A x \<longrightarrow> R x m))" unfolding greatest_def rel_defs set_defs comb_defs ..

declare least_def[endorel_defs] greatest_def[endorel_defs]

lemma greatest_defT: \<open>R-greatest = R\<^sup>t-least\<close> unfolding endorel_defs rel_defs comb_defs ..
lemma least_defT: \<open>R-least = R\<^sup>t-greatest\<close> unfolding endorel_defs rel_defs comb_defs ..


subsubsection \<open>Maximal and minimal elements\<close>

(*The set of minimal (resp. maximal) elements of a set A wrt. a relation R. *)
definition min::"ERel('a) \<Rightarrow> SetEOp('a)" ("_-min")
  where \<open>min \<equiv> least \<circ> lax\<close>
definition max::"ERel('a) \<Rightarrow> SetEOp('a)" ("_-max")
  where \<open>max \<equiv> greatest \<circ> lax\<close>

lemma "R-min A = (\<lambda>m. A m \<and> (\<forall>x. A x \<longrightarrow> R\<^sup>\<flat> m x))" unfolding min_def endorel_defs rel_defs set_defs comb_defs ..
lemma "R-max A = (\<lambda>m. A m \<and> (\<forall>x. A x \<longrightarrow> R\<^sup>\<flat> x m))" unfolding max_def endorel_defs rel_defs set_defs comb_defs ..

lemma \<open>R-min = (\<lambda>A. \<lambda>m. A m \<and> (\<forall>x. A x \<longrightarrow> R x m \<longrightarrow> R m x))\<close> unfolding min_def endorel_defs rel_defs set_defs comb_defs by auto
lemma \<open>R-max = (\<lambda>A. \<lambda>m. A m \<and> (\<forall>x. A x \<longrightarrow> R m x \<longrightarrow> R x m))\<close> unfolding max_def endorel_defs rel_defs set_defs comb_defs by auto

declare min_def[endorel_defs] max_def[endorel_defs]

lemma max_defT: \<open>R-max = R\<^sup>t-min\<close> unfolding endorel_defs rel_defs set_defs comb_defs ..
lemma min_defT: \<open>R-min = R\<^sup>t-max\<close> unfolding endorel_defs rel_defs set_defs comb_defs ..

(*Minimal and maximal elements generalize least and greatest elements respectively*)
lemma "R-least A \<subseteq> R-min A"
  unfolding endorel_defs rel_defs set_defs comb_defs by simp
lemma "R-greatest A \<subseteq> R-max A" 
  unfolding endorel_defs rel_defs set_defs comb_defs by simp


subsubsection \<open>Least-upper and greatest-lower bounds\<close>

(*The (set of) least upper-bound(s) and greatest lower-bound(s) for a given set*)
definition lub::"ERel('a) \<Rightarrow> SetEOp('a)" ("_-lub")
  where "lub \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<circ>) least upperBounds"
definition glb::"ERel('a) \<Rightarrow> SetEOp('a)" ("_-glb")
  where "glb \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<circ>) greatest lowerBounds"

lemma "R-lub S  = R-least(R-upperBounds S)" unfolding lub_def endorel_defs comb_defs ..
lemma "R-glb S  = R-greatest(R-lowerBounds S)" unfolding glb_def endorel_defs comb_defs ..

declare lub_def[endorel_defs] glb_def[endorel_defs]

lemma lub_defT: "R-lub = R\<^sup>t-glb" 
  unfolding endorel_defs rel_defs set_defs comb_defs ..
lemma glb_defT: "R-glb = (R)\<^sup>t-lub" 
  unfolding endorel_defs rel_defs set_defs comb_defs ..

(*Moreover, when it comes to upper/lower bounds, least/greatest and glb/lub elements coincide*)
lemma lub_def3: "R-lub S = R-glb (R-upperBounds S)"
  unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma glb_def3: "R-glb S = R-lub (R-lowerBounds S)"
  unfolding endorel_defs rel_defs set_defs comb_defs by auto

(*Join/meet are partial & nondeterministic binary operations, arising as a special case of lub/glb applied
 to unordered pairs. They are encoded as set-valued functions (e.g. returning empty-set when undefined).*)
abbreviation(input) join::"ERel('a) \<Rightarrow> Op\<^sub>2('a,Set('a))" ("_-join")
  where "R-join \<equiv> \<lambda>a b. R-lub{a,b}"
abbreviation(input) meet::"ERel('a) \<Rightarrow> Op\<^sub>2('a,Set('a))" ("_-meet")
  where "R-meet \<equiv> \<lambda>a b. R-glb{a,b}"


subsection \<open>Existence and uniqueness\<close>

(*There can be at most one least/greatest element in a set*)
lemma antisymm_least_unique: "antisymmetric R \<Longrightarrow> \<exists>\<^sub>\<le>\<^sub>1(R-least S)" 
  unfolding endorel_defs rel_defs set_defs comb_defs by simp
lemma antisymm_greatest_unique: "antisymmetric R \<Longrightarrow> \<exists>\<^sub>\<le>\<^sub>1(R-greatest S)"
  unfolding endorel_defs rel_defs set_defs comb_defs by simp

(* If (the) least/greatest elements exist then they are identical to (the) min/max elements*)
lemma antisymm_least_min: "antisymmetric R \<Longrightarrow> \<exists>(R-least S) \<longrightarrow> (R-least S) = (R-min S)" 
  unfolding endorel_defs rel_defs set_defs comb_defs by metis
lemma antisymm_greatest_max: "antisymmetric R \<Longrightarrow> \<exists>(R-greatest S) \<longrightarrow> (R-greatest S) = (R-max S)"
  unfolding endorel_defs rel_defs set_defs comb_defs by metis

(* If (the) least/greatest elements of a set exist then they are identical to (the) glb/lub *)
lemma antisymm_least_glb: "antisymmetric R \<Longrightarrow> \<exists>(R-least S) \<longrightarrow> R-least S = R-glb S"
  unfolding endorel_defs rel_defs set_defs comb_defs by metis
lemma antisymm_greatest_lub: "antisymmetric R \<Longrightarrow> \<exists>(R-greatest S) \<longrightarrow> R-greatest S = R-lub S"
  unfolding endorel_defs rel_defs set_defs comb_defs by metis

(*Existence of lub for all sets entails existence of glbs for all sets (and viceversa)*)
lemma "\<forall>S. \<exists>(R-lub S) \<Longrightarrow> \<forall>S. \<exists>(R-glb S)" 
  by (simp add: glb_def3)
lemma "\<forall>S. \<exists>(R-glb S) \<Longrightarrow> \<forall>S. \<exists>(R-lub S)"
  by (simp add: lub_def3)

(*In fact, the above results motivate the following definition: A relation R is called limit-complete
 when lubs/glbs (wrt R) exist for every set S (yet they are not necessarily contained in S)*)
definition limitComplete::"ERel('a) \<Rightarrow> o" ("limitComplete")
  where "limitComplete \<equiv> \<forall> \<circ> (\<exists> \<circ>\<^sub>2 lub)" 

lemma "limitComplete R = (\<forall>S. \<exists>(R-lub S))" unfolding limitComplete_def comb_defs ..

declare limitComplete_def[endorel_defs] 

lemma limitComplete_defT: "limitComplete = (\<lambda>R. \<forall>S. \<exists>(R-glb S))"
  unfolding limitComplete_def comb_defs by (metis glb_def3 lub_def3)


subsection \<open>Well-foundedness & co.\<close>

(*Well-foundedness of a set wrt. a given relation (as in "N is well-founded wrt. < ")*)
definition wellfounded::"ERel('a) \<Rightarrow> Set('a) \<Rightarrow> o" ("_-wellfounded")
  where "wellfounded \<equiv> \<^bold>B\<^sub>2\<^sub>1\<^sub>1 (\<supseteq>) (\<exists> \<circ>\<^sub>2 min) (((\<inter>) \<exists>) \<circ> (\<supseteq>))" (*TODO: simplify?*)
definition wellordered::"ERel('a) \<Rightarrow> Set('a) \<Rightarrow> o" ("_-wellordered")
  where "wellordered \<equiv> \<^bold>B\<^sub>2\<^sub>1\<^sub>1 (\<supseteq>) (\<exists> \<circ>\<^sub>2 least) (((\<inter>) \<exists>) \<circ> (\<supseteq>))" (*TODO: simplify?*) 

declare wellfounded_def[endorel_defs] wellordered_def[endorel_defs]

lemma "R-wellfounded S = (\<forall>D. D \<subseteq> S \<longrightarrow> \<exists>D \<longrightarrow> \<exists>(R-min D))" (*every non-empty S-subset has min elements (in D/S)*)
  unfolding endorel_defs rel_defs set_defs comb_defs by auto
lemma "R-wellordered S = (\<forall>D. D \<subseteq> S \<longrightarrow> \<exists>D \<longrightarrow> \<exists>(R-least D))" (*every non-empty S-subset has least elements (in D/S)*)
  unfolding endorel_defs rel_defs set_defs comb_defs by auto

lemma "(\<subseteq>)-wellfounded {{1::nat},{2},{1,2}}" 
  unfolding endorel_defs rel_defs endorel_defs set_defs comb_defs by (smt (verit, best))
lemma "\<not> (\<subseteq>)-wellordered {{1::nat},{2},{1,2}}" 
  unfolding endorel_defs rel_defs endorel_defs set_defs comb_defs apply simp oops (*TODO: this used to work with sledgehammer*)

abbreviation(input) wellfoundedRelation::"ERel('a) \<Rightarrow> o" ("wellfounded")
  where "wellfounded R \<equiv> R-wellfounded \<UU>"
abbreviation(input) wellorderedRelation::"ERel('a) \<Rightarrow> o" ("wellordered")
  where "wellordered R \<equiv> R-wellordered \<UU>"

lemma wellfoundedRel_def2: "wellfounded R = (\<forall>D. \<exists>D \<longrightarrow> \<exists>(R-min D))" 
  unfolding endorel_defs set_defs comb_defs by simp
lemma wellorderedRel_def2: "wellordered R = (\<forall>D. \<exists>D \<longrightarrow> \<exists>(R-least D))" 
  unfolding endorel_defs set_defs comb_defs by simp

end