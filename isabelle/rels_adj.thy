theory rels_adj
imports rels
begin

section \<open>Adjunctions & Dualities\<close>

subsection \<open>Dual\<close>

(*The dual of a set-operation. It gets a convenient superscript notation.*)
abbreviation(input) setopDual::"EOp(SetOp('a,'b))" ("_\<^sup>d") 
  where \<open>f\<^sup>d \<equiv> \<midarrow> \<circ> f \<circ> \<midarrow>\<close>
abbreviation(input) setopDual2::"EOp(SetOp\<^sub>2('a,'b))" ("_\<^sup>d") 
  where \<open>f\<^sup>d \<equiv> \<midarrow> \<circ>\<^sub>2 (\<^bold>\<Psi>\<^sub>2 f \<midarrow>)\<close>

(* Two set-operators (having the same type) can be said to be dual (wrt. set-complement).*)
abbreviation(input) Dual::"ERel(SetOp('a,'b))" ("DUAL")
  where "DUAL f g \<equiv> \<midarrow> \<circ> f  = g \<circ> \<midarrow>" (*beware polymorphism: (\<midarrow>) gets instantiated twice with different types*)
abbreviation(input) Dual2::"ERel(SetOp\<^sub>2('a,'b))" ("DUAL\<^sub>2")
  where "DUAL\<^sub>2 f g \<equiv> \<midarrow> \<circ>\<^sub>2 f  = \<^bold>\<Psi>\<^sub>2 g \<midarrow>" 

(*Of course*)
lemma "DUAL f f\<^sup>d"
  unfolding set_defs comb_defs by simp
lemma "DUAL\<^sub>2 f f\<^sup>d"
  unfolding set_defs comb_defs by simp


subsection \<open>Residuation\<close>

(*Two set-operators (having converse types) can be said to be (co)residuated (aka. (co)adjoint).*)
abbreviation(input) Residuation ::"Rel(SetOp('a,'b),SetOp('b,'a))" ("RESID")
  where "RESID f g \<equiv> \<forall>A B. f A \<subseteq> B \<longleftrightarrow> A \<subseteq> g B"
abbreviation(input) Coresiduation ::"Rel(SetOp('a,'b),SetOp('b,'a))" ("CORESID")
  where "CORESID f g \<equiv> \<forall>A B. B \<squnion> f A \<longleftrightarrow> g B \<bottom> A"

(*Residuation and co-residuation are related via complement*)
lemma "RESID f g \<longleftrightarrow> CORESID (f\<^sup>-) (g\<^sup>-)"
  unfolding rel_defs set_defs comb_defs by metis

(*The relation of being (co-)residuated is not symmetric.*)
lemma "RESID f g \<longleftrightarrow> RESID g f" nitpick oops (*counterexample*)
lemma "CORESID f g \<longleftrightarrow> CORESID g f" nitpick oops (*counterexample*)

(*In fact, reversed (co-)residuation corresponds to (co-)residuation of the duals*)
lemma "RESID f g \<longleftrightarrow> RESID (g\<^sup>d) (f\<^sup>d)" 
  unfolding rel_defs set_defs comb_defs apply auto sorry (*external provers can prove this (but internal ones don't)*)
lemma "CORESID f g \<longleftrightarrow> CORESID (g\<^sup>d) (f\<^sup>d)"
  unfolding rel_defs set_defs comb_defs apply auto sorry (*external provers can prove this (but internal ones don't)*)

(*Conveniently extend definitions to binary operations *)
abbreviation(input) Residuation2 ("RESID\<^sub>2")
  where "RESID\<^sub>2 f g \<equiv> \<forall>x. RESID (f x) (g x)"
abbreviation(input) CoResiduation2 ("CORESID\<^sub>2")
  where "CORESID\<^sub>2 f g \<equiv> \<forall>x. CORESID (f x) (g x)"

lemma "RESID\<^sub>2 f g \<longleftrightarrow> (\<forall>A B C. f C A \<subseteq> B \<longleftrightarrow> A \<subseteq> g C B)" by auto
lemma "CORESID\<^sub>2 f g \<longleftrightarrow> (\<forall>A B C. B \<squnion> f C A \<longleftrightarrow> g C B \<bottom> A)" by auto


subsection \<open>Galois Connections\<close>

(*Two set-operators (having converse types) can also be said to be Galois-adjoint (form a Galois connection).
 Dually, they can be said to be dual-Galois-adjoint (form a dual-Galois connection).*)
abbreviation(input) Galois::"Rel(SetOp('a,'b),SetOp('b,'a))" ("GALOIS")
  where  "GALOIS f g \<equiv> \<forall>A B. A \<subseteq> g B \<longleftrightarrow> B \<subseteq> f A"
abbreviation(input) DualGalois::"Rel(SetOp('a,'b),SetOp('b,'a))" ("DGALOIS")
  where "DGALOIS f g \<equiv> \<forall>A B. g B \<subseteq> A \<longleftrightarrow> f A \<subseteq> B"

(*Galois and dual-Galois connection are related via dual*)
lemma "GALOIS f g \<longleftrightarrow> DGALOIS (f\<^sup>d) (g\<^sup>d)"
  unfolding comb_defs set_defs apply auto sorry (*external provers can prove this (but internal ones don't)*)

(*The relation of being (dual-)Galois-adjoint is in fact symmetric.*)
lemma "GALOIS f g \<longleftrightarrow> GALOIS g f" by blast
lemma "DGALOIS f g \<longleftrightarrow> DGALOIS g f" by blast

(*Conveniently extend definitions to binary operations *)
abbreviation(input) Galois2 ("GALOIS\<^sub>2")
  where "GALOIS\<^sub>2 f g \<equiv> \<forall>x. GALOIS (f x) (g x)"
abbreviation(input) DualGalois2 ("DGALOIS\<^sub>2")
  where "DGALOIS\<^sub>2 f g \<equiv> \<forall>x. DGALOIS (f x) (g x)"

lemma "GALOIS\<^sub>2 f g \<longleftrightarrow> (\<forall>A B C. A \<subseteq> g C B \<longleftrightarrow> B \<subseteq> f C A)" by auto
lemma "DGALOIS\<^sub>2 f g \<longleftrightarrow> (\<forall>A B C. g C B \<subseteq> A \<longleftrightarrow> f C A \<subseteq> B)" by auto


subsection \<open>Conjugations\<close>

(*Two set-operators (having converse types) can be said to be (dual-)conjugated in two ways.*)
abbreviation(input) Conjugation::"Rel(SetOp('a,'b),SetOp('b,'a))" ("CONJ")
  where "CONJ f g  \<equiv> \<forall>A B. f A \<bottom> B \<longleftrightarrow> A \<bottom> g B"
abbreviation(input) DualConjugation::"Rel(SetOp('a,'b),SetOp('b,'a))" ("DCONJ")
  where "DCONJ f g \<equiv> \<forall>A B. f A \<squnion> B \<longleftrightarrow> A \<squnion> g B"

(*Conjugation and dual-conjugation are related via dual*)
lemma "CONJ f g \<longleftrightarrow> DCONJ (f\<^sup>d) (g\<^sup>d)"
  unfolding set_defs comb_defs apply auto sorry (*external provers can prove this (but internal ones don't)*)

(*The (dual-)conjugation relation is symmetric too.*)
lemma "CONJ f g \<longleftrightarrow> CONJ g f" unfolding set_defs comb_defs by fast
lemma "DCONJ f g \<longleftrightarrow> DCONJ g f" unfolding set_defs comb_defs by auto

(*Galois-connection and conjugation are related via complement *)
lemma "CONJ f g \<longleftrightarrow> GALOIS f\<^sup>- g\<^sup>-"
  unfolding set_defs comb_defs rel_defs by auto

(*Conveniently extend definitions to binary operations *)
abbreviation(input) Conjugation2 ("CONJ\<^sub>2")
  where "CONJ\<^sub>2 f g \<equiv> \<forall>x. CONJ (f x) (g x)"
abbreviation(input) DualConjugation2 ("DCONJ\<^sub>2")
  where "DCONJ\<^sub>2 f g \<equiv> \<forall>x. DCONJ (f x) (g x)"

lemma "CONJ\<^sub>2 f g \<longleftrightarrow> (\<forall>A B C. f C A \<bottom> B \<longleftrightarrow> A \<bottom> g C B)" by auto
lemma "DCONJ\<^sub>2 f g \<longleftrightarrow> (\<forall>A B C. f C A \<squnion> B \<longleftrightarrow> A \<squnion> g C B)" by auto

end