theory tl
  imports "../../operators" "HOL-Eisbach.Eisbach"
begin

section \<open>Extended Tense Logic\<close>

text \<open>We start by implementing a custom prover for this theory (called "them" for "theory-method").
Current implementation is very brute! It consists of mindless definition-unfolding followed by
 invocation of ground HOL-provers (extensionality is applied in between, if no success at first).
 A decent implementation shall unfold definitions gradually and call custom methods at each layer.\<close>
method skip = (tactic \<open>all_tac\<close>)
method them = (unfold endorel_defs rel_defs func_defs comb_defs) ;
            (auto | skip) ; (fastforce | skip) ; (metis | skip) ;
            ((rule ext)+ | skip) ; (auto | fastforce | metis | smt)

(*Syntactic sugar for object-logical Boolean connectives*)
notation(input) compl ("\<^bold>\<not>") and inter (infixr "\<^bold>\<and>" 54) and union (infixr "\<^bold>\<or>" 53) and impl  (infixr "\<^bold>\<rightarrow>" 51)
notation(input) emptyset ("\<^bold>\<bottom>") and universe ("\<^bold>\<top>")  

(*We introduce the four basic tense modalities as notation for the left/right (dual) image operators*)
notation(input) leftImage ("\<^bold>\<F>") and rightImage ("\<^bold>\<P>") 
notation(input) leftDualImage ("\<^bold>\<G>") and rightDualImage ("\<^bold>\<H>") 

(*A will be the case (at some point) in the \<^bold>\<F>uture*)
lemma "\<^bold>\<F>(\<prec>) A = (\<lambda>t. \<exists>t'. t \<prec> t' \<and> A t')" for prec (infix "\<prec>" 99) by them
(*A was the case (at some point) in the \<^bold>\<P>ast*)
lemma "\<^bold>\<P>(\<prec>) A = (\<lambda>t. \<exists>t'. t' \<prec> t \<and> A t')" for prec (infix "\<prec>" 99) by them
(*A is always \<^bold>\<G>oing to be the case (in the future)*)
lemma "\<^bold>\<G>(\<prec>) A = (\<lambda>t. \<forall>t'. t \<prec> t' \<rightarrow> A t')" for prec (infix "\<prec>" 99) by them
(*A \<^bold>\<H>as always been the case (in the past)*)
lemma "\<^bold>\<H>(\<prec>) A = (\<lambda>t. \<forall>t'. t' \<prec> t \<rightarrow> A t')" for prec (infix "\<prec>" 99) by them

(*Additionally, we introduce the well-known binary "until" connective and its dual "release"*)
definition Until::"ERel('a) \<Rightarrow> SetEOp\<^sub>2('a)" ("\<^bold>\<U>")
  where "\<^bold>\<U>(\<prec>) \<equiv> \<lambda>A B. \<lambda>a. \<exists>b. a \<prec> b  \<and> interval (\<prec>) a b \<subseteq> A  \<and>  B b" for prec (infix "\<prec>" 99)
definition Release::"ERel('a) \<Rightarrow> SetEOp\<^sub>2('a)" ("\<^bold>\<R>")
  where "\<^bold>\<R>(\<prec>) \<equiv> \<lambda>A B. \<lambda>a. \<forall>b. a \<prec> b \<rightarrow> interval (\<prec>) a b \<subseteq> \<midarrow>A \<rightarrow> B b " for prec (infix "\<prec>" 99)

(*The "since" and "trigger" connectives are definable in terms of the converse (time) precedence relation.*)
abbreviation(input) Since ("\<^bold>\<S>") where "\<^bold>\<S> R \<equiv> \<^bold>\<U> R\<^sup>\<smile>"
abbreviation(input) Trigger ("\<^bold>\<T>") where "\<^bold>\<T> R \<equiv> \<^bold>\<R> R\<^sup>\<smile>"

declare Until_def[endorel_defs] Release_def[endorel_defs]

(*B will be the case and A is going to be the case until then *)
lemma "\<^bold>\<U>(\<prec>) A B = (\<lambda>t. \<exists>t''. t \<prec> t'' \<and>  B t'' \<and>  (\<forall>t'. t \<prec> t' \<and> t' \<prec> t'' \<rightarrow> A t'))" for prec (infix "\<prec>" 99) by them
(*TODO: paraphrase "release" *)
lemma "\<^bold>\<R>(\<prec>) A B = (\<lambda>t. \<forall>t''. t \<prec> t'' \<and> \<not>B t'' \<rightarrow> (\<exists>t'. t \<prec> t' \<and> t' \<prec> t'' \<and> A t'))" for prec (infix "\<prec>" 99) by them

(* Until and release are (de-Morgan-like) duals *)
lemma "\<midarrow>(\<^bold>\<R>(\<prec>) A B) = \<^bold>\<U>(\<prec>) (\<midarrow>A) (\<midarrow>B)" for prec (infix "\<prec>" 99) by them

(* All connectives are definable in therms of until (and release) as expected*)
lemma "\<^bold>\<F>(R) = \<^bold>\<U>(R) \<^bold>\<top>" by them
lemma "\<^bold>\<P>(R) = \<^bold>\<S>(R) \<^bold>\<top>" by them
lemma "\<^bold>\<G>(R) = \<^bold>\<R>(R) \<^bold>\<bottom>" by them
lemma "\<^bold>\<H>(R) = \<^bold>\<T> (R)\<^bold>\<bottom>" by them

end