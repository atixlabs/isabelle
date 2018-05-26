theory Section_3_5
imports Main
begin

(* Exercise 3.2 *)

inductive palindrome :: "'a list \<Rightarrow> bool" where
palEmpt: "palindrome []" |
palSing: "palindrome [x]" |
palStep: "palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])"

(* NOTE: Some sample tests of proofs using the inductive definition. *)
lemma test1: "palindrome []"
  apply (rule palEmpt)
  done

lemma test2: "palindrome [1]"
  apply (rule palSing)
  done

lemma test3: "palindrome (1 # [2] @ [1])"
  apply (rule palStep)
  apply (rule palSing)
  done

lemma test4: "palindrome (1 # [1] @ [1])"
  apply (rule palStep[OF palSing])
  done

theorem rev_pal_is_pal: "palindrome xs \<Longrightarrow> palindrome (rev xs)"
  apply (induction rule: palindrome.induct)
  apply (auto simp add: palindrome.intros)
  done


(* Exercise 3.3 *)

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma rel_imp_star: "r x y \<Longrightarrow> star r x y"
  apply (auto simp add: step refl)
  done

lemma star_flip_step: "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
  apply (induction rule: star.induct)
  apply (auto simp add: rel_imp_star star.step)
  done

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x" |
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

(* NOTE: The sledgehammer method suggested the "meson" method... What is that?  *)
lemma rel_imp_star': "r x y \<Longrightarrow> star' r x y"
  apply (meson step' refl')
  done

lemma star'_flip_step: "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
  apply (induction rule: star'.induct)
  apply (auto simp add: rel_imp_star' step')
  done

theorem star'_imp_star: "star' r x y \<Longrightarrow> star r x y"
  apply (induction rule: star'.induct)
  apply (auto simp add: refl star_flip_step)
  done

theorem star_imp_star': "star r x y \<Longrightarrow> star' r x y"
  apply (induction rule: star.induct)
  apply (auto simp add: refl' star'_imp_star star'_flip_step)
  done


(* Exercise 3.4 *)

(* FIXME: iter1 is not needed since it's itern[OF iter0] *)
inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
iter0: "iter r 0 x x" |
iter1: "r x y \<Longrightarrow> iter r (Suc 0) x y" |
itern: "iter r n x y \<Longrightarrow> r y z \<Longrightarrow> iter r (Suc n) x z"

(* NOTE: Some sample tests of proofs using the inductive definition. *)

(* 0 R^0 0  *)
lemma "iter r 0 0 0" 
  by (rule iter0)

(* 0 R^1 1  *)
lemma "r 0 1 \<and> r 1 2 \<Longrightarrow> iter r (Suc 0) 0 1" 
  by (rule iter1) auto

(* 0 R^1 2 *)
lemma "r 0 1 \<and> r 1 2 \<Longrightarrow> iter r (Suc (Suc 0)) 0 2" 
  by (rule itern [OF iter1]) auto

lemma iter_step: "iter r n y z \<Longrightarrow> r x y \<Longrightarrow> \<exists>n. iter r n x z"
  apply (induction rule: iter.induct)
  apply (auto intro: iter.intros)
  done

(* NOTE: The intended meaning of the claim is "x R^* y \<Longrightarrow> x R^n y for some n", more formally 
   "x R^* y \<Longrightarrow> (\<exists>n. x R^n y)". However in "star r x y \<Longrightarrow> iter r n x y", n is a free variable,
   so the correct claim is: "star r x y \<Longrightarrow> (\<exists>n. iter r n x y)". *)
theorem star_imp_iter: "star r x y \<Longrightarrow> (\<exists>n. iter r n x y)"
  apply (induction rule: star.induct)
  apply (auto simp add: iter_step intro: iter.intros)
  done


(* Exercise 3.5 *)

datatype alpha = a | b  (* | ... *)

(* Grammar 1 *)
inductive S :: "alpha list \<Rightarrow> bool" where
empS: "S []" |
expS: "S w \<Longrightarrow> S (a # w @ [b])" |
dupS: "S w \<Longrightarrow> S w' \<Longrightarrow> S (w @ w')"

(* \<epsilon> \<in> \<L>(S) *)
lemma "S []" by (rule empS)

(* ab \<in> \<L>(S) *)
lemma test2S: "S (a # [] @ [b])"
  apply (rule expS[OF empS])
  done

lemma test2S': "S [a,b]" (* A variant of test2S *)
 by (metis S.simps append_Nil)

(* abab \<in> \<L>(S) *)
lemma "S ((a # [] @ [b]) @ (a # [] @ [b]))"
  apply (rule dupS[OF test2S test2S])
  done

(* Grammar 2 *)
inductive T :: "alpha list \<Rightarrow> bool" where
empT: "T []" |
expT: "T w \<Longrightarrow> T w' \<Longrightarrow> T (w @ [a] @ w' @ [b])"

(* \<epsilon> \<in> \<L>(T) *)
lemma "T []" by (rule empT)

(* ab \<in> \<L>(T) *)
lemma test2T: "T ([] @ [a] @ [] @ [b])"
  apply (rule expT[OF empT empT])
  done

(* abab \<in> \<L>(T) *)
lemma "T ((([] @ [a] @ [] @ [b]) @ [a] @ [] @ [b]))"
  apply (rule expT[OF expT[OF empT empT] empT])
  done

theorem T_imp_S: "T w \<Longrightarrow> S w"
  apply (induction rule: T.induct)
  apply (auto intro: S.intros)
  done

(* Auxiliary lemma stating that T can simulate production S \<longrightarrow> aSb *)
lemma T_sim_expS: "T w \<Longrightarrow> T (a # w @ [b])"
  using empT expT by fastforce

(* Auxiliary lemma stating that T can simulate production S \<longrightarrow> SS *)
lemma T_sim_dupS: "T w \<Longrightarrow> T w' \<Longrightarrow> T (w' @ w)"  
  apply (induction rule: T.induct)
  apply fastforce
  by (metis T.simps append.assoc)

theorem S_imp_T: "S w \<Longrightarrow> T w"
  apply (induction rule: S.induct)
  apply (simp add: empT)
  apply (blast intro: T_sim_expS)
  by (simp add: T_sim_dupS)

end
