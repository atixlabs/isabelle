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
  apply (auto simp add: palEmpt palSing palStep)
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

theorem star'_star_equiv: "star' r x y \<Longrightarrow> star r x y"
  apply (induction rule: star'.induct)
  apply (auto simp add: refl star_flip_step)
  done

theorem star_star'_equiv: "star r x y \<Longrightarrow> star' r x y"
  apply (induction rule: star.induct)
  apply (auto simp add: refl' star'_star_equiv star'_flip_step)
  done

end
