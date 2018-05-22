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



end
