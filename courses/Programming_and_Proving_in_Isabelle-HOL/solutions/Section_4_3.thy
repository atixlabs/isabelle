theory Section_4_3
imports Main
begin

(* Exercise 4.1 *)

lemma 
  assumes 
    T: "\<forall> x y. T x y \<or> T y x"
  and 
    A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
  and 
    TA: "\<forall> x y. T x y \<longrightarrow> A x y" 
  and 
    "A x y"
  shows "T x y"
proof cases
  assume "T x y"
  thus ?thesis by simp
next
  assume "\<not> T x y"
  hence "T y x" using T by blast 
  hence "A y x" using TA by simp
  hence "x = y" using `A x y` and A by simp
  thus ?thesis using `T y x` by simp  
qed


(* Exercise 4.2 *)

(* NOTE: The idea was to use the rule "(P \<Longrightarrow> A) \<Longrightarrow> (\<not>P \<Longrightarrow> B) \<Longrightarrow> (A \<or> B)" in order to prove the 
   lemma, since no natural deduction introduction rule was appropriate in this case (e.g. disjI1). 
   For this lemma, P = even (length xs). *)
lemma "(\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs)
     \<or> (\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs + 1)"
proof (cases "even (length xs)")
  case True
  assume e: "even (length xs)"
  have "length (take (length xs div 2) xs) = length xs div 2" by auto
  moreover have "length (drop (length xs div 2) xs) = length xs div 2" using e
    by (metis add_diff_cancel_right' dvd_mult_div_cancel length_drop mult_2)
  moreover have "xs = take (length xs div 2) xs @ drop (length xs div 2) xs" by simp
  moreover have "xs = take (length xs div 2) xs @ drop (length xs div 2) xs 
          \<and> length (take (length xs div 2) xs) = length (drop (length xs div 2) xs)"
    using calculation(1) calculation(2) calculation(3) by linarith 
  ultimately show ?thesis by blast
next
  case False
  assume o: "odd (length xs)"
  have "length (take (length xs div 2 + 1) xs) = length xs div 2 + 1" 
    by (metis (no_types, lifting) Divides.div_mult2_eq dvd_mult_div_cancel le_add2 left_add_mult_distrib length_take min.absorb2 mult_2 nat_1_add_1 o odd_two_times_div_two_succ one_add_one one_dvd) 
  moreover have "length (drop (length xs div 2 + 1) xs) = length xs div 2" using o
    by (metis (no_types, lifting) Suc_eq_plus1 add_Suc_right add_diff_cancel_right' length_drop mult_2 odd_two_times_div_two_succ)
  moreover have "xs = take (length xs div 2 + 1) xs @ drop (length xs div 2 + 1) xs" by simp
  moreover have "xs = take (length xs div 2 + 1) xs @ drop (length xs div 2 + 1) xs 
          \<and> length (take (length xs div 2 + 1) xs) = length (drop (length xs div 2 + 1) xs) + 1"
  using calculation(1) calculation(2) calculation(3) by linarith 
  ultimately show ?thesis by blast
qed
