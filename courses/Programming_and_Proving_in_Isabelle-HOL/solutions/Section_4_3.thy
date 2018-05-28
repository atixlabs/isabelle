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

lemma "(\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs)
     \<or> (\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs + 1)"
proof cases
  assume "even (length xs)"
  hence "length (take (length xs div 2) xs) = length xs div 2" by auto
  hence "length (drop (length xs div 2) xs) = length xs div 2"
proof -
  show ?thesis
    by (metis \<open>even (length xs)\<close> add_implies_diff dvd_mult_div_cancel length_drop mult_2)
qed 
next
  assume "\<not> even (length xs)"
  hence "length (take (length xs div 2) xs) = length xs div 2" by auto
  hence "length (drop (length xs div 2) xs) = (length xs div 2) + 1"
proof -
  have "2 * (length xs div 2) + 1 = length xs"
    by (meson \<open>odd (length xs)\<close> odd_two_times_div_two_succ)
  thus ?thesis by simp
qed
