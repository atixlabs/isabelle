theory Section_4_3
imports Main
begin

(* Exercise 4.1 *)

lemma 
  assumes 
    T: "\<forall>x y. T x y \<or> T y x"
  and 
    A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
  and 
    TA: "\<forall>x y. T x y \<longrightarrow> A x y" 
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
