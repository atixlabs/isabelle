theory Section_2_2
  imports Main
begin

(* Exercise 2.1 *)

value "1 + (2::nat)"  (* 3::nat *)
value "1 + (2::int)"  (* 3::int *)
value "1 - (2::nat)"  (* 0::nat *)
value "1 - (2::int)"  (* -1::int *)


(* Exercise 2.2 *)

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc (add m n)"

lemma add_02 [simp]: "add m 0 = m"
  apply (induction m)
  apply auto
  done

(* Auxiliary lemma: n + (m + 1) = (n + 1) + m *)
lemma add_03 [simp]: "add n (Suc m) = add (Suc n) m" (* "add (Suc n) m = add n (Suc m)" *)
  (* TODO: The order in which terms of equations in lemmata are written seems to matter! Why? *)
  (* Wolfgang's answer: The order of terms in equations matters when these equations are used as 
     simplification rules. Simplification only replaces the left side by the right side, never the
     other way round. This prevents the simplifier from going in circles. *)
  apply (induction n)
  apply auto
  done

theorem add_is_commutative: "add n m = add m n"
  apply (induction n)
  apply auto
  (* TODO: If lemma add_03 is written the other way, then "using add_03 by auto" would do the trick. 
           Why? *)
  (* Wolfgang's answer: `using add_03` adds `add_03` as another fact that the following proof method, 
     in this case `auto`, can use. As a result, `add_03` cannot be used as a simplification rule 
     only but also as a premise for classical logic reasoning and possibly more. *)
  done

theorem add_is_associative: "add i (add j k) = add (add i j) k"
  apply (induction i)
  apply auto
  done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc n) = Suc (Suc (double n))" (* i.e. 2 * (n + 1) = 2 * n + 2 *)

value "double 0" (* 0::nat *)
value "double 1" (* 2::nat *)
value "double 2" (* 4::nat *)

theorem double_is_add_twice: "double m = add m m"
  apply (induction m)
  apply auto
  done


(* Exercise 2.3 *)

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count _ [] = 0" |
(* NOTE: With the following definition it's more difficult to prove the theorem. Lesson learned: Try
   to keep function definitions as "simple" as possible (i.e. in a form in which applying the IH is 
   easier).
*)
(* NOTE: The modifier split : can be followed by multiple names. Splitting
if or case-expressions in the assumptions requires split : if_splits or split :
t .splits.The "more difficult" definition can be used if we add the unfolding rule for "let" in auto 
   (i.e. "apply (auto simp add: Let_def") *)
"count x (y # ys) = (
  let rest = count x ys 
  in (if x = y then Suc rest else rest))"
(* "count x (y # ys) = (if x = y then 1 else 0) + count x ys" *)

value "count 1 ([]::nat list)"      (* 0::nat *)
value "count 1 [0::nat]"            (* 0::nat *)
value "count 1 [0::nat, 1]"         (* 1::nat *)
value "count 1 [0::nat, 1, 2, 1]"   (* 2::nat *)

theorem count_leq_length: "count x xs \<le> length xs"
  apply (induction xs)
  apply (auto simp add: Let_def)
  done


(* Exercise 2.4 *)

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] y = [y]" |
"snoc (x # xs) y = x # snoc xs y"

value "snoc ([]::nat list) (1::nat)"  (* [1]::nat list  *)
value "snoc [1::nat] 2"               (* [1,2]::nat list *)
value "snoc [1::nat, 2] 3"            (* [1,2,3]::nat list *)

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x # xs) = snoc (reverse xs) x"

value "reverse ([]::nat list)"  (* []::nat list *)
value "reverse [1::nat]"        (* [1]::nat list *)
value "reverse [1::nat, 2, 3]"  (* [3,2,1]::nat list *)

(* While trying to prove the theorem "reverse_is_own_inverse" (see below), Isabelle stops with the 
   goal "\<And>a xs. reverse (reverse xs) = xs \<Longrightarrow> reverse (snoc (reverse xs) a) = a # xs". Since I need
   the consequent to include "reverse (reverse xs)" in order to apply the IH, the following 
   auxiliary lemma is proven. Using this lemma, Isabelle is able to proceed this way: 
     reverse (snoc (reverse xs) a
      = (lemma "reverse_01")
        a # (reverse (reverse xs))
      = (IH)
        a # xs
*)
lemma reverse_01 [simp]: "reverse (snoc xs x) = x # reverse xs"
  apply (induction xs)
  apply auto
  done

theorem reverse_is_own_inverse: "reverse (reverse xs) = xs"
  apply (induction xs)
  apply auto
  done


(* Exercise 2.5 *)

fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto (Suc n) = sum_upto n + Suc n"

value "sum_upto 0" (* 0::nat *)
value "sum_upto 1" (* 1::nat *)
value "sum_upto 4" (* 10::nat *)

theorem sum_upto_01: "sum_upto n = n * (n + 1) div 2"
  apply (induction n)
  apply auto
  done

end
