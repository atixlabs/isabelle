theory Section_2_4
  imports Section_2_2
begin

(* Exercise 2.9 *)

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n  = n" |
"itadd (Suc m) n = itadd m (Suc n)"

value "itadd 0 3" (* 3 *)
value "itadd 3 0" (* 3 *)
value "itadd 3 2" (* 5 *)
value "itadd 2 3" (* 5 *)

lemma itadd_eq_add: "itadd m n = add m n"
  apply (induction m arbitrary: n)
  apply auto
  done

end
