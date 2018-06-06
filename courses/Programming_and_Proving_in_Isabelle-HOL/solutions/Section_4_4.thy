theory Section_4_4
imports Section_3_5
begin

(* Exercise 4.3 *)

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS : "ev n \<Longrightarrow> ev (n + 2)"

(* NOTE: For some reason the technique explained in Section 4.4.7 didn't work. The following code 
   hangs:

    lemma assumes a: "ev (Suc(Suc n))" shows "ev n"
    proof (induction "Suc (Suc m)" arbitrary: m rule: ev.induct)
    ...

  Therefore, I decided to use the other technique that reformulates the goal, that is, rewrites 
    ev (Suc(Suc n)) \<Longrightarrow> ev n
  as
    ev m \<Longrightarrow> m = Suc(Suc n) \<Longrightarrow> ev n
 *)
lemma 
  assumes "ev m" 
  shows "m = Suc(Suc n) \<Longrightarrow> ev n"
  using assms
proof (induction m arbitrary: n rule: ev.induct)
   case ev0
   then show ?case by (simp add: ev.ev0)
next
   case evSS
   then show ?case by (simp add: ev.evSS)
qed


(* Exercise 4.4 *)

lemma "\<not> ev (Suc (Suc (Suc 0)))" 
proof
  assume "ev (Suc (Suc (Suc 0)))" 
  from this show False
  proof cases 
    (* Case ev0 is impossible, so it's not proven. *)
    case evSS then show False using ev.cases by auto 
  qed
qed


(* Exercise 4.5 *)

lemma 
  assumes "iter r n x y" 
  shows "star r x y"
  using assms
proof (induction rule: iter.induct)
  case (iter_refl x)
  then show ?case by (simp add: refl)
next
  case (iter_step n x y z)
  (* NOTE: The key here is to use lemma star_flip_step from Exercise 3.3. *)
  then show ?case using iter_step.IH and iter_step.hyps(2) by (simp add: star_flip_step) 
qed


(* Exercise 4.6 *)

fun elems :: "'a list \<Rightarrow> 'a set" where
"elems []     = {}" |
"elems (x#xs) = {x} \<union> elems xs"

value "elems [(1::nat),2,3]" (* {1,2,3} *)

lemma "x \<in> elems xs \<Longrightarrow> \<exists> ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof (induction xs rule: elems.induct)
  case 1
  then show ?case by simp
next
  case (2 a as)
  then show ?case
  proof (cases "x = a")
    case True
    (* NOTE: The thesis holds for ys = [] and zs = as. *)
    then have "a # as = [] @ a # as \<and> a \<notin> elems []" by simp 
    then show ?thesis using `x = a` by blast 
  next
    case False
    then have "x \<in> elems as" using `x \<in> elems (a # as)` and `x \<noteq> a` by simp
    then have "\<exists>ys zs. as = ys @ x # zs \<and> x \<notin> elems ys" using "2.IH" by simp
    (* NOTE: The thesis holds for ys' = a # ys and zs' = zs. *)
    then obtain ys zs where "a # as = (a # ys) @ x # zs \<and> x \<notin> elems ys" by auto
    then show ?thesis using `x \<noteq> a` by fastforce 
  qed
qed


(* Exercise 4.7 *)

fun balanced :: "nat \<Rightarrow> alpha list \<Rightarrow> bool" where
"balanced 0       []     = True" |
"balanced n       (a#xs) = balanced (Suc n) xs" |
"balanced (Suc n) (b#xs) = balanced n xs" |
"balanced _        _     = False"

value "balanced 0 [] = True"
value "balanced 0 [a] = False"
value "balanced 0 [b] = False"
value "balanced 0 [a,a] = False"
value "balanced 0 [b,b] = False"
value "balanced 0 [b,a] = False"
value "balanced 0 [a,b] = True"
value "balanced 0 [a,a,b,b] = True"
value "balanced 0 [a,a,b] = False"
value "balanced 0 [b,b,a,a] = False"
value "balanced 0 [b,a,b,a] = False"
value "balanced 0 [a,b,a,b] = True"
value "balanced 0 [a,b,b,a] = False"
value "balanced 1 [b] = True"
value "balanced 1 [a,b] = False"
value "balanced 1 [b,b] = False"
value "balanced 1 [b,a,b] = True"
value "balanced 1 [a,a,b,b,b] = True"
value "balanced 1 [a,b,b] = True"
value "balanced 1 [a,b,a,b,b] = True"

(* NOTE: Required auxiliary lemmas *)

lemma S_ends_with_b: "S w \<Longrightarrow> w \<noteq> [] \<Longrightarrow> last w = b"
  by (metis S_imp_T T.cases append_is_Nil_conv last_append last_snoc) 

lemma balanced_inj: "balanced n w \<Longrightarrow> balanced m w \<Longrightarrow> n = m"
proof (induction w arbitrary: n m)
  case Nil
  then show ?case by (metis balanced.elims(2) list.distinct(1)) 
next
  case (Cons x xs)
  then show ?case 
  proof (cases x)
    case a
    then show ?thesis
      using Cons.IH Cons.prems(1) Cons.prems(2) balanced.simps(2) by blast 
  next
    case b
    then show ?thesis
      by (metis Cons.IH Cons.prems(1) Cons.prems(2) alpha.distinct(1) balanced.elims(2) list.distinct(1) list.inject) 
  qed
qed

lemma balanced_concat: "balanced n w \<Longrightarrow> balanced m v \<Longrightarrow> balanced (n + m) (w @ v)"
proof (induction w arbitrary: n m v)
  case Nil
  then show ?case using add_eq_if balanced_inj by auto
next
  case (Cons x xs)
  then show ?case
    by (metis add_eq_if append_Cons balanced.elims(2) balanced.simps(2) balanced.simps(3) diff_Suc_1 list.distinct(1) list.inject nat.simps(3))
qed

lemma balanced_append_closing: "balanced n w \<Longrightarrow> balanced (Suc n) (w @ [b])"
proof (induction w arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case 
    by (smt append_Cons balanced.elims(2) balanced.elims(3) balanced.simps(2) diff_Suc_1 list.inject list.sel(2) list.sel(3) nat.simps(3) not_Cons_self2) 
qed

(* TODO: Complete the proof. *)
lemma S_sneak_in: "S (replicate n a @ w) \<Longrightarrow> S (replicate (Suc n) a @ b # w)"
proof (induction "replicate n a @ w" arbitrary: n w rule: S.induct)
  case empS
  then show ?case using test2S' by auto 
next
  case (expS w')
  then show ?case sorry
next
  case (dupS w1 w2)
  then show ?case sorry
qed

(*
TODO: Prove this lemma. This should hold since given that "S w1" (i.e. w1 is balanced) and w1 is a prefix of 
"replicate n a @ w", then w1 should include "replicate n a" and the subsequent substring u such that 
"replicate n a @ u" is balanced. Graphically, 

   n times          w
  /-------\ /-------------\
  a a ... a x1 x2   ...  xm
            \------/
               u
  \----------------/  \----/
          w1            w2

*)
lemma S_replicate_prefix: "S w1 \<Longrightarrow> w1 @ w2 = replicate n a @ w \<Longrightarrow> (\<exists>u. w1 = replicate n a @ u \<and> w = u @ w2)" sorry


(* NOTE: Other auxiliary lemmas, just for fun :) *)

lemma cons_disbalance: "balanced n w \<Longrightarrow> \<not> balanced n (x#w)"
proof (induction w)
  case Nil
  then show ?case
    using balanced.elims(2) balanced.simps(4) by blast 
next
  case (Cons x xs)
  then show ?case
    by (metis (full_types) alpha.exhaust balanced.simps(2) balanced.simps(3) balanced_inj) 
qed

lemma balanced_starts_with_a: "w \<noteq> [] \<Longrightarrow> balanced 0 w \<Longrightarrow> hd w = a"
  by (metis balanced.elims(2) balanced.simps(1) balanced.simps(4) list.sel(1)) 

lemma balanced_ends_with_b: "w \<noteq> [] \<Longrightarrow> balanced n w \<Longrightarrow> last w = b" 
proof (induction w arbitrary: n)
  case Nil
  then show ?case by simp 
next
  case (Cons x xs)
  then show ?case by (smt balanced.elims(2) balanced.simps(4) last_ConsL last_ConsR list.sel(3)) 
qed


(* Main theorems *)

theorem "S (replicate n a @ w) \<Longrightarrow> balanced n w"
proof (induction "replicate n a @ w" arbitrary: n w rule: S.induct)
  case empS
  then show ?case by auto 
next
  case (expS w')
  then have "w \<noteq> []"
    by (metis S.expS S_ends_with_b alpha.distinct(1) append_Nil2 empty_replicate last_replicate list.distinct(1))  
  then have "(\<exists>v. w = v @ [b])"
    by (metis Nil_is_append_conv append_butlast_last_id expS.hyps(3) last.simps last_append last_snoc) 
  then have "(\<exists>v. a # w' @ [b] = replicate n a @ v @ [b])"
    by (simp add: expS.hyps(3))
  then have "(\<exists>v. w' @ [b] = replicate (n - 1) a @ v @ [b])"
    by (metis append_Cons append_Nil elems.cases list.sel(2) list.sel(3) tl_replicate)
  then have "(\<exists>v. w' = replicate (n - 1) a @ v)"
    by simp 
  then have "(\<exists>v. balanced (n - 1) v)"
    using expS.hyps(2) by blast
  then show ?case by (smt Suc_pred' \<open>\<exists>v. w' @ [b] = replicate (n - 1) a @ v @ [b]\<close> append_Cons append_self_conv2 balanced.simps(2) balanced_append_closing butlast_append butlast_snoc list.sel(2) local.expS(2) local.expS(3) not_gr_zero replicate_Suc replicate_empty same_append_eq snoc_eq_iff_butlast tl_replicate)
next
  case (dupS w1 w2)
  then have "(\<exists>u. w1 = replicate n a @ u \<and> w = u @ w2)" using S_replicate_prefix by auto 
  then have "(\<exists>u. balanced n u \<and> w = u @ w2)" using dupS.hyps(2) by blast 
  moreover have "w2 = replicate 0 a @ w2" by simp
  then have "balanced 0 w2" using dupS.hyps(4) by auto
  then have "balanced (n + 0) (u @ w2)" using S_replicate_prefix empS by fastforce 
  then show ?case using \<open>balanced 0 w2\<close> balanced_concat calculation by force  
qed

theorem "balanced n w \<Longrightarrow> S (replicate n a @ w)"
proof (induction w arbitrary: n)
  case Nil
  then show ?case
    by (metis S.simps balanced.elims(2) list.simps(3) replicate_empty) 
next
  case (Cons x xs)
  then show ?case
  proof (cases x)
    case a
    then have "balanced n (x # xs) = balanced n (a # xs)" by simp
    also have "... = balanced (Suc n) xs" by simp
    also have "... = S (replicate (Suc n) a @ xs)"
      using Cons.IH Cons.prems calculation by blast 
    finally show ?thesis
      by (metis Cons.prems a append_Cons replicate_Suc replicate_app_Cons_same) 
  next
    case b
    then have "balanced n (x # xs) = balanced n (b # xs)" by simp
    also have "... = balanced (n - 1) xs"
      by (metis Cons.prems Suc_pred' alpha.distinct(1) balanced.elims(2) balanced.simps(3) calculation list.inject list.simps(3) zero_less_Suc) 
    finally have "balanced n (x # xs) = S (replicate (n - 1) a @ xs)" using Cons.IH Cons.prems by auto 
    then show ?thesis
      by (metis Cons.prems S_sneak_in Suc_pred' b balanced.simps(5) not_gr_zero) 
  qed
qed

end
