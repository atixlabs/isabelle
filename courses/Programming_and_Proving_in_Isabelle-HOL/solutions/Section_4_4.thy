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

lemma balanced_concat: "balanced n w \<Longrightarrow> balanced m v \<Longrightarrow> balanced (n + m) (w @ v)"
proof (induction w arbitrary: n m v)
  case Nil
  then show ?case by (metis add_eq_if append_Nil balanced.elims(2) list.distinct(1)) 
next
  case (Cons x xs)
  then show ?case
  proof (cases x)
    case a
    then have "balanced n (a # xs) = balanced (Suc n) xs" by simp
    then have "balanced (Suc (n + m)) (xs @ v)" using Cons.IH Cons.prems(1,2) a by fastforce  
    then have "balanced (n + m) (a # xs @ v)" using balanced.simps(2) by blast 
    then show ?thesis by (simp add: a) 
  next
    case b
    then have "balanced n (b # xs) = balanced (n - 1) xs" by (metis Cons.prems(1) One_nat_def Suc_pred balanced.simps(3,5) neq0_conv)  
    then have "balanced ((n - 1) + m) (xs @ v)" using Cons.IH Cons.prems(1,2) b by auto 
    then have "balanced (n + m) (b # xs @ v)" using Cons.prems(1) add_eq_if b by auto 
    then show ?thesis by (simp add: b) 
  qed
qed

lemma balanced_append_closing: "balanced n w \<Longrightarrow> balanced (Suc n) (w @ [b])"
proof (induction w arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case 
  proof (cases x)
    case a
    then have "balanced n (a # xs) = balanced (Suc n) xs" by simp
    then have "balanced (Suc (Suc n)) (xs @ [b])" using Cons.IH Cons.prems a by blast 
    then show ?thesis by (simp add: a) 
  next
    case b
    then have "balanced n (b # xs) = balanced (n - 1) xs" by (metis Cons.prems(1) One_nat_def Suc_pred balanced.simps(3,5) neq0_conv)
    then have "balanced (Suc (n - 1)) (xs @ [b])" using Cons.IH Cons.prems b by blast 
    then show ?thesis by (metis Cons.prems One_nat_def Suc_pred append_Cons b balanced.simps(3,5) neq0_conv)
  qed
qed

lemma S_sneak_in: "S (replicate n a @ w) \<Longrightarrow> S (replicate (Suc n) a @ b # w)"
proof (induction "replicate n a @ w" arbitrary: n w rule: S.induct)
  case empS
  then show ?case using test2S' by auto 
next
  case (expS w')
  then show ?case
  proof (cases n)
    case 0
    then have "a # w' @ [b] = w" 
      using expS.hyps(3) by simp 
    then have "S w" 
      using `S w'` and S.simps by blast
    moreover have "S [a, b]" 
      using test2S' by simp
    ultimately have "S ([a, b] @ w)" 
      using S.simps by blast
    then show ?thesis 
      using "0" by simp 
  next
    case (Suc n')
    then show ?thesis
    proof (cases "w' = []")
      case True
      then have "[a, b] = replicate n a @ w" 
        using expS.hyps(3) and Suc by simp
      then have "n = Suc 0 \<and> w = [b]"
        by (metis Suc alpha.distinct(1) append_Nil diff_Suc_1 last.simps length_replicate list.sel(3) list.size(3) nat.distinct(1) replicate_app_Cons_same tl_append2 tl_replicate) 
      then have "replicate (Suc n) a @ b # w = replicate (Suc (Suc 0)) a @ b # [b]" 
        by simp
      then have "replicate (Suc (Suc 0)) a @ b # [b] = [a, a, b, b]" 
        by simp
      then show ?thesis 
        using \<open>n = Suc 0 \<and> w = [b]\<close> and S.expS and test2S' by force      
    next
      case False
      then obtain v where split_w: "w = v @ [b]"
        by (metis Nil_is_append_conv alpha.distinct(1) append_butlast_last_id expS.hyps(3) last.simps last_append list.distinct(1) replicate_app_Cons_same) 
      then have "a # w' @ [b] = replicate n a @ v @ [b]" 
        using expS.hyps(3) by simp
      then have "w' @ [b] = replicate n' a @ v @ [b]"
        using Suc by auto 
      then have "S (replicate (Suc n') a @ b # v)"
        using expS.hyps(2) by simp
      then have "S (a # replicate (Suc n') a @ b # v @ [b])"
        using S.intros(2) by fastforce 
      then have "S (replicate (Suc n) a @ b # v @ [b])"
        using expS.hyps(3) and \<open>w' @ [b] = replicate n' a @ v @ [b]\<close> and Suc by simp   
      then show ?thesis 
        using split_w by simp
    qed
  qed
next
  case (dupS w1 w2)
  then show ?case
  proof (cases "n < length w1")
    case True
    then have "w1 = replicate n a @ take (length w1 - n) w" 
      using dupS.hyps(5) by (simp add: append_eq_conv_conj min.absorb2)
    then have "S (replicate (Suc n) a @ b # take (length w1 - n) w)"
      using dupS.hyps(2) by blast 
    moreover have "w2 = drop (length w1 - n) w" 
      using dupS.hyps(5) True by (simp add: append_eq_conv_conj)
    ultimately show ?thesis
      using S.dupS dupS.hyps(3) by force 
  next
    case False
    then have "w2 = replicate (n - length w1) a @ w"
      using dupS.hyps(5) by (simp add: append_eq_append_conv_if)
    then have "S (replicate (Suc (n - length w1)) a @ b # w)"
      using dupS.hyps(4) by blast 
    moreover have "w1 = replicate (length w1) a" 
      using dupS.hyps(5) False
      by (smt \<open>w2 = replicate (n - length w1) a @ w\<close> append.assoc append_same_eq length_append length_replicate replicate_add)
    ultimately show ?thesis  
      by (metis dupS.hyps(1) S_ends_with_b alpha.distinct(1) dupS.hyps(4) dupS.hyps(5) last_replicate length_0_conv self_append_conv2) 
  qed
qed


(* NOTE: Other auxiliary lemmas, just for fun :) *)

lemma "balanced n w \<Longrightarrow> balanced m w \<Longrightarrow> n = m"
proof (induction w arbitrary: n m)
  case Nil
  then show ?case by (metis balanced.elims(2) list.distinct(1)) 
next
  case (Cons x xs)
  then show ?case 
  proof (cases x)
    case a
    then have "balanced n (a # xs) = balanced (Suc n) xs" by simp
    moreover have "balanced m (a # xs) = balanced (Suc m) xs" by simp
    ultimately have "Suc n = Suc m" using Cons.IH Cons.prems(1,2) a by blast 
    then show ?thesis by auto
  next
    case b
    then have "balanced n (b # xs) = balanced (n - 1) xs" by (metis Cons.prems(1) One_nat_def Suc_pred balanced.simps(3,5) neq0_conv) 
    moreover have "balanced m (b # xs) = balanced (m - 1) xs" by (metis Cons.prems(2) One_nat_def Suc_pred b balanced.simps(3,5) neq0_conv) 
    ultimately have "n - 1 = m - 1" using Cons.IH Cons.prems(1) Cons.prems(2) b by blast 
    then show ?thesis by (metis Cons.prems(1,2) One_nat_def Suc_pred b balanced.simps(5) neq0_conv) 
  qed
qed

lemma "balanced n w \<Longrightarrow> \<not> balanced n (x # w)"
proof (induction w arbitrary: n)
  case Nil
  then show ?case
    using balanced.elims(2) balanced.simps(4) by blast 
next
  case (Cons x xs)
  then show ?case 
  proof (cases x)
    case a
    then have "balanced n (a # xs) = balanced (Suc n) xs" by simp
    then have "\<not> balanced (Suc n) (a # xs)" by (metis (full_types) Cons.IH Cons.prems a alpha.exhaust balanced.simps(2-3)) 
    then have "\<not> balanced n (a # a # xs)" by auto
    then show ?thesis by (metis (full_types) Cons.IH Cons.prems a alpha.exhaust balanced.simps(2,3,5) not0_implies_Suc)  
  next
    case b
    then have "balanced n (b # xs) = balanced (n - 1) xs" by (metis Cons.prems One_nat_def Suc_pred balanced.simps(3,5) neq0_conv) 
    then have "\<not> balanced (n - 1) (b # xs)" by (metis (full_types) Cons.IH Cons.prems alpha.exhaust b balanced.simps(2,3,5) not0_implies_Suc) 
    then have "\<not> balanced n (b # b # xs)" by (metis One_nat_def Suc_pred balanced.simps(3,5) neq0_conv) 
    then show ?thesis by (metis (full_types) Cons.IH Cons.prems alpha.exhaust b balanced.simps(2,3,5) not0_implies_Suc) 
  qed
qed

lemma "w \<noteq> [] \<Longrightarrow> balanced 0 w \<Longrightarrow> hd w = a"
  by (metis balanced.elims(2) balanced.simps(1) balanced.simps(4) list.sel(1)) 

lemma "w \<noteq> [] \<Longrightarrow> balanced n w \<Longrightarrow> last w = b" 
proof (induction w arbitrary: n)
  case Nil
  then show ?case by simp 
next
  case (Cons x xs)
  then show ?case 
  proof (cases x)
    case a
    then have "balanced n (a # xs) = balanced (Suc n) xs" by simp
    then have "last xs = b" using Cons.IH Cons.prems(2) a balanced.simps(4) by blast 
    then show ?thesis using Cons.prems(2) a by auto 
  next
    case b
    then show ?thesis
    proof (cases "xs = []")
      case True 
      then show ?thesis by (simp add: b) 
    next
      case False
      then have "balanced n (b # xs) = balanced (n - 1) xs" by (metis Cons.prems(2) One_nat_def Suc_pred b balanced.simps(3,5) neq0_conv) 
      then have "last xs = b" using Cons.IH Cons.prems(2) False b by blast 
      then show ?thesis by (simp add: False)
    qed
  qed
qed


(* Main theorems *)

(* TODO: Refactor using "obtain" (e.g. "obtain v where split_w: "w = v @ [b]") *)
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
  then show ?case 
  proof (cases "n < length w1")
    case True
    then have "w1 = replicate n a @ take (length w1 - n) w" 
      using dupS.hyps(5) by (simp add: append_eq_conv_conj min.absorb2)
    then have "balanced n (take (length w1 - n) w)"
      using dupS.hyps(2) by blast 
    moreover have "w2 = drop (length w1 - n) w" 
      using dupS.hyps(5) True by (simp add: append_eq_conv_conj)
    ultimately show ?thesis 
      using balanced_concat dupS.hyps(4) by fastforce 
  next
    case False
    then have "w2 = replicate (n - length w1) a @ w"
      using dupS.hyps(5) by (simp add: append_eq_append_conv_if)
    then have "balanced (n - length w1) w"
      using dupS.hyps(4) by blast 
    moreover have "w1 = replicate (length w1) a" 
      using dupS.hyps(5) False by (metis append_eq_append_conv_if drop_replicate leI length_replicate rev_replicate take_rev) 
    ultimately show ?thesis  
      using balanced_concat by (metis False append_Nil2 dupS.hyps(2) le_add_diff_inverse2 not_less) 
  qed  
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
