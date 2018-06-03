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

(* NOTE: Auxiliary lemmas *)

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

lemma S_inj: "S (replicate n a @ w) \<Longrightarrow> S (replicate m a @ w) \<Longrightarrow> n = m"
proof (induction w arbitrary: n m)
  case Nil
  then have "n = 0" using S.empS
    by (smt Nil_is_append_conv S_imp_T T.cases alpha.distinct(1) last_append last_replicate last_snoc replicate_empty) 
  moreover have "m = 0" using S.empS
    by (smt Nil.prems(2) Nil_is_append_conv S_imp_T T.cases alpha.distinct(1) last_append last_replicate last_snoc replicate_empty) 
  finally show ?case by simp
next
  case (Cons x xs)
  then show ?case
  proof (cases x)
    case a
    then show ?thesis
      by (metis Cons_eq_appendI Suc_inject local.Cons(1) local.Cons(2) local.Cons(3) replicate_Suc replicate_app_Cons_same) 
  next
    case b then show ?thesis sorry (* TODO: Is this provable? *)
  qed
qed

lemma lem1: "balanced n w \<Longrightarrow> \<not> balanced n (x#w)"
proof (induction w)
  case Nil
  then show ?case
    using balanced.elims(2) balanced.simps(4) by blast 
next
  case (Cons x xs)
  then show ?case
    by (metis (full_types) alpha.exhaust balanced.simps(2) balanced.simps(3) balanced_inj) 
qed

lemma lem2: "S (replicate n a @ w) \<Longrightarrow> \<not> S (replicate n a @ (x#w))"
proof (induction w)
  case Nil
  then show ?case
    by (metis S_imp_T T.simps alpha.distinct(1) append_Cons append_assoc replicate_append_same snoc_eq_iff_butlast) 
next
  case (Cons x xs)
  then show ?case sorry (* TODO: Is this provable? *)
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

lemma S_starts_with_a: "S w \<Longrightarrow> w \<noteq> [] \<Longrightarrow> hd w = a" sorry (* TODO: Prove it (by rule inversion?) *)

lemma S_ends_with_b: "S w \<Longrightarrow> w \<noteq> [] \<Longrightarrow> last w = b"
  by (metis S_imp_T T.cases append_is_Nil_conv last_append last_snoc) 

lemma lem3: "length w = 1 \<Longrightarrow> \<not> balanced 0 w"
  by (metis One_nat_def Suc_length_conv balanced.simps(1) lem1 length_0_conv)

lemma lem4: "length w = 1 \<Longrightarrow> \<not> S w"
  by (metis One_nat_def S_ends_with_b S_starts_with_a Suc_length_conv balanced.simps(1) balanced.simps(2) balanced.simps(3) balanced.simps(4) last_ConsL length_0_conv list.sel(1))

lemma lem5: "length w > 1 \<Longrightarrow> (\<exists>w'. w = a # w' @ [b] \<and> balanced 0 w') \<Longrightarrow> balanced 0 w" sorry (* TODO: Prove it *)

lemma lem6: "length w > 1 \<Longrightarrow> balanced 0 w \<Longrightarrow> (\<exists>w'. w = a # w' @ [b])" sorry (* w' may not be balanced, e.g. [b,a] *)

lemma lem7: "balanced n w \<Longrightarrow> S (replicate (Suc n) a @ (w @ [b]))" sorry (* TODO: Prove it *)

lemma lem8: "S (replicate n a @ (w @ [b])) \<Longrightarrow> balanced n (w @ [b])" sorry (* TODO: Prove it *)

(* Main theorem *)

(* NOTE: A first attempt at proving the equality directly. *)
theorem bal_eq_S: "balanced n w = S (replicate n a @ w)"
proof (induction n arbitrary: w)
  case 0
  then show ?case
  proof (induction w)
    case Nil
    then show ?case using empS by simp
  next
    case (Cons x xs)
    then show ?case 
    proof (cases "balanced 0 xs")
      case True
      then show ?thesis using Cons.IH lem1 lem2 by blast 
    next
      case False
      then show ?thesis sorry (* TODO: Is this provable? *)
    qed
  qed
next
  case (Suc n)
  then show ?case
  proof (cases w)
    case Nil
    then show ?thesis
      by (metis Suc.IH append_Nil2 balanced.simps(2) replicate_Suc replicate_append_same) 
  next
    case (Cons x xs)
    then show ?thesis
      by (metis Suc.IH append_Cons balanced.simps(2) replicate_Suc replicate_app_Cons_same) 
  qed
qed

(* NOTE: An alternative strategy: Proving the double implication. *)
theorem bal_imp_S: "balanced 0 w \<Longrightarrow> S (replicate 0 a @ w)"
proof (induction w)
  case Nil
  then show ?case by (simp add: empS) 
next
  case (Cons x xs)
  then show ?case
  proof (cases "xs = []")
    case True
    then show ?thesis using Cons.prems lem1 by auto 
  next
    case False
    then show ?thesis sorry (* TODO: Is this provable? *)
  qed
qed

theorem "S (replicate n a @ w) \<Longrightarrow> balanced n w"
proof (induction "replicate n a @ w" arbitrary: w rule: S.induct)
case empS
  then show ?case
    by auto 
next
case (expS w)
then show ?case
  by (metis (no_types, lifting) Nil_is_append_conv S.expS alpha.distinct(1) append_butlast_last_id last.simps last_appendR lem8 list.distinct(1) replicate_app_Cons_same) 
next
  case (dupS w w')
then show ?case
  by (smt Cons_replicate_eq Nil_is_append_conv S.dupS S_ends_with_b alpha.distinct(1) append_Cons append_Nil append_butlast_last_id append_self_conv append_self_conv2 last.simps last_appendR last_snoc lem8 less_numeral_extra(3) replicate_app_Cons_same replicate_empty) 
qed

(* NOTE: Another version of bal_imp_S. *)
lemma 
  fixes n and w
  assumes "balanced n w"
  shows "S (replicate n a @ w)"
  using assms
proof (cases w)
  case Nil
  then show ?thesis
    by (metis append_Nil2 assms balanced.simps(1) balanced_inj empS replicate_empty) 
next
  case (Cons x xs)
  then show ?thesis 
  proof (cases xs)
    case Nil
    have "n = 1 \<and> x = b"
      by (smt One_nat_def alpha.exhaust assms balanced.elims(2) balanced.simps(1) balanced.simps(2) balanced.simps(4) balanced_inj lem1 list.sel(3) local.Cons local.Nil) 
    then show ?thesis
      by (simp add: local.Cons local.Nil test2S')
  next
    case (Cons y ys)
    then show ?thesis sorry (* TODO: Is this provable? *)
  qed
qed

end
