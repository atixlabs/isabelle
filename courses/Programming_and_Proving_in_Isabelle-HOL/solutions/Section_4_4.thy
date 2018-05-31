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

lemma cons_disbalance:
  assumes "balanced n w = S (replicate n a @ w)"
  shows "balanced n (x#w) = S (replicate n a @ (x#w))" sorry

lemma "balanced n w = S (replicate n a @ w)"
proof (induction n arbitrary: w)
  case 0
  then show ?case
  proof (induction w)
    case Nil
    then show ?case using empS by simp
  next
    case (Cons x xs)
    then show ?case using cons_disbalance by simp
  qed
next
  case (Suc n)
  then show ?case
  proof (cases "w = []")
    case True
    then show ?thesis
      by (metis Suc.IH add.right_neutral add_Suc_right balanced.simps(2) replicate_0 replicate_Suc replicate_add) 
  next
    case False
    then show ?thesis
      by (metis Suc.IH append_Cons balanced.simps(2) replicate_Suc replicate_app_Cons_same) 
  qed
qed

end
