theory Section_4_3
imports Main
begin

lemma "(x::nat) = 0 \<longleftrightarrow> x + 1 = 1"
proof
  assume "x = 0"
  thus "x + 1 = 1" by simp
next
  assume "x + 1 = 1"
  thus "x = 0" by simp
qed

lemma "0 = 0 \<or> x = y"
proof cases
  assume "x = y"
  hence "0 = 0 \<or> True" by simp
  thus "0 = 0 \<or> x = y" by simp
next
  assume "x \<noteq> y"
  hence "0 = 0 \<or> False" by simp
  thus "0 = 0 \<or> x = y" by simp
qed

lemma "\<not>(x \<and> \<not> x)"
proof
  assume 0: "x \<and> \<not> x"
  from 0 have 1:  "x \<longrightarrow> x \<and> \<not>x" by simp
  from 0 have 2: "\<not>x \<longrightarrow> \<not>x \<and> \<not>\<not>x" by simp
  from 1 and 2 have "(x \<longrightarrow> False) \<and> (\<not>x \<longrightarrow> False)" by simp
  thus "False" by simp
qed

lemma "\<forall>x. (x::nat) + 1 > x"
proof
  fix x
  show "(x::nat) + 1 > x" by simp
qed

lemma "\<exists>n. (n::nat) + 1 = 1"
proof - 
  have "\<exists>n. (n::nat) + 1 = 1" by simp
  then obtain n where p: "(n::nat) + 1 = 1" by simp
  then show ?thesis by (rule exI) 
  (* show "(0::nat) + 1 = 1" by simp *) 
qed

lemma "A \<union> {} = A"
proof
  show "A \<union> {} \<subseteq> A"
  proof
    fix x
    assume "x \<in> A \<union> {}"
    hence "x \<in> A \<or> x \<in> {}" by simp
    thus "x \<in> A" by simp
  qed
next
  show "A \<subseteq> A \<union> {}"
  proof
    fix x
    assume "x \<in> A"
    hence "x \<in> A \<or> x \<in> {}" by simp
    thus "x \<in> A \<union> {}" by simp
  qed
qed

assume "surj f"
from this have "\<exists> a. {x . x \<notin> f x } = f a" by (auto simp: surj_def )
from this show "False" by blast
qed

proof
assume "surj f"
hence "\<exists> a. {x . x \<noteq> f x } = f a" by(auto simp: surj_def )
thus "False" by blast
qed






lemma
fixes f :: "'a \<Rightarrow> 'a set"
assumes s: "surj f"
shows "False"
proof - 
  have "\<exists> a. {x . x \<notin> f x} = f a" using s by (auto simp: surj_def)
	thus "False" by blast
qed

end
