theory Partial_Order
  imports Main
begin

locale partial_order =
  fixes le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50)
  assumes refl [intro, simp]: "x \<sqsubseteq> x"
    and anti_sym [intro]: "\<lbrakk> x \<sqsubseteq> y; y \<sqsubseteq> x \<rbrakk> \<Longrightarrow> x = y"
		and trans [trans]: "\<lbrakk> x \<sqsubseteq> y; y \<sqsubseteq> z \<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"

thm partial_order_def
thm partial_order.trans

definition (in partial_order)
  less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubset>" 50)
  where "(x \<sqsubset> y) = (x \<sqsubseteq> y \<and> x \<noteq> y)"

thm partial_order.less_def

lemma (in partial_order) less_le_trans [trans]:
  "\<lbrakk> x \<sqsubset> y; y \<sqsubseteq> z \<rbrakk> \<Longrightarrow> x \<sqsubset> z"
  unfolding less_def by (blast intro: trans)

print_locale! partial_order

end
