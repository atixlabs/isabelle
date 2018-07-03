theory Total_Order
  imports Partial_Order3
begin

locale total_order = partial_order +
  assumes total: "x \<sqsubseteq> y \<or> y \<sqsubseteq> x"

lemma (in total_order) less_total: "x \<sqsubset> y \<or> x = y \<or> y \<sqsubset> x" sorry

print_locale! total_order

end
