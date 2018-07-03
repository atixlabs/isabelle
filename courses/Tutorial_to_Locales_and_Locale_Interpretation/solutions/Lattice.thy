theory Lattice
  imports Partial_Order3
begin

locale lattice = partial_order +
  assumes ex_inf: "\<exists>inf. is_inf x y inf"
    and ex_sup: "\<exists>sup. is_sup x y sup"
begin

definition
  meet (infixl "\<sqinter>" 70) where "x \<sqinter> y = (THE inf. is_inf x y inf)"

definition
  join (infixl "\<squnion>" 65) where "x \<squnion> y = (THE sup. is_sup x y sup)"

lemma meet_left: "x \<squnion> y \<sqsubseteq> x" sorry

end

print_locale! lattice

end
