theory Distrib_Lattice
  imports Lattice
begin

locale distrib_lattice = lattice +
  assumes meet_distr: "x \<squnion> (y \<sqinter> z) = x \<squnion> y \<sqinter> x \<squnion> z"

lemma (in distrib_lattice) join_distr: "x \<sqinter> (y \<squnion> z) = x \<sqinter> y \<squnion> x \<sqinter> z" sorry

print_locale! distrib_lattice

end
