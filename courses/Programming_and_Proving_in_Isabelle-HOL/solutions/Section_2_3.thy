theory Section_2_3
  imports Main
begin

(* Exercise 2.6 *)

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

(* NOTE: Traverses the tree in pre-order. *)
fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node l x r) = x # contents l @ contents r"

value "contents (Node (Node Tip 1 Tip) (2::nat) (Node Tip 1 Tip))" (* [2,1,1]::nat list *)

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node l x r) = x + sum_tree l + sum_tree r"

value "sum_tree (Node (Node Tip 1 Tip) (2::nat) (Node Tip 1 Tip))" (* 4::nat *)

lemma sum_tree_is_flatten_and_sum: "sum_tree t = sum_list (contents t)"
  apply (induction t)
  apply auto
  done


(* Exercise 2.7 *)

datatype 'a tree2 = Leaf 'a | Branch "'a tree2" 'a "'a tree2"

fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror (Leaf x) = Leaf x" |
"mirror (Branch l x r) = Branch (mirror r) x (mirror l)"

(* Result: Branch (Leaf 5) 4 (Branch (Leaf 2) 3 (Leaf 1))::nat tree2 *)
value "mirror (Branch (Branch (Leaf 1) 3 (Leaf 2)) 4 (Leaf (5::nat)))"

lemma mirror_twice_is_identity: "mirror (mirror t) = t"
  apply (induction t)
  apply auto
  done

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
"pre_order (Leaf x) = [x]" |
"pre_order (Branch l x r) = x # pre_order l @ pre_order r"

value "pre_order (Branch (Branch (Leaf 1) 3 (Leaf 2)) 4 (Leaf (5::nat)))" (* [4,3,1,2,5] *)

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
"post_order (Leaf x) = [x]" |
"post_order (Branch l x r) = post_order l @ post_order r @ [x]"

value "post_order (Branch (Branch (Leaf 1) 3 (Leaf 2)) 4 (Leaf (5::nat)))" (* [1,2,3,5,4] *)

lemma pre_post_orders: "pre_order (mirror t) = rev (post_order t)"
  apply (induction t)
  apply auto
  done


(* Exercise 2.8 *)

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse y [] = []" |
"intersperse y [x] = [x]" |
"intersperse y (x1 # x2 # xs) = x1 # y # intersperse y (x2 # xs)"

value "intersperse (0::nat) []" (* [] *)
value "intersperse (0::nat) [1]" (* [1] *)
value "intersperse (0::nat) [1,2,3,4]" (* [1,0,2,0,3,0,4] *)

lemma map_intersperse: "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs rule: intersperse.induct)
  apply auto
  done

end
