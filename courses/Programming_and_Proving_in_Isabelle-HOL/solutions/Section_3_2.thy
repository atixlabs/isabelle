theory Section_3_2
  imports Main
begin

(* Exercise 3.1 *)

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}" |
"set (Node l x r) = {x} \<union> set l \<union> set r"

value "set (Node (Node Tip (2::nat) Tip) 1 (Node Tip 3 (Node Tip 4 Tip)))" (* {2,1,3,4} *)

fun ord :: "int tree \<Rightarrow> bool" where
"ord Tip = True" |
"ord (Node l x r) = (x = Max (set l \<union> {x}) \<and> x = Min (set r \<union> {x}) \<and> ord l \<and> ord r)"

value "ord (Node (Node Tip 0 Tip) 1 (Node Tip 0 Tip))"

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
"ins x Tip = Node Tip x Tip" |
"ins x (Node l y r) = (
  if x < y 
  then Node (ins x l) y r 
  else (
    if x > y  
    then Node l y (ins x r)
    else Node l y r))"

value "ins 1 (ins 10 (ins 20 (ins 0 (ins 3 (ins 2 (ins 1 Tip))))))"

(*
lemma max_01: "x < y \<Longrightarrow> y = Max (set t \<union> {y}) \<Longrightarrow> y = Max (set (ins x t) \<union> {y})"
  apply (induction t rule: tree.induct)
  apply (auto simp add: algebra_simps)
  done
*)

lemma ins_02 [simp]: "set (ins x t) = {x} \<union> set t"
  apply (induction t rule: tree.induct)
  apply auto
  done

theorem ins_correctness: "set (ins x t) = {x} \<union> set t \<and> ord t \<Longrightarrow> ord (ins x t)"
  apply (induction t rule: tree.induct)
  apply auto
  done

lemma ins_01: "x = y \<Longrightarrow> set (ins x (Node l y r)) = {x} \<union> set (Node l y r) \<and> ord (Node l y r) \<Longrightarrow> ord (ins x (Node l y r))"
  apply auto
  done



end
