theory Section_3_2
  imports Main
begin

(* Exercise 3.1 *)

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
"set Tip          = {}" |
"set (Node l x r) = {x} \<union> set l \<union> set r"

value "set (Node (Node Tip (2::nat) Tip) 1 (Node Tip 3 (Node Tip 4 Tip)))" (* {2,1,3,4} *)

(* NOTE: "A la" Haskell ;)  *)
fun all :: "(int \<Rightarrow> bool) \<Rightarrow> int tree \<Rightarrow> bool" where
"all _ Tip          = True" |
"all p (Node l x r) = (p x \<and> all p l \<and> all p r)"  

fun ord :: "int tree \<Rightarrow> bool" where
"ord Tip          = True" |
(* NOTE: I will not use Max and Min since I would need to search for lemmas about them. *)
(* "ord (Node l x r) = (x = Max (set l \<union> {x}) \<and> x = Min (set r \<union> {x}) \<and> ord l \<and> ord r)" *)
"ord (Node l x r) = ((all (op > x) l) \<and> (all (op < x) r) \<and> ord l \<and> ord r)"

value "ord (Node (Node Tip 0 Tip) 1 (Node Tip 0 Tip))"
value "ord (Node (Node Tip 0 Tip) 1 (Node Tip 2 Tip))"

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
"ins x Tip          = Node Tip x Tip" |
"ins x (Node l y r) = (
  if x < y 
  then Node (ins x l) y r 
  else (
    if x > y  
    then Node l y (ins x r)
    else Node l y r))"

value "ins (-1) (ins 1 (ins 10 (ins 20 (ins 0 (ins 3 (ins 2 (ins 1 Tip)))))))"

(* Auxiliary lemma: If y is the greatest element in t and x < y then inserting x in t doesn't change that. *)
lemma all_01 [simp]: "x < y \<Longrightarrow> all (op > y) t \<Longrightarrow> all (op > y) (ins x t)"
  apply (induction t)
  apply auto
  done

(* Auxiliary lemma: If y is the least element in t and x > y then inserting x in t doesn't change that. *)
lemma all_02 [simp]: "x > y \<Longrightarrow> all (op < y) t \<Longrightarrow> all (op < y) (ins x t)"
  apply (induction t)
  apply auto
  done

(* Auxiliary lemma: ins inserts the given element. *)
lemma ins_inserts_element [simp]: "set (ins x t) = {x} \<union> set t"
  apply (induction t)
  apply auto
  done

(* Auxiliary lemma: ins preserves order. *)
lemma ins_preserves_order [simp]: "ord t \<longrightarrow> ord (ins x t)"
  apply (induction t)
  apply auto
  done

theorem ins_correctness: "set (ins x t) = {x} \<union> set t \<and> (ord t \<longrightarrow> ord (ins x t))"
  apply auto
  done

end
