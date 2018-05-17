theory Section_2_5
  imports Main
begin

(* Exercise 2.10 *)

datatype tree0 = Tip | Node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Tip = 1" |
"nodes (Node l r) = 1 + nodes l + nodes r"

value "nodes (Node (Node Tip Tip) Tip)" (* 5 *)

(* NOTE: "explode n t" builds a complete tree0 of height n whose leaves are replaced by a copy of 
   t *)
fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

value "explode 0 Tip" (* Tip *)
value "explode 1 Tip" (* Node Tip Tip*)
value "explode 2 Tip" (* Node (Node Tip Tip) (Node Tip Tip) *)
value "explode 0 (Node Tip Tip)" (* Node Tip Tip *)
value "explode 1 (Node Tip Tip)" (* Node (Node Tip Tip) (Node Tip Tip) *)
value "nodes (explode 2 (Node Tip Tip))"

(* 
  NOTE: It is well known that a complete binary tree of height h has 2^(h+1)-1 nodes and 2^h 
   leaves. Therefore, "explode n t" will have 2^(n+1)-1 nodes (the nodes of the complete binary 
   tree that is built), minus 2^n (the leaves that will be "replaced by copies of t"), plus 
   2^n * nodes t (the number of nodes contained in the copies of t). That is, 

     2^(n+1)-1 - 2^n + 2^n * nodes t

  By arithmetic, this is equal to 2^n + 2^n * nodes t - 1, which in turn is equal to
  2^n * (1 + nodes t) - 1. 
*)

theorem explode_nodes: "nodes (explode n t) = 2^n * (1 + nodes t) - 1"
  apply (induction n arbitrary: t)
  apply (auto simp add: algebra_simps)
  done

(* Other interesting properties: *)

theorem nodes_01: "nodes (Node t t) = (nodes t) * 2 + 1"
  apply (induction t)
  apply auto
  done

theorem explode_01: "explode (n+1) t = Node (explode n t) (explode n t)"
  apply (induction n arbitrary: t)
  apply auto
  done

theorem explode_nodes_01: "nodes (explode (n+1) t) = 2 * (nodes (explode n t)) + 1"
  apply (induction n arbitrary: t)
  apply auto
  done

theorem explode_nodes_02: "nodes (explode n (Node t t)) = nodes (explode n t) * 2 + 1"
  apply (induction n arbitrary: t)
  apply auto
  done

corollary explode_nodes_tip: "nodes (explode n Tip) = 2^(n+1) - 1"
  apply (auto simp add: explode_nodes)
  done


(* Exercise 2.11 *)

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const n) _ = n" |
"eval (Add e e') x = eval e x + eval e' x" |
"eval (Mult e e') x = eval e x * eval e' x"

value "eval (Mult (Add Var (Const 1)) Var) 2" (* eval ((v + 1) * v) 2 = 6 *)

fun evalp' :: "nat \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> int" where
"evalp' _ [] _ = 0" |
"evalp' k (c#cs) x = (let term_val = c*x^k in term_val + evalp' (k+1) cs x)"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp cs x = evalp' 0 cs x"

value "evalp [4, 2, -1, 3] 2" (* 28 *)

(* TODO: I didn't search for something "à la Haskell" and implemented it myself from scratch. *)
fun add_coeffs :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"add_coeffs [] ys         = ys" |
"add_coeffs xs []         = xs" |
"add_coeffs (x#xs) (y#ys) = (x+y) # add_coeffs xs ys"

value "add_coeffs [1,2,3] [1,2,3,4,5]" (* [2,4,6,4,5] *)
value "add_coeffs [1,2,3,4,5] [1,2,3]" (* [2,4,6,4,5] *)
value "add_coeffs [1,2,3] [1,2,3]" (* [2,4,6] *)

fun add_index :: "int list \<Rightarrow> (nat \<times> int) list" where
"add_index l = zip [0..<length l] l"

value "add_index [1,2,3,4]" (* [(0,1), (1,2), (2,3), (3,4)] *)

fun list_max :: "nat list \<Rightarrow> nat" where
"list_max xs = fold max xs 0"

value "list_max [1,2,3,10,3]"

(* NOTE: The warning "The following clauses are redundant (covered by preceding clauses):" can be
   safely be ignored. *)
(*
fun mult_coeffs :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"mult_coeffs xs ys = 
  (let 
    xs' = add_index xs;
    ys' = add_index ys;
    zs  = [(i + j, x * y) . (i, x) \<leftarrow> xs', (j, y) \<leftarrow> ys'];
    n   = list_max [k. (k, _) \<leftarrow> zs];
    zs' = [(i, \<Sum> p \<leftarrow> [(j, _) \<leftarrow> zs . j = i] . snd p) . i \<leftarrow> [0..<n+1]]
  in map snd zs')"

value "mult_coeffs [1, 2, 1, 3]  [2, 0, 1]"
*)

fun pad_with_zero :: "nat \<Rightarrow> int list \<Rightarrow> int list" where
"pad_with_zero n xs = xs @ replicate (n - length xs) 0"

value "pad_with_zero 3 [1,2]"

(*
theorem pad_with_zero_spec: "(length (pad_with_zero n xs) = max (length xs) n) \<and> nths xs {0..max (length xs) n} = xs"
  apply (induction xs)
  apply (auto simp add: algebra_simps)
  done
*)

(* Assume length p = length q *)
fun conv :: "nat \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> int" where
"conv i p q = (\<Sum> j \<leftarrow> [0..<i+1] . p!j * q!(i-j))"

value "conv 3 [0,1,0,0] [0,0,1,0]"

(*
function mult_coeffs' :: "nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> int list" 
where
  "mult_coeffs' i N xs ys = (if i > N then [] else (conv i xs ys) # mult_coeffs' (i+1) N xs ys)"
by auto
termination
by (relation "measure (\<lambda>(i,N,_,_). N + 1 - i)") auto
*)

fun mult_coeffs' :: "nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> int list" where
(* TODO: Is "case" recommended instead of "if"? With "if" the simplifier seems to loop forever. *)
  -- "mult_coeffs' i N xs ys = (if i = 0 then [] else (conv (N-i) xs ys) # mult_coeffs' (i-1) N xs ys)"
  -- "mult_coeffs' i N xs ys = (case i of 0 \<Rightarrow> [] | Suc i' \<Rightarrow> (conv (N-i) xs ys) # mult_coeffs' i' N xs ys)"
"mult_coeffs' 0 _ _ _ = []" |
"mult_coeffs' (Suc i) N xs ys = (conv (N-Suc i) xs ys) # mult_coeffs' i N xs ys"

value "mult_coeffs' 3 3 (pad_with_zero 3 [0,1]) (pad_with_zero 3 [0,1])"

value "evalp' 0 (mult_coeffs' 3 3 (pad_with_zero 3 [0,1]) (pad_with_zero 3 [0,1])) 7 = evalp' 0 [0,1] 7 * evalp' 0 [0,1] 7" 

lemma 
  assumes "length xs > 0 \<and> length ys > 0"
  shows "evalp' 0 (mult_coeffs' (length xs + length ys - 1) (length xs + length ys - 1) (pad_with_zero (length xs + length ys - 1) xs) (pad_with_zero (length xs + length ys - 1) ys)) x = evalp' 0 xs x * evalp' 0 ys x"
  (* apply (auto simp add: algebra_simps simp add: nat.split) *)
  using assms by (induct xs ys rule: list_induct2') (simp_all add: algebra_simps add: nat.split)

fun mult_coeffs :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"mult_coeffs xs ys = 
  (let 
    n   = length xs + length ys - 1;
    xs' = pad_with_zero n xs;
    ys' = pad_with_zero n ys
   in
    mult_coeffs' n n xs' ys')
"

value "mult_coeffs [2] [2]" (* 2 * 2 = [4] = 4 *)
value "mult_coeffs [2] [0,1]" (* 2 * x = [0,2] = 2 x *)
value "mult_coeffs [0,1] [0,1]" (* x * x = [0,0,1] = x^2 *)
value "mult_coeffs [0,1] [0,0,1]" (* x * (x * x) = [0,0,0,1] = x^3 *)
value "mult_coeffs [1,1] [1,1]" (* (x+1) * (x+1) = [1,2,1] = 1 + 2x + x^2 *)

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var         = [0, 1]" | (* x *)
"coeffs (Const n)   = [n]" | (* n *)
"coeffs (Add e e')  = add_coeffs (coeffs e) (coeffs e')" |
"coeffs (Mult e e') = mult_coeffs (coeffs e) (coeffs e')"

(* x(x + 1) = [0,1,1] = x + x^2 *)
value "coeffs (Mult Var (Add Var (Const 1)))" 

(* (x + 1)(x + 1) = [1,2,1] = x + 2x + x^2 *)
value "coeffs (Mult (Add Var (Const 1)) (Add Var (Const 1)))"

(* 2x(x + 1) = [0,2,2] = 2x + 2x^2 *)
value "coeffs (Mult (Mult (Const 2) Var) (Add Var (Const 1)))" 

(* 5(x - 1)(x^2 + x + 1) = [-5,0,0,5]  = 5x^3 - 5 *)
value "coeffs (Mult (Const 5) (Mult (Add Var (Const (-1))) (Add (Add (Mult Var Var) Var) (Const 1))))" 

(* NOTE: I needed simultaneous induction here, had to Google a little bit to discover it. *)
lemma evalp'_add_coeffs [simp]: "evalp' n (add_coeffs cs1 cs2) x = evalp' n cs1 x + evalp' n cs2 x"
  apply (induction cs1 cs2 arbitrary: n rule: add_coeffs.induct)
  apply (auto simp add: algebra_simps)
  done

(*
lemma evalp'_mult_coeffs [simp]: "evalp' 0 (mult_coeffs cs1 cs2) x = evalp' 0 cs1 x * evalp' 0 cs2 x"
  apply (induction cs1 arbitrary: cs2)
  apply (auto simp add: Let_def algebra_simps)
  done
*)

lemma evalp'_mult_coeffs [simp]: "cs1 \<noteq> [] \<Longrightarrow> cs2 \<noteq> [] \<Longrightarrow> evalp' 0 (mult_coeffs cs1 cs2) x = evalp' 0 cs1 x * evalp' 0 cs2 x"
  (* apply (auto simp add: Let_def algebra_simps ) *)
  (* apply (auto simp add: Let_def) *)
  apply (induct cs1 arbitrary: cs2)
  apply (case_tac cs2, simp add: Let_def, force)
  apply (case_tac cs2, force, simp add: Let_def)
  done

value "evalp' 0 (add_coeffs [1,2,3] [1,2,3,4,5]) 7 = evalp' 0 [1,2,3] 7 + evalp' 0 [1,2,3,4,5] 7"
value "evalp' 0 (mult_coeffs [1,2,3] [1,2,3,4,5]) 7 = evalp' 0 [1,2,3] 7 * evalp' 0 [1,2,3,4,5] 7"

theorem coeffs_preserves_value: "evalp (coeffs e) x = eval e x"
  apply (induction e rule: exp.induct)
  apply (auto simp add: Let_def algebra_simps)
  done

lemma 
  assumes "\<And>x x1 x2a. evalp' 0
        (mult_coeffs' (length (coeffs x1) + length (coeffs x2a) - Suc 0) (length (coeffs x1) + length (coeffs x2a) - Suc 0)
          (coeffs x1 @ replicate (length (coeffs x2a) - Suc 0) 0) (coeffs x2a @ replicate (length (coeffs x1) - Suc 0) 0))
        x = evalp' 0 (coeffs x1) x * evalp' 0 (coeffs x2a) x"
  shows "evalp (coeffs e) x = eval e x"
  using assms by (induct e rule: exp.induct) (simp_all add: algebra_simps add: nat.split add: Let_def)

value "set [1::nat,1]"

end
