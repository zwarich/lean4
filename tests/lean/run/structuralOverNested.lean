inductive Tree where | node : List Tree → Tree

mutual
def Tree.size : Tree → Nat
  | node ts => list_size ts

def Tree.list_size : List Tree → Nat
  | [] => 0
  | t::ts => t.size + list_size ts
end

example : Tree.list_size (t :: ts) = t.size + Tree.list_size ts := rfl

-- If we only look at the nested type at a finite depth we don't need an auxillary definition:

def Tree.isList : Tree → Bool
  | .node [] => true
  | .node [t] => t.isList
  | .node _ => false


-- A nested inductive type
-- the `Bool → RTree α` prevents well-founded recursion and
-- tests support for reflexive types

inductive RTree (α : Type u) : Type u
 | node : α → (Bool → RTree α) → List (RTree α) → RTree α

-- only recurse on the non-nested component
def RTree.simple_size : RTree α → Nat
  | .node _x t _ts => 1 + (t true).simple_size + (t false).simple_size

/--
info: theorem RTree.simple_size.eq_1.{u_1} : ∀ {α : Type u_1} (_x : α) (t : Bool → RTree α) (_ts : List (RTree α)),
  (RTree.node _x t _ts).simple_size = 1 + (t true).simple_size + (t false).simple_size :=
fun {α} _x t _ts => Eq.refl (RTree.node _x t _ts).simple_size
-/
#guard_msgs in
#print RTree.simple_size.eq_1

-- set_option trace.Elab.definition.structural true

-- also recurse on the nested components
#guard_msgs in
mutual
def RTree.size : RTree α → Nat
  | .node _ t ts => 1 + (t true).size + (t false).size + aux_size ts
def RTree.aux_size : List (RTree α) → Nat
  | [] => 0
  | t::ts => t.size + aux_size ts
end

/--
info: theorem RTree.aux_size.eq_2.{u_1} : ∀ {α : Type u_1} (t : RTree α) (ts : List (RTree α)),
  RTree.aux_size (t :: ts) = t.size + RTree.aux_size ts :=
fun {α} t ts => Eq.refl (RTree.aux_size (t :: ts))
-/
#guard_msgs in
#print RTree.aux_size.eq_2

mutual
def RTree.map (f : α → β) : RTree α → RTree β
  | .node x t ts => .node (f x) (fun b => (t b).map f) (map_aux f ts)
def RTree.map_aux (f : α → β) : List (RTree α) → List (RTree β)
  | [] => []
  | t::ts => t.map f :: map_aux f ts
end

/--
info: theorem RTree.map_aux.eq_2.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} (f : α → β) (t : RTree α) (ts : List (RTree α)),
  RTree.map_aux f (t :: ts) = RTree.map f t :: RTree.map_aux f ts :=
fun {α} {β} f t ts => Eq.refl (RTree.map_aux f (t :: ts))
-/
#guard_msgs in
#print RTree.map_aux.eq_2
