import SixSingletonQ2Data189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.Q2
open SimpleGraph SimpleGraph.Walk Finset Sat Graffiti189Ore ArticulationPair
open private walk_of_chain from ArticulationClique189
open private positive_even_cap from TwoCutOrderCenters189
open private in_positive_even_of_dist_two from TwoCutDistanceCaps189
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def posEdge (u v : Vertex) : List Literal :=
  match tag u v with
  | .variable i => [.pos i]
  | _=>[]

def negEdge (u v : Vertex) : List Literal :=
  match tag u v with
  | .variable i => [.neg i]
  | _=>[]

theorem satisfies_iff_neg (v : Valuation) (c : List Literal) :
    v.satisfies c ↔ ((∀ l∈c,v.neg l) → False) := by
  induction c with
  | nil => simp [Valuation.satisfies]
  | cons l c ih =>
    rw [Valuation.satisfies,ih]
    simp only [List.forall_mem_cons]
    tauto

theorem no_edge_of_falsified_pos {G : SimpleGraph Vertex} {u v : Vertex}
    (nf : tag u v≠.fixed) (forb : G.Adj u v → tag u v≠.forb)
    (neg : ∀ l∈posEdge u v,(value G).neg l) : ¬G.Adj u v := by
  intro edge
  cases e : tag u v with
  | forb => exact forb edge e
  | fixed => exact nf e
  | «variable» i =>
    have m : Literal.pos i∈posEdge u v := by simp [posEdge,e]
    exact neg _ m ((edge_atom G e).mpr edge)

theorem edge_of_falsified_neg {G : SimpleGraph Vertex} [DecidableRel G.Adj] (M : Data G)
    {u v : Vertex} (nf : tag u v≠.forb)
    (neg : ∀ l∈negEdge u v,(value G).neg l) : G.Adj u v := by
  cases e : tag u v with
  | forb => exact (nf e).elim
  | fixed => exact M.fixed u v e
  | «variable» i =>
    have m : Literal.neg i∈negEdge u v := by simp [negEdge,e]
    exact (edge_atom G e).mp (neg _ m)

def walkClause : List Vertex → List Literal
  | u::v::t => negEdge u v ++ walkClause (v::t)
  | _ => []

def feasibleWalk : List Vertex → Bool
  | u::v::t => (tag u v != .forb) && feasibleWalk (v::t)
  | _ => true

theorem chain_of_falsified_walk {G : SimpleGraph Vertex} [DecidableRel G.Adj] (M : Data G)
    (L : List Vertex) (good : feasibleWalk L=true)
    (neg : ∀ l∈walkClause L,(value G).neg l) : L.Chain' G.Adj := by
  match L with
  | [] => trivial
  | [u] => exact List.chain'_singleton u
  | u::v::t =>
    have m : (tag u v != .forb) = true ∧ feasibleWalk (v::t) = true := by simpa only [feasibleWalk,Bool.and_eq_true] using good
    refine List.Chain'.cons (edge_of_falsified_neg M (by simpa using m.1) ?_) (chain_of_falsified_walk M (v::t) m.2 ?_)
    · intro l lm
      exact neg l (List.mem_append_left _ lm)
    · intro l lm
      exact neg l (List.mem_append_right _ lm)

theorem sat_path {G : SimpleGraph Vertex} [DecidableRel G.Adj] (M : Data G)
    (no : ¬Traceable G)
    (p : List Vertex) (nd : p.Nodup) (cov : ∀ u,u∈p) (good : feasibleWalk p=true) :
    (value G).satisfies (walkClause p) := by
  rw [satisfies_iff_neg]
  intro h
  have c := chain_of_falsified_walk M p good h
  cases p with
  | nil => exact List.not_mem_nil (cov 0)
  | cons u t =>
    obtain ⟨v,w,eq⟩ := walk_of_chain u t c
    exact no ⟨u,v,w,IsPath.mk' (eq.symm ▸ nd),fun x=>eq.symm ▸ cov x⟩

theorem sat_degree {G : SimpleGraph Vertex} [DecidableRel G.Adj] (M : Data G)
    (u : Vertex) (xs : List Vertex) (u8 : u≠8)
    (nf : ∀ v : Vertex,v∈xs → tag u v≠.fixed)
    (few : (neighborsAllowed u\xs.toFinset).card≤5) :
    (value G).satisfies (xs.flatMap (posEdge u)) := by
  rw [satisfies_iff_neg]
  intro n
  have sub : G.neighborFinset u⊆neighborsAllowed u\xs.toFinset := by
    intro v mv
    have g := (mem_neighborFinset _ _ _).mp mv
    apply mem_sdiff.mpr
    refine ⟨mem_filter.mpr ⟨mem_univ _,M.allowed u v g⟩,?_⟩
    intro m
    have q := List.mem_toFinset.mp m
    apply no_edge_of_falsified_pos (nf _ q) (M.allowed u v) (fun l lm=>n l ?_) g
    exact List.mem_flatMap.mpr ⟨v,q,lm⟩
  have low := card_le_card sub
  rw [card_neighborFinset_eq_degree] at low
  have hi := M.degree u u8
  omega

theorem sat_budget {G : SimpleGraph Vertex} [DecidableRel G.Adj] (M : Data G)
    (u : Vertex) (xs : List Vertex) (nd : xs.Nodup) (seven : xs.length=7)
    (off : ∀ v : Vertex,v∈xs → v≠u) :
    (value G).satisfies (xs.map (fun v=>.neg (two u v))) := by
  rw [satisfies_iff_neg]
  intro n
  have sub : xs.toFinset⊆PositiveEven G u := by
    intro v mv
    have q := List.mem_toFinset.mp mv
    have w := n _ (List.mem_map_of_mem q)
    exact in_positive_even_of_dist_two ((two_atom G (off _ q).symm).mp w)
  have h := card_le_card sub
  rw [List.toFinset_card_of_nodup nd,seven] at h
  have up := positive_even_cap (d:=6) (M.cap u)
  omega

theorem sat_witness {G : SimpleGraph Vertex} [DecidableRel G.Adj] (M : Data G)
    {u v w : Vertex} (uv : u≠v) (notfix : tag u v≠.fixed)
    (uw : tag u w≠.forb) (wv : tag w v≠.forb) :
    (value G).satisfies (.pos (two u v)::(posEdge u v++negEdge u w++negEdge w v)) := by
  rw [satisfies_iff_neg]
  intro n
  have no : ¬G.Adj u v := no_edge_of_falsified_pos notfix (M.allowed u v) (fun l lm=>
    n l (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ lm))))
  have e1 : G.Adj u w := edge_of_falsified_neg M uw (fun l lm=>
    n l (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ lm))))
  have e2 : G.Adj w v := edge_of_falsified_neg M wv (fun l lm=>
    n l (List.mem_cons_of_mem _ (List.mem_append_right _ lm)))
  let p : G.Walk u v := .cons e1 (.cons e2 .nil)
  have hc := G.dist_le p
  have w2 : p.length=2 := rfl
  have x : G.dist u v≠0 := dist_ne_zero_iff_ne_and_reachable.mpr ⟨uv,p.reachable⟩
  have y : G.dist u v≠1 := fun h=>no (dist_eq_one_iff_adj.mp h)
  have z : G.dist u v=2 := by omega
  exact n (Literal.pos (two u v)) List.mem_cons_self ((two_atom G uv).mpr z)

theorem sat_hit {G : SimpleGraph Vertex} {u : Vertex} {xs : List Vertex}
    (vhit : ∃ v∈xs,G.Adj u v)
    (test : ∀ v : Vertex,v∈xs → tag u v≠.fixed ∧ tag u v≠.forb) :
    (value G).satisfies (xs.flatMap (posEdge u)) := by
  rw [satisfies_iff_neg]
  intro h
  obtain ⟨v,vm,uv⟩ := vhit
  have ⟨nf,nb⟩ := test v vm
  exact no_edge_of_falsified_pos nf (fun _=>nb) (fun l lm=>h l (List.mem_flatMap.mpr ⟨v,vm,lm⟩)) uv

deriving instance DecidableEq for Sat.Literal

theorem sat_superset {v : Valuation} {c d : List Literal}
    (h : c.all (fun l=>decide (l∈d))=true) (sat : v.satisfies c) : v.satisfies d := by
  rw [satisfies_iff_neg] at sat ⊢
  intro bad
  exact sat (fun l lm=>bad l (of_decide_eq_true (List.all_eq_true.mp h _ lm)))

end Graffiti189LongestPath.CrossSaturation.ThresholdSix.Q2
