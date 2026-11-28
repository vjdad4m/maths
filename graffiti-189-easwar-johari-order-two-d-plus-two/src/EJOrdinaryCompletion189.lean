import OreClosure189
import ArticulationClosure189

namespace Graffiti189Ore
open SimpleGraph SimpleGraph.Walk Finset
open private degree_increasing graphSize_lt graphSize_le from OreClosure189
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G H : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem traceable_ore_completion (sub : G ≤ H)
    (hdeg : ∀ x y, H.Adj x y → ¬ G.Adj x y → Fintype.card V ≤ G.degree x + G.degree y + 1)
    (hp : Traceable H) : Traceable G := by
  classical
  induction hn : graphSize H-graphSize G using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases eq : G=H
    · simpa [eq] using hp
    have not_sub : ¬ H ≤ G := fun e=>eq (le_antisymm sub e)
    have missing : ∃ u v, H.Adj u v ∧ ¬G.Adj u v := by
      by_contra neg
      push_neg at neg
      exact not_sub (fun {u v} e=>neg u v e)
    obtain ⟨u,v,uv,nu⟩ := missing
    let K := G ⊔ fromEdgeSet ({s(u,v)} : Set (Sym2 V))
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    have gk : G≤K := le_sup_left
    have kh : K≤H := by
      intro x y e
      rcases (sup_adj _ _ x y).mp e with e|e
      · exact sub e
      · obtain ⟨es,_⟩ := (fromEdgeSet_adj _).mp e
        have eqs : s(x,y)=s(u,v) := es
        apply (SimpleGraph.mem_edgeSet H).mp
        rw [eqs]
        exact (SimpleGraph.mem_edgeSet H).mpr uv
    have kv : K.Adj u v := (sup_adj _ _ _ _).mpr (Or.inr ((fromEdgeSet_adj _).mpr ⟨rfl,uv.ne⟩))
    have glt : G < K := lt_of_le_of_ne gk (fun e=>nu (e.symm ▸ kv))
    have less : graphSize H-graphSize K<n := by
      have smaller := graphSize_lt glt
      have below := graphSize_le kh
      omega
    have nd (x y : V) (e : H.Adj x y) (k : ¬K.Adj x y) :
        Fintype.card V ≤ K.degree x+K.degree y+1 := by
      have orig := hdeg x y e (fun g=>k (gk g))
      exact orig.trans (Nat.add_le_add_right (Nat.add_le_add (degree_increasing gk x) (degree_increasing gk y)) 1)
    have rr := ih _ less (G:=K) kh nd rfl
    refine traceable_closure_one (u:=u) (v:=v) ?_ (hdeg u v uv nu) rr
    intro x y e
    rcases (sup_adj _ _ x y).mp e with e|e
    · exact Or.inl e
    · exact Or.inr ((fromEdgeSet_adj _).mp e).1


#print axioms traceable_ore_completion
end Graffiti189Ore

namespace Graffiti189LongestPath.SmallOrder
open SimpleGraph SimpleGraph.Walk Finset Graffiti189Ore CrossSaturation CrossSaturation.ArticulationPair
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- Ore completion avoids any degree sequence theorem: complete the high
class to a clique and leave the sole possible low vertex untouched. -/
theorem traceable_all_but_one_by_order (hc : G.Connected) (d : ℕ)
    (degree : ∀ u v : V,u≠v → d≤G.degree u ∨ d≤G.degree v)
    (order : Fintype.card V≤2*d+1) :
    Graffiti189Ore.Traceable G := by
  classical
  let A := (univ : Finset V).filter (fun u=>d≤G.degree u)
  let K := completeWith G A
  have eq (u : V) : u∈A ↔ d≤G.degree u := by simp [A]
  refine traceable_ore_completion (completeWith_mono G A) ?_ ?_
  · intro u v uv not
    obtain ⟨ua,va,_⟩ := uv.resolve_left not
    have uhi := (eq u).mp ua
    have vhi := (eq v).mp va
    omega
  by_cases low : ∃ z,¬d≤G.degree z
  · obtain ⟨z,zlo⟩ := low
    by_cases one : Fintype.card V≤1
    · have ss := Fintype.card_le_one_iff_subsingleton.mp one
      exact ⟨z,z,Walk.nil,by simp,fun u=>by simp [ss.elim u z]⟩
    have some : ∃ y : V,y≠z := by
      apply Classical.byContradiction
      intro none
      have sub : (univ : Finset V)⊆{z} := fun u _=>mem_singleton.mpr
        (Classical.byContradiction (fun e=>none ⟨u,e⟩))
      have c := card_le_card sub
      rw [card_univ,card_singleton] at c
      omega
    obtain ⟨y,yz⟩ := some
    have hit : ∃ v,G.Adj z v := by
      obtain ⟨q⟩ := hc.preconnected z y
      cases q with
      | nil => exact (yz rfl).elim
      | cons e q => exact ⟨_,e⟩
    obtain ⟨v,zv⟩ := hit
    have va : v∈A := (eq v).mpr ((degree v z zv.ne.symm).resolve_right zlo)
    obtain ⟨r,p,pp,ps⟩ := rooted_path_in_clique A (completeWith_of_mem G A) va
    have za : z∉A := fun a=>zlo ((eq z).mp a)
    let e : K.Adj z v := completeWith_mono G A zv
    refine ⟨z,r,Walk.cons e p,pp.cons (fun h=>za ((ps z).mp h)),?_⟩
    intro u
    simp only [support_cons,List.mem_cons,ps]
    by_cases uz : u=z
    · exact .inl uz
    exact .inr ((eq u).mpr ((degree u z uz).resolve_right zlo))
  obtain ⟨x⟩ := hc.nonempty
  have all (v : V) : v∈A := (eq v).mpr
    (Classical.byContradiction (fun h=>low ⟨v,h⟩))
  obtain ⟨y,p,pp,ps⟩ := rooted_path_in_clique A (completeWith_of_mem G A) (all x)
  exact ⟨x,y,p,pp,fun u=>(ps u).mpr (all u)⟩

#print axioms traceable_all_but_one_by_order
end Graffiti189LongestPath.SmallOrder
