import EJTerminalOrderTwo189

namespace Graffiti189Ore
open SimpleGraph SimpleGraph.Walk Finset
open private only_edgeSet only_cap from OreClosure189
variable {V : Type*} [Fintype V] [DecidableEq V] {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
set_option linter.unusedSectionVars false

/-- If the newly added edge is used, cutting it from the apex cycle
exposes a spanning path in the original capped graph. -/
theorem traceable_or_open_one_edge {u v : V}
    (only : ∀ x y, H.Adj x y → G.Adj x y ∨ s(x,y)=s(u,v))
    (ht : Traceable H) :
    Traceable G ∨ ∃ p : (cap G (fun _=>True)).Walk (some u) (some v),
        p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  obtain ⟨a,b,p,hp,all⟩ := ht
  by_cases h : s(u,v) ∈ p.edges
  swap
  · have ed : ∀ e ∈ p.edges, e ∈ G.edgeSet := by
      intro e he
      exact (only_edgeSet only e (p.edges_subset_edgeSet he)).resolve_right
        (fun eq=>h (eq ▸ he))
    let q := p.transfer G ed
    have qs : q.support=p.support := support_transfer p ed
    exact .inl ⟨a,b,q,IsPath.mk' (qs ▸ hp.support_nodup),fun w=>qs ▸ all w⟩
  have ab : a≠b := by
    intro eq
    subst b
    have e0 : 0=p.length := (hp.getVert_eq_end_iff (Nat.zero_le _)).mp (by simp)
    have zn := length_eq_zero_iff.mp e0.symm
    simp [zn] at h
  obtain ⟨c,hc,cn,_⟩ := cap_ring (P:=fun _=>True) p hp all ab trivial trivial
  have he : s((some u : Option V),some v) ∈ c.edges := by
    rename_i hen
    rw [hen]
    simp only [List.cons_append,List.mem_cons,List.mem_append]
    exact Or.inr (Or.inl (List.mem_map.mpr ⟨_,h,rfl⟩))
  obtain ⟨x,y,w,wp,wa,xye,we⟩ := cut_spanning_ring hc he cn
  have transfer : ∀ e ∈ w.edges, e ∈ (cap G (fun _=>True)).edgeSet := by
    intro e he'
    obtain ⟨_,hn⟩ := we e he'
    exact (only_edgeSet (only_cap only) e (w.edges_subset_edgeSet he')).resolve_right hn
  let q := w.transfer (cap G (fun _=>True)) transfer
  have qs : q.support=w.support := support_transfer w transfer
  have qp : q.IsPath := IsPath.mk' (qs ▸ wp.support_nodup)
  have qa : ∀ z, z ∈ q.support := fun z=>qs ▸ wa z
  apply Or.inr
  rcases Sym2.eq_iff.mp xye with ⟨e,f⟩|⟨e,f⟩
  · subst x; subst y
    exact ⟨q,qp,qa⟩
  subst x; subst y
  exact ⟨q.reverse,qp.reverse,fun z=>by simpa using qa z⟩

theorem cap_traceability_of_overlap {u v : V}
    {p : (cap G (fun _=>True)).Walk (some u) (some v)}
    (hp : p.IsPath) (all : ∀ z,z∈p.support)
    {i : ℕ} (il : i<p.length)
    (ui : (cap G (fun _=>True)).Adj (some u) (p.getVert (i+1)))
    (vi : (cap G (fun _=>True)).Adj (some v) (p.getVert i)) :
    Traceable G := by
  obtain ⟨q,hq,hs⟩ := ore_spliced_path p hp i il vi
  let r := Walk.cons ui q.reverse
  have ring : SpanningRing r := by
    constructor
    · simpa only [r,support_cons,List.tail_cons,support_reverse,List.nodup_reverse] using hq.support_nodup
    · intro w
      simpa only [r,support_cons,List.tail_cons,support_reverse,List.mem_reverse] using (hs w).mpr (all w)
  obtain ⟨x,y,p',_,_,path,all'⟩ := ring_to_cap_path r ring
  exact ⟨x,y,p',path,all'⟩

#print axioms traceable_or_open_one_edge
end Graffiti189Ore
