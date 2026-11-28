import SmallSeparator189
import CycleRootBridge189

open SimpleGraph SimpleGraph.Walk Graffiti189LongestPath

namespace PosaCycleExtend189

open private Graffiti189LongestPath.outside_edge from SmallSeparator189

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- A cycle containing every vertex of a longest path, and longer by
one edge, cannot omit any vertex of a connected graph. -/
theorem spanning_of_longest_path_cycle {a b t : V} {p : G.Walk a b}
    (hp : IsLongest p) (hc : G.Connected) (c : G.Walk t t) (cycle : c.IsCycle)
    (sup : ∀ v, v ∈ c.support ↔ v ∈ p.support) (long : p.length < c.length) :
    ∀ v, v ∈ p.support := by
  by_contra! h
  obtain ⟨x,xout,y,yin,xy⟩ := Graffiti189LongestPath.outside_edge p hc h
  have yc := (sup y).2 yin
  let d := c.rotate yc
  have dc : d.IsCycle := cycle.rotate yc
  obtain ⟨hlen,hsupp⟩ := CycleRootBridge.rotated_cycle_support_length c cycle yc
  change d.length = c.length at hlen
  have dn : ¬ d.Nil := by simpa only [nil_iff_eq_nil] using dc.ne_nil
  have tail : d.tail.IsPath := by
    rw [isPath_def, support_tail d dn]
    exact dc.support_nodup
  have xoff : x ∉ d.tail.reverse.support := by
    intro hx
    rw [support_reverse, List.mem_reverse, support_tail d dn] at hx
    exact xout ((sup x).1 ((hsupp x).1 (List.mem_of_mem_tail hx)))
  let q := Walk.cons xy d.tail.reverse
  have qp : q.IsPath := tail.reverse.cons xoff
  have qlen : q.length = c.length := by
    change (Walk.cons xy d.tail.reverse).length = c.length
    rw [length_cons, length_reverse, length_tail_add_one dn, hlen]
  have too := hp.2 _ _ q qp
  omega

end PosaCycleExtend189

#print axioms PosaCycleExtend189.spanning_of_longest_path_cycle
