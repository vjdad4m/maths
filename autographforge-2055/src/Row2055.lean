import TraceableBurn
import DegreeTwoClass
import Sharpness

namespace TraceableBurn
open SimpleGraph Finset

open PathCycleSharpness (Burns burning ClawFree Eulerian Subcubic)

theorem burns_of_cover {V : Type*} {G : SimpleGraph V} (hc : G.Connected)
    {k : ℕ} (h : Cover G k) : Burns G k := by
  obtain ⟨c,cover⟩ := h
  let flip : Fin k → Fin k := fun r => ⟨k-1-r.val,by have h := r.isLt; omega⟩
  refine ⟨fun t => c (flip t),?_⟩
  intro x
  obtain ⟨r,hr⟩ := cover x
  have inv : flip (flip r)=r := Fin.ext (by
    have h := r.isLt
    change k-1-(k-1-r.val)=r.val
    omega)
  refine ⟨flip r,?_⟩
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist (c (flip (flip r))) x
  refine ⟨p,?_⟩
  have hp' := hp.trans (congrArg (fun z : Fin k => G.dist (c z) x) inv)
  change p.length≤k-1-(k-1-r.val)
  have h := r.isLt
  calc
    p.length = G.dist (c r) x := hp'
    _ ≤ r.val := hr
    _ = k-1-(k-1-r.val) := by omega

private theorem acyclic_neighbors_not_adj {V : Type*} {G : SimpleGraph V}
    (ha : G.IsAcyclic) {a x y : V} (xy : x≠y) (ax : G.Adj a x) (ay : G.Adj a y) : ¬G.Adj x y := by
  intro e
  let p : G.Path x y := ⟨Walk.cons e Walk.nil,Walk.IsPath.cons Walk.IsPath.nil (by simpa using xy)⟩
  let q : G.Path x y := ⟨Walk.cons ax.symm (Walk.cons ay Walk.nil),
    Walk.IsPath.cons (Walk.IsPath.cons Walk.IsPath.nil (by simpa using ay.ne)) (by simp [ax.ne.symm,xy])⟩
  have hp := congrArg (fun t : G.Path x y => t.val.length) (ha.path_unique p q)
  change 1=2 at hp
  omega

theorem degree_le_two_of_claw_free_tree {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (ht : G.IsTree) (hf : ClawFree G) (a : V) : G.degree a≤2 := by
  classical
  by_contra! h
  have h' : 2<(G.neighborFinset a).card := by simpa [G.card_neighborFinset_eq_degree] using h
  obtain ⟨x,y,z,xm,ym,zm,xy,xz,yz⟩ := Finset.two_lt_card_iff.mp h'
  have ax : G.Adj a x := (mem_neighborFinset _ _ _).1 xm
  have ay : G.Adj a y := (mem_neighborFinset _ _ _).1 ym
  have az : G.Adj a z := (mem_neighborFinset _ _ _).1 zm
  rcases hf a x y z ax ay az xy xz yz with hxy|hxz|hyz
  · exact acyclic_neighbors_not_adj ht.IsAcyclic xy ax ay hxy
  · exact acyclic_neighbors_not_adj ht.IsAcyclic xz ax az hxz
  · exact acyclic_neighbors_not_adj ht.IsAcyclic yz ay az hyz

theorem cover_of_degree_two {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hc : G.Connected) (hn : 2≤Fintype.card V)
    (hd : ∀ v, G.degree v≤2) {k : ℕ} (hs : Fintype.card V≤k^2) : Cover G k := by
  classical
  have hv (v : V) : Graffiti271.nbr G v = G.neighborFinset v := by
    ext w
    exact (Graffiti271.mem_nbr G).trans (mem_neighborFinset G v w).symm
  have hd' : ∀ v, (Graffiti271.nbr G v).card≤2 := by
    intro v
    rw [hv,card_neighborFinset_eq_degree]
    exact hd v
  obtain ⟨m,_,f,_,adj⟩ := GraffitiDegreeTwo.degree_two_indexed G hc hn hd'
  have hcard := Fintype.card_congr f
  rw [Fintype.card_fin] at hcard
  have hs' : m+1≤k^2 := hcard.trans_le hs
  exact cover_of_enumeration hc (Nat.zero_lt_succ m) hs' f
    (fun i j hij => (adj i j).2 (.inl hij))

/-- AutoGraphForge normalized row 2055, cleared of the positive denominator. -/
theorem row2055 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2≤Fintype.card V) (ht : G.IsTree) (hf : ClawFree G) :
    2*burning G≤PathCycleSharpness.slater G+4 := by
  have hd := degree_le_two_of_claw_free_tree G ht hf
  have size := (card_le_thrice_slater G hd).trans (path_budget _)
  have cv := cover_of_degree_two G ht.isConnected hn hd size
  have hb : burning G≤slater G/2+2 := Nat.sInf_le (burns_of_cover ht.isConnected cv)
  change 2*burning G≤TraceableBurn.slater G+4
  omega

theorem row2055_rat {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2≤Fintype.card V) (ht : G.IsTree) (hf : ClawFree G) :
    (burning G : ℚ) ≤ (1/2 : ℚ)*PathCycleSharpness.slater G+2 := by
  have h : (2:ℚ)*(burning G : ℚ)≤(PathCycleSharpness.slater G : ℚ)+4 := by
    exact_mod_cast row2055 G hn ht hf
  linarith

#print axioms row2055_rat
end TraceableBurn
