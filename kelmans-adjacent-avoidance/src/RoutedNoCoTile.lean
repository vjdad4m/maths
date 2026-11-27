import ThreePort

open Finset
namespace KelmansCactus.AtomicBridge
open ThreePort

private theorem only_exit
    {V I : Type*} {G : SimpleGraph V} {A : Finset V} {p q : I→V}
    (S : Seam (G:=G) A p q) (i : I) {v : V} (outside : v∉A)
    (edge : G.Adj (p i) v) : v=q i := by
  obtain ⟨j,hp,hq⟩ := (S.edge (p i) (S.left i) v outside).mp edge
  have ji : j=i := S.left_inj hp
  subst j
  exact hq.symm

/-- In a packing that omits an edge of a matching seam, its endpoints
cannot occur together in a tile even as two nonadjacent leaves. -/
theorem no_tile_at_omitted_seam
    {V I : Type*} [DecidableEq V]
    {G K : SimpleGraph V} {D B : Finset V} {p q p' q' : I→V}
    (HA : Seam (G:=G) D p q) (HB : Seam (G:=G) B p' q')
    (sep : Disjoint D B) (i j : I)
    (revA : p' j=q i) (revB : q' j=p i)
    (adj : ∀ {x y},K.Adj x y→G.Adj x y)
    (omitEdge : ¬K.Adj (p i) (q i))
    {P : Finset (Finset V)} (tile : ∀t∈P,KelmansStarter.IsTile K t) :
    ¬∃ t∈P,p i∈t∧q i∈t := by
  classical
  rintro ⟨t,tt,pt,qt⟩
  obtain ⟨_,c,ct,star⟩ := tile t tt
  have pq : p i≠q i := by
    intro e
    have h := HA.left i
    rw [e] at h
    exact HA.right i h
  by_cases cp : c=p i
  · have h : K.Adj c (q i) := star _ qt (fun q=>pq (cp.symm.trans q.symm))
    rw [cp] at h
    exact omitEdge h
  by_cases cq : c=q i
  · have h : K.Adj c (p i) := star _ pt (fun p=>pq (p.trans cq))
    rw [cq] at h
    exact omitEdge h.symm
  have pc : G.Adj (p i) c := (adj (star _ pt (Ne.symm cp))).symm
  have qc : G.Adj (q i) c := (adj (star _ qt (Ne.symm cq))).symm
  have inside : c∈D := by
    by_contra no
    exact cq (only_exit HA i no pc)
  have outside : c∉B := fun h=>disjoint_left.mp sep inside h
  rw [←revA] at qc
  exact cp ((only_exit HB j outside qc).trans revB)

#print axioms no_tile_at_omitted_seam
end KelmansCactus.AtomicBridge
