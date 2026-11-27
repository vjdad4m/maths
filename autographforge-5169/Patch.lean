import Obstructions

namespace Packing2560
open SimpleGraph Finset BullCover1125
variable {V : Type*} {G : SimpleGraph V} {a b : V} {X : Finset V}

/-- At most two neighbors of any vertex can belong to an independent set
in a claw-free graph. -/
theorem neighbor_limit (cl : Free G claw) (ind : ∀ x ∈ X, ∀ y ∈ X, ¬ G.Adj x y)
    (v : V) (all : ∀ x ∈ X, G.Adj v x) : X.card ≤ 2 := by
  by_contra! large
  obtain ⟨r,s,t,hr,hs,ht,rs,rt,st⟩ := two_lt_card_iff.mp large
  exact (claw_neighbors cl (all r hr) (all s hs) (all t ht) rs rt st).elim (ind r hr s hs)
    (fun h => h.elim (ind r hr t ht) (ind s hs t ht))

theorem three_bound (cl : Free G claw) (h : Attached G a b X) : X.card ≤ 3 := by
  classical
  by_cases all : ∀ x ∈ X, G.Adj b x
  · exact (neighbor_limit cl h.independent b all).trans (by decide)
  push_neg at all
  obtain ⟨x,hx,bx⟩ := all
  have cap : (X.erase x).card ≤ 2 := by
    apply neighbor_limit cl (fun r hr s hs => h.independent r (mem_of_mem_erase hr) s (mem_of_mem_erase hs)) b
    intro y hy
    exact ((pair_up cl h hx (mem_of_mem_erase hy) (ne_of_mem_erase hy).symm).resolve_right
      (fun z => bx z.2)).2
  rw [card_erase_of_mem hx] at cap
  omega

/-- When three private assignments land on one edge, the patch is a bull.
The chosen names make the two private neighbors and the common neighbor explicit. -/
structure Profile (G : SimpleGraph V) (a b : V) (X : Finset V) where
  x : V
  y : V
  z : V
  hx : x ∈ X
  hy : y ∈ X
  hz : z ∈ X
  xz : x ≠ z
  yz : y ≠ z
  ax : G.Adj a x
  byEdge : G.Adj b y
  az : G.Adj a z
  bz : G.Adj b z
  bx : ¬ G.Adj b x
  ay : ¬ G.Adj a y

theorem heavy_profile (cl : Free G claw) (h : Attached G a b X) (large : 2 < X.card) :
    Nonempty (Profile G a b X) := by
  classical
  have missing (v : V) : ∃ z ∈ X, ¬ G.Adj v z := by
    by_contra! all
    exact Nat.not_le_of_gt large (neighbor_limit cl h.independent v all)
  obtain ⟨x,hx,bx⟩ := missing b
  obtain ⟨y,hy,ay⟩ := missing a
  have third : ∃ z ∈ X, z ≠ x ∧ z ≠ y := by
    by_contra none
    have sub : X ⊆ {x,y} := fun v hv => by
      by_cases eq : v=x
      · simp [eq]
      · by_cases eqy : v=y
        · simp [eqy]
        · exact False.elim (none ⟨v,hv,eq,eqy⟩)
    have cap := (card_le_card sub).trans (card_insert_le x {y})
    simp at cap
    omega
  obtain ⟨z,hz,zx,zy⟩ := third
  have bz := ((pair_up cl h hx hz zx.symm).resolve_right (fun e => bx e.2)).2
  have az := ((pair_up cl h hy hz zy.symm).resolve_left (fun e => ay e.1)).1
  exact ⟨⟨x,y,z,hx,hy,hz,zx.symm,zy.symm,(h.touch x hx).resolve_right bx,
    (h.touch y hy).resolve_left ay,az,bz,bx,ay⟩⟩

theorem profile_copy (p : Profile G a b X) (h : Attached G a b X) :
    ∃ f : bull ↪g G, ∀ i, f i = a ∨ f i = b ∨ f i ∈ X := by
  classical
  let f : Fin 5 → V := ![a,b,p.x,p.y,p.z]
  have xy := h.independent _ p.hx _ p.hy
  have xz := h.independent _ p.hx _ p.hz
  have yz := h.independent _ p.hy _ p.hz
  have rel (i j : Fin 5) : G.Adj (f i) (f j) ↔ bull.Adj i j := by
    fin_cases i <;> fin_cases j <;>
      simp [f,listed,h.edge,p.ax,p.byEdge,p.az,p.bz,h.edge.symm,p.ax.symm,p.byEdge.symm,
        p.az.symm,p.bz.symm,p.bx,p.ay,xy,xz,yz,G.adj_comm p.x b,G.adj_comm p.y a,
        G.adj_comm p.y p.x,G.adj_comm p.z p.x,G.adj_comm p.z p.y]
  have rows : ∀ i j : Fin 5, i ≠ j → ∃ k, ¬ (bull.Adj i k ↔ bull.Adj j k) := by decide
  have inj : Function.Injective f := by
    intro i j eq
    by_contra ne
    obtain ⟨k,hk⟩ := rows _ _ ne
    exact hk ((rel i k).symm.trans (eq ▸ rel j k))
  refine ⟨⟨⟨f,inj⟩,rel _ _⟩,fun i => ?_⟩
  change f i = a ∨ f i = b ∨ f i ∈ X
  fin_cases i <;> simp [f,p.hx,p.hy,p.hz]

theorem profile_neighbors (p : Profile G a b X) {v} (hv : v=a ∨ v=b) :
    ∃ r ∈ X, ∃ s ∈ X, r ≠ s ∧ G.Adj v r ∧ G.Adj v s := by
  rcases hv with rfl|rfl
  · exact ⟨_,p.hx,_,p.hz,p.xz,p.ax,p.az⟩
  · exact ⟨_,p.hy,_,p.hz,p.yz,p.byEdge,p.bz⟩

theorem patch_cover (cl : Free G claw) (h : Attached G a b X) :
    ∃ P : Finset G.edgeSet, P.card ≤ 2 + (if 2 < X.card then 1 else 0) ∧
      ∀ v, v=a ∨ v=b ∨ v∈X → ∃ e ∈ P, v ∈ e.val := by
  classical
  by_cases heavy : 2 < X.card
  · obtain ⟨p⟩ := heavy_profile cl h heavy
    let Y := X.erase p.z
    have sub : Y ⊆ X := erase_subset _ _
    have attached : Attached G a b Y := ⟨h.edge,fun x hx => h.away x (sub hx),
      fun x hx y hy => h.independent x (sub hx) y (sub hy),fun x hx => h.touch x (sub hx)⟩
    have cap := three_bound cl h
    have small : Y.card ≤ 2 := by
      dsimp [Y]
      rw [card_erase_of_mem p.hz]
      omega
    obtain ⟨P,cost,covers⟩ := small_piece cl attached small
    let e : G.edgeSet := ⟨s(a,p.z),p.az⟩
    refine ⟨insert e P, (card_insert_le _ _).trans (by simp [heavy]; omega),?_⟩
    intro v hv
    by_cases eq : v = p.z
    · exact ⟨e,mem_insert_self _ _,eq ▸ Sym2.mem_iff.mpr (Or.inr rfl)⟩
    · obtain ⟨f,hf,vf⟩ := covers v (hv.imp_right (Or.imp_right (fun hx => mem_erase.mpr ⟨eq,hx⟩)))
      exact ⟨f,mem_insert_of_mem hf,vf⟩
  · simpa [heavy] using small_piece cl h (le_of_not_gt heavy)

end Packing2560
