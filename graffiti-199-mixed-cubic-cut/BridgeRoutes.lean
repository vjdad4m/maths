import PrescribedPaths

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V]

namespace Traverses

theorem extend_universal {A B : Set V} {x y : V} (p : Traverses G A x y)
    (xy : x ≠ y) (included : A ⊆ B)
    (extra : ∀ v ∈ B, v ∉ A → ∀ w ∈ B, v ≠ w → G.Adj v w) :
    Traverses G B x y := by
  obtain ⟨P,first,last⟩ := p
  have front : P.vertices.head? = some x := by rw [List.head?_eq_head P.nonempty]; exact congrArg some first
  have finish : P.vertices.getLast? = some y := by rw [List.getLast?_eq_getLast P.nonempty]; exact congrArg some last
  have length : 2 ≤ P.vertices.length := by
    cases e : P.vertices with
    | nil => exact (P.nonempty e).elim
    | cons a L =>
      cases L with
      | nil =>
        have ax : a = x := by simpa only [e,List.head?_cons,Option.some.injEq] using front
        have ay : a = y := by simpa only [e,List.getLast?_singleton,Option.some.injEq] using finish
        exact (xy (ax.symm.trans ay)).elim
      | cons b T => simp
  apply traverses_of_universal_extension length P.nodup P.chain front finish
    (fun v h => included ((P.covers v).mp h))
  exact fun v vB no w wB ne => extra v vB (fun h => no ((P.covers v).mpr h)) w wB ne

end Traverses

/-- Two disjoint cliques with a specified bridge connecting them. -/
structure BridgedCliques (G : SimpleGraph V) where
  left : Set V
  right : Set V
  b : V
  c : V
  bl : b ∈ left
  cr : c ∈ right
  edge : G.Adj b c
  apart : Disjoint left right
  cl : left.Pairwise G.Adj
  cq : right.Pairwise G.Adj

namespace BridgedCliques

variable (K : BridgedCliques G)

def flip : BridgedCliques G :=
  ⟨K.right,K.left,K.c,K.b,K.cr,K.bl,K.edge.symm,K.apart.symm,K.cq,K.cl⟩

omit [Fintype V] in
theorem left_ne_right {x y : V} (xl : x ∈ K.left) (yr : y ∈ K.right) : x ≠ y :=
  fun h => Set.disjoint_left.mp K.apart xl (h.symm ▸ yr)

theorem some_route :
    ∃ x ∈ K.left, ∃ y ∈ K.right, Traverses G (K.left ∪ K.right) x y := by
  obtain ⟨x,xl,P⟩ := Traverses.end_clique K.cl K.bl
  obtain ⟨y,yr,Q⟩ := Traverses.start_clique K.cq K.cr
  exact ⟨x,xl,y,yr,P.join Q K.apart K.edge⟩

theorem route_from_left {x : V}
    (xl : x ∈ K.left) (start : x ≠ K.b ∨ K.left = {K.b}) :
    ∃ y ∈ K.right, Traverses G (K.left ∪ K.right) x y := by
  obtain ⟨y,yr,Q⟩ := Traverses.start_clique K.cq K.cr
  have P : Traverses G K.left x K.b := by
    rcases start with different|eq
    · exact Traverses.clique K.cl xl K.bl different
    · have xb : x ∈ ({K.b} : Set V) := eq ▸ xl
      change x = K.b at xb
      subst x
      exact eq.symm ▸ Traverses.single K.b
  exact ⟨y,yr,P.join Q K.apart K.edge⟩

private theorem same_side_via_block {z x y w : V} {L1 L2 : Set V}
    (partition : L1 ∪ L2 = K.left) (apart : Disjoint L1 L2)
    (P : Traverses G L1 x K.b) (Q : Traverses G L2 w y) (wL : w ∈ L2)
    (zOff : z ∉ K.left ∪ K.right)
    (universal : ∀ v ∈ K.left ∪ K.right, G.Adj z v) :
    Traverses G ((K.left ∪ K.right) ∪ {z}) x y := by
  have L1sub : L1 ⊆ K.left := fun _ h => partition ▸ (Or.inl h : _ ∈ L1 ∪ L2)
  have L2sub : L2 ⊆ K.left := fun _ h => partition ▸ (Or.inr h : _ ∈ L1 ∪ L2)
  have leftR : Disjoint L1 K.right := Set.disjoint_left.mpr
    (fun x xl xr => Set.disjoint_left.mp K.apart (L1sub xl) xr)
  obtain ⟨t,tr,R⟩ := Traverses.start_clique K.cq K.cr
  have path1 := P.join R leftR K.edge
  have off : Disjoint (L1 ∪ K.right) {z} :=
    Set.disjoint_singleton_right.mpr (fun h => zOff (h.imp (fun x => L1sub x) id))
  have path2 := path1.join (Traverses.single z) off (universal _ (Or.inr tr)).symm
  have dis : Disjoint ((L1 ∪ K.right) ∪ {z}) L2 := by
    apply Set.disjoint_left.mpr
    intro v hv v2
    rcases hv with (v1|vr)|vz
    · exact Set.disjoint_left.mp apart v1 v2
    · exact Set.disjoint_left.mp K.apart (L2sub v2) vr
    · exact zOff (Or.inl ((show v = z from vz) ▸ L2sub v2))
  have all := path2.join Q dis (universal w (Or.inl (L2sub wL)))
  have eq : ((L1 ∪ K.right) ∪ {z}) ∪ L2 = (K.left ∪ K.right) ∪ {z} := by
    rw [← partition]
    ext v
    simp only [Set.mem_union]
    tauto
  exact eq ▸ all

private theorem same_left {z x y : V} (xl : x ∈ K.left) (yl : y ∈ K.left) (xy : x ≠ y)
    (zOff : z ∉ K.left ∪ K.right)
    (universal : ∀ v ∈ K.left ∪ K.right, G.Adj z v) :
    Traverses G ((K.left ∪ K.right) ∪ {z}) x y := by
  classical
  have from_b (v : V) (vl : v ∈ K.left) (vb : v ≠ K.b) :
      Traverses G ((K.left ∪ K.right) ∪ {z}) K.b v := by
    let L2 := K.left \ {K.b}
    have v2 : v ∈ L2 := ⟨vl,vb⟩
    obtain ⟨s,s2,Q⟩ := Traverses.end_clique (K.cl.mono Set.diff_subset) v2
    have dis : Disjoint ({K.b} : Set V) L2 :=
      Set.disjoint_singleton_left.mpr (fun h => h.2 rfl)
    have union : {K.b} ∪ L2 = K.left := by
      ext w
      by_cases e : w = K.b <;> simp [L2,e,K.bl]
    exact K.same_side_via_block union dis (Traverses.single K.b) Q s2 zOff universal
  by_cases xb : x = K.b
  · subst x
    exact from_b y yl xy.symm
  · by_cases yb : y = K.b
    · subst y
      exact (from_b x xl xb).reverse
    · let L1 := K.left \ {y}
      have x1 : x ∈ L1 := ⟨xl,xy⟩
      have b1 : K.b ∈ L1 := ⟨K.bl,Ne.symm yb⟩
      have P := Traverses.clique (K.cl.mono Set.diff_subset) x1 b1 xb
      have dis : Disjoint L1 ({y} : Set V) :=
        Set.disjoint_singleton_right.mpr (fun h => h.2 rfl)
      have union : L1 ∪ {y} = K.left := by
        ext w
        by_cases e : w = y <;> simp [L1,e,yl]
      exact K.same_side_via_block union dis P (Traverses.single y) (by simp) zOff universal

/-- One universal vertex suffices for all endpoint pairs drawn from the
two bridge cliques. -/
theorem route_with_one_universal {z x y : V} (xB : x ∈ K.left ∪ K.right)
    (yB : y ∈ K.left ∪ K.right) (xy : x ≠ y)
    (zOff : z ∉ K.left ∪ K.right)
    (universal : ∀ v ∈ K.left ∪ K.right, G.Adj z v) :
    Traverses G ((K.left ∪ K.right) ∪ {z}) x y := by
  have opposite {u v : V} (ul : u ∈ K.left) (vr : v ∈ K.right) :
      Traverses G ((K.left ∪ K.right) ∪ {z}) u v := by
    obtain ⟨i,il,P⟩ := Traverses.start_clique K.cl ul
    obtain ⟨j,jr,Q⟩ := Traverses.end_clique K.cq vr
    have leftOff : Disjoint K.left {z} :=
      Set.disjoint_singleton_right.mpr (fun h => zOff (Or.inl h))
    have q := P.join (Traverses.single z) leftOff (universal i (Or.inl il)).symm
    have dis : Disjoint (K.left ∪ {z}) K.right :=
      Set.disjoint_union_left.mpr ⟨K.apart,Set.disjoint_singleton_left.mpr (fun h => zOff (Or.inr h))⟩
    have path := q.join Q dis (universal j (Or.inr jr))
    have eq : (K.left ∪ {z}) ∪ K.right = (K.left ∪ K.right) ∪ {z} := by
      ext v
      simp only [Set.mem_union]
      tauto
    exact eq ▸ path
  rcases xB with xl|xr <;> rcases yB with yl|yr
  · exact K.same_left xl yl xy zOff universal
  · exact opposite xl yr
  · exact (opposite yl xr).reverse
  · have path := K.flip.same_left xr yr xy
      (fun h => zOff (h.elim Or.inr Or.inl)) (fun _ h => universal _ (h.elim Or.inr Or.inl))
    have eq : (K.flip.left ∪ K.flip.right) ∪ {z} = (K.left ∪ K.right) ∪ {z} := by
      change (K.right ∪ K.left) ∪ {z} = _
      rw [Set.union_comm K.right K.left]
    exact eq ▸ path

end BridgedCliques
end Graffiti199Depleted.Catalogue
