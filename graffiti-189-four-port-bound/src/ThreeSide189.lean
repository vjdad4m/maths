import FourCut189
namespace Graffiti189LongestPath.FourCut.Three
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

/-- Data supplied by three distinct components of a two-vertex deletion. -/
structure Sides (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) where
  con : G.Connected
  ab : a ≠ b
  d2 : ∀ x, (DistanceTwo G x).card ≤ 4
  even : ∀ x, (EvenFrom G x).card ≤ 5
  degree : ∀ x y : V, x≠y → 4≤G.degree x ∨ 4≤G.degree y
  H : Fin 3 → Finset V
  dis : ∀ i j, i≠j → Disjoint (H i) (H j)
  off : ∀ i, a∉H i ∧ b∉H i
  closed : ∀ i, ∀ x∈H i, ∀ y, G.Adj x y → y=a ∨ y=b ∨ y∈H i
  joined : ∀ i, ∀ x∈H i, ∀ y∈H i, ∃ q : G.Walk x y, ∀ z∈q.support, z∈H i
  hita : ∀ i, ∃ x∈H i, G.Adj a x
  hitb : ∀ i, ∃ x∈H i, G.Adj b x
  plenty : ∀ i, 2≤(H i).card → 2≤((H i).filter (fun x => G.Adj a x ∨ G.Adj b x)).card

namespace Sides
noncomputable section
variable {a b : V} (S : Sides G a b)
def A (i : Fin 3) := (S.H i).filter (G.Adj a)
def B (i : Fin 3) := (S.H i).filter (G.Adj b)
def D (i : Fin 3) := (S.H i).filter (fun x => x∈DistanceTwo G a)
def Ports (i : Fin 3) := (S.H i).filter (fun x => G.Adj a x ∨ G.Adj b x)
def Inner (i : Fin 3) := (S.H i) \ S.Ports i

def swap : Sides G b a where
  con := S.con
  ab := S.ab.symm
  d2 := S.d2
  even := S.even
  degree := S.degree
  H := S.H
  dis := S.dis
  off i := (S.off i).symm
  closed i x hx y xy := (S.closed i x hx y xy).elim (fun h => Or.inr (Or.inl h))
    (fun h => h.elim Or.inl (fun h => Or.inr (Or.inr h)))
  joined := S.joined
  hita := S.hitb
  hitb := S.hita
  plenty i two := by simpa only [or_comm] using S.plenty i two

theorem dist_two {x y z : V} (hc : G.Connected) (xz : x≠z)
    (no : ¬G.Adj x z) (xy : G.Adj x y) (yz : G.Adj y z) :
    G.dist x z=2 := by
  have lo := hc.one_lt_dist_of_ne_of_not_adj xz no
  have hi := G.dist_le (Walk.cons xy (Walk.cons yz .nil))
  simp at hi
  omega

theorem mem_d2 {x y : V} : y∈DistanceTwo G x ↔ G.dist x y=2 := by
  classical
  simp [DistanceTwo]

theorem apos (i : Fin 3) : 1≤(S.A i).card := by
  obtain ⟨x,hx,ax⟩ := S.hita i
  exact card_pos.mpr ⟨x,mem_filter.mpr ⟨hx,ax⟩⟩

theorem adj_forces_same {i j : Fin 3} (ij : i≠j)
    {x y : V} (xi : x∈S.H i) (yj : y∈S.H j) : ¬G.Adj x y := fun xy =>
  (S.closed i x xi y xy).elim
    (fun e => (S.off j).1 (e ▸ yj))
    (fun h => h.elim (fun e => (S.off j).2 (e ▸ yj))
     (fun yi => disjoint_left.mp (S.dis i j ij) yi yj))

theorem foreign_port {i j : Fin 3} (ij : i≠j) {x y : V}
    (xi : x∈S.A i) (yj : y∈S.A j) : y∈DistanceTwo G x := by
  obtain ⟨xH,ax⟩ := mem_filter.mp xi
  obtain ⟨yH,ay⟩ := mem_filter.mp yj
  have ne : x≠y := fun e => disjoint_left.mp (S.dis i j ij) (e ▸ xH) yH
  exact mem_d2.mpr (dist_two S.con ne (S.adj_forces_same ij xH yH) ax.symm ay)

theorem pair_cap {i j k : Fin 3} (ij : i≠j) (ik : i≠k) (jk : j≠k) :
    (S.A j).card+(S.A k).card≤4 := by
  obtain ⟨x,hx⟩ := card_pos.mp (S.apos i)
  have dis : Disjoint (S.A j) (S.A k) := (S.dis j k jk).mono (filter_subset _ _) (filter_subset _ _)
  have sub : S.A j ∪ S.A k ⊆ DistanceTwo G x := union_subset
    (fun y hy => S.foreign_port ij hx hy) (fun y hy => S.foreign_port ik hx hy)
  have le := card_le_card sub
  rw [card_union_of_disjoint dis] at le
  exact le.trans (S.d2 x)

theorem degree_bound {i : Fin 3} {x : V} (hx : x∈S.A i) :
    G.degree x ≤ (S.A i).card+(S.D i).card+(if G.Adj x b then 1 else 0) := by
  obtain ⟨xi,ax⟩ := mem_filter.mp hx
  let t : Finset V := ({b} : Finset V).filter (G.Adj x)
  have sub : G.neighborFinset x ⊆ insert a (t ∪ ((S.A i).erase x ∪ S.D i)) := by
    intro y hy
    have xy := (mem_neighborFinset G x y).mp hy
    rcases S.closed i x xi y xy with rfl|rfl|yi
    · simp
    · simp [t,xy]
    · refine mem_insert.mpr (Or.inr (mem_union.mpr (Or.inr (mem_union.mpr ?_))))
      by_cases ay : G.Adj a y
      · exact Or.inl (mem_erase.mpr ⟨xy.ne.symm,mem_filter.mpr ⟨yi,ay⟩⟩)
      · right
        have na : a≠y := fun e => (S.off i).1 (e.symm ▸ yi)
        exact mem_filter.mpr ⟨yi,mem_d2.mpr (dist_two S.con na ay ax xy)⟩
  have c := card_le_card sub
  have c1 := card_insert_le a (t ∪ ((S.A i).erase x ∪ S.D i))
  have c2 := card_union_le t ((S.A i).erase x ∪ S.D i)
  have c3 := card_union_le ((S.A i).erase x) (S.D i)
  rw [card_erase_of_mem hx] at c3
  rw [card_neighborFinset_eq_degree] at c
  have cardt : t.card = (if G.Adj x b then 1 else 0) := by
    by_cases yes : G.Adj x b
    · have eq : t={b} := by ext y; simp [t]; aesop
      simp [eq,yes]
    · have eq : t=∅ := by ext y; simp [t]; aesop
      simp [eq,yes]
  have po := S.apos i
  omega

theorem Dsum :
    (S.D 0).card+(S.D 1).card+(S.D 2).card≤(DistanceTwo G a).card := by
  have sub (i : Fin 3) : S.D i ⊆ DistanceTwo G a := fun _ hx => (mem_filter.mp hx).2
  have dis (i j : Fin 3) (ne : i≠j) : Disjoint (S.D i) (S.D j) :=
    (S.dis i j ne).mono (filter_subset _ _) (filter_subset _ _)
  have c := card_le_card (union_subset (union_subset (sub 0) (sub 1)) (sub 2))
  rw [card_union_of_disjoint (disjoint_union_left.mpr
      ⟨dis 0 2 (by decide),dis 1 2 (by decide)⟩),card_union_of_disjoint (dis 0 1 (by decide))] at c
  exact c

theorem saturates {i j k : Fin 3} (ij : i≠j) (ik : i≠k) (jk : j≠k)
    (full : (S.A j).card+(S.A k).card=4) {x : V} (xi : x∈S.A i) :
    (∀ y∈S.H i, x=y ∨ G.Adj x y) ∧ G.Adj b x ∧ S.B j⊆S.A j ∧ S.B k⊆S.A k := by
  let F := S.A j ∪ S.A k
  have sub : F⊆DistanceTwo G x :=
    union_subset (fun _ hy => S.foreign_port ij xi hy) (fun _ hy => S.foreign_port ik xi hy)
  have cf : F.card=4 := by
    have dis : Disjoint (S.A j) (S.A k) := (S.dis j k jk).mono (filter_subset _ _) (filter_subset _ _)
    rw [show F=S.A j∪S.A k from rfl,card_union_of_disjoint dis,full]
  have eq : DistanceTwo G x=F := (eq_of_subset_of_card_le sub (by rw [cf]; exact S.d2 x)).symm
  have inside {y : V} (yi : y∈S.H i) : y∉DistanceTwo G x := by
    rw [eq]
    intro h
    rcases mem_union.mp h with h|h
    · exact disjoint_left.mp (S.dis i j ij) yi (mem_filter.mp h).1
    · exact disjoint_left.mp (S.dis i k ik) yi (mem_filter.mp h).1
  have uni (y : V) (yi : y∈S.H i) : x=y ∨ G.Adj x y := by
    obtain ⟨w,ws⟩ := S.joined i x (mem_filter.mp xi).1 y yi
    have step {u v : V} (q : G.Walk u v) (hs : ∀ z∈q.support,z∈S.H i)
        (head : x=u ∨ G.Adj x u) : x=v ∨ G.Adj x v := by
      induction q with
      | nil => exact head
      | @cons u z v uz q ih =>
        apply ih (fun z hz => hs z (by simp [hz]))
        rcases head with rfl|head
        · exact Or.inr uz
        by_cases xz : x=z
        · exact Or.inl xz
        by_cases edge : G.Adj x z
        · exact Or.inr edge
        exact (inside (hs z (by simp)) (mem_d2.mpr (dist_two S.con xz edge head uz))).elim
    exact step w ws (Or.inl rfl)
  have xb : G.Adj b x := by
    by_cases xb : G.Adj b x
    · exact xb
    obtain ⟨y,yi,by'⟩ := S.hitb i
    rcases uni y yi with e|xy
    · exact (xb (e.symm ▸ by')).elim
    have ne : x≠b := fun e => (S.off i).2 (e ▸ (mem_filter.mp xi).1)
    have bt := mem_d2.mpr (dist_two S.con ne (fun e => xb e.symm) xy by'.symm)
    rw [eq] at bt
    rcases mem_union.mp bt with bt|bt
    · exact ((S.off j).2 (mem_filter.mp bt).1).elim
    · exact ((S.off k).2 (mem_filter.mp bt).1).elim
  have cover {l : Fin 3} (il : i≠l) (side : l=j ∨ l=k) : S.B l⊆S.A l := by
    intro y hy
    obtain ⟨yl,by'⟩ := mem_filter.mp hy
    have xl := (mem_filter.mp xi).1
    have ne : x≠y := fun e => disjoint_left.mp (S.dis i l il) (e ▸ xl) yl
    have yt := mem_d2.mpr (dist_two S.con ne (S.adj_forces_same il xl yl) xb.symm by')
    rw [eq] at yt
    rcases side with e|e
    · subst l
      rcases mem_union.mp yt with h|h
      · exact h
      · exact (disjoint_left.mp (S.dis j k jk) yl (mem_filter.mp h).1).elim
    · subst l
      rcases mem_union.mp yt with h|h
      · exact (disjoint_left.mp (S.dis j k jk) (mem_filter.mp h).1 yl).elim
      · exact h
  exact ⟨uni,xb,cover ij (Or.inl rfl),cover ik (Or.inr rfl)⟩

#print axioms saturates
end
end Sides
end Graffiti189LongestPath.FourCut.Three
