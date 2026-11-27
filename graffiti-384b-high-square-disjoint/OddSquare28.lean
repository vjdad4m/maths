import HighDisjoint28

namespace Graffiti384b.HighSquare28
open Finset SimpleGraph EarFrame33 HighEar Core28 Four28
open private CubicShore.half_tight from CubicDiamondCut33
open private Repair.isolate Repair.nbr_mono Repair.triangles_le_choose from Repair384b
open private CliquePivot33.isolated_degree from CliquePivot33
open private Four28.ear_one Four28.core_data from FourFrontier28
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- An omitted vertex that sees two fixed pins of either color leaves
27 vertices to divide into two dominating sets. -/
private theorem odd_cut {A B : Finset V} {s : V} (n : Fintype.card V=28)
    (fr : Frame H A B) (off : s∉A∪B) (sa : 2≤nbr H s A) (sb : 2≤nbr H s B)
    (remaining : ∀ w,w∉A∪B → 3≤H.degree w ∧ (H.Adj w s → 4≤H.degree w)) : gamma H≤13 := by
  apply Nat.le_of_not_gt
  intro h
  apply (CliquePivot33.shared H ∅ fr.1 (fun m => off (mem_union_left _ m))
    (fun m => off (mem_union_right _ m)) sa sb fr.2.1 fr.2.2 ?_) (CubicShore.half_tight H (by omega))
  intro w ws wa wb
  obtain ⟨d,high⟩ := remaining w (fun m => (mem_union.mp m).elim wa wb)
  simp only [not_mem_empty,ite_false,Nat.mul_zero,Nat.add_zero]
  rw [CliquePivot33.isolated_degree H ws]
  by_cases edge : H.Adj w s
  · rw [card_erase_of_mem ((H.mem_neighborFinset ..).mpr edge),card_neighborFinset_eq_degree]
    have := high edge; omega
  · rwa [erase_eq_of_not_mem (fun m => edge ((H.mem_neighborFinset ..).mp m)),card_neighborFinset_eq_degree]

omit [Fintype V] in
private theorem absorb {A B : Finset V} {u : V} (fr : Frame H A B) (ua : u∉A)
    (sees : 2≤nbr H u A) : Frame H A (insert u B) := by
  refine ⟨?_,fun w wm => (fr.2.1 w wm).trans (Repair.nbr_mono H w (subset_insert ..)),?_⟩
  · apply disjoint_left.mpr
    intro z za zb
    exact (mem_insert.mp zb).elim (fun h => ua (h ▸ za)) (disjoint_left.mp fr.1 za)
  · intro w wm
    exact (mem_insert.mp wm).elim (fun h => h ▸ sees) (fr.2.2 w)

/-- The one remaining cubic can stay free when it misses the omitted
vertex, or be pinned opposite two of its neighbors. -/
private theorem absorb_cut {A B : Finset V} {s u : V} (n : Fintype.card V=28)
    (fr : Frame H A B) (off : s∉A∪B) (us : u≠s) (sa : 2≤nbr H s A) (sb : 2≤nbr H s B)
    (degree : ∀ w,w∉A∪B → 3≤H.degree w ∧ (w≠u → 4≤H.degree w))
    (safe : ¬H.Adj u s ∨ 2≤nbr H u A ∨ 2≤nbr H u B) : gamma H≤13 := by
  by_cases um : u∈A∪B
  · exact odd_cut H n fr off sa sb (fun w wm => ⟨(degree w wm).1,fun _ =>
      (degree w wm).2 (fun h => wm (h ▸ um))⟩)
  have extend {L R : Finset V} (f : Frame H L R) (un : u∉L∪R) (sn : s∉L∪R)
      (ls : 2≤nbr H s L) (rs : 2≤nbr H s R) (hit : 2≤nbr H u L)
      (deg : ∀ w,w∉L∪R → 3≤H.degree w ∧ (w≠u → 4≤H.degree w)) : gamma H≤13 := by
    have f' := absorb H f (fun m => un (mem_union_left _ m)) hit
    apply odd_cut H n f' (by simpa [mem_union,not_or,us.symm] using sn) ls
      (rs.trans (Repair.nbr_mono H s (subset_insert ..)))
    intro w wm
    have bare : w∉L∪R := fun m => wm (union_subset_union (Subset.rfl) (subset_insert ..) m)
    exact ⟨(deg w bare).1,fun _ => (deg w bare).2 (fun h => wm (mem_union_right L (h ▸ mem_insert_self ..)))⟩
  rcases safe with miss|ha|hb
  · apply odd_cut H n fr off sa sb
    intro w wm
    exact ⟨(degree w wm).1,fun adj => (degree w wm).2 (fun h => miss (h ▸ adj))⟩
  all_goals first
    | exact extend fr um off sa sb ha degree
    | exact extend ⟨fr.1.symm,fr.2.2,fr.2.1⟩ ((union_comm A B) ▸ um)
        ((union_comm A B) ▸ off) sb sa hb (fun w wm => degree w ((union_comm B A) ▸ wm))

/-- Choose two pins Q in the four-clique of the score-three cubic.
Both ear endpoints must touch Q and be outside Q. A fourth vertex s
seeing both pins can be omitted whenever the score-two cubic is safe. -/
theorem opposite_pins_saving {e a b s u v : V} {C Q : Finset V}
    (n : Fintype.card V=28) (pos : ∀ w,0<trianglesAt H w) (fi : Function.Injective (trianglesAt H))
    (ab : H.Adj a b) (en : H.neighborFinset e={a,b}) (sm : s∈additional H e a b)
    (su : trianglesAt H u=2) (sv : trianglesAt H v=3) (us : u≠s)
    (cl : H.IsNClique 4 C) (vc : v∈C) (ec : e∉C) (sc : s∉C)
    (sub : Q⊆C) (two : Q.card=2) (aq : a∉Q) (bq : b∉Q)
    (ah : ∃ p∈Q,H.Adj a p) (bh : ∃ p∈Q,H.Adj b p) (sh : ∀ p∈Q,H.Adj s p)
    (safe : ¬H.Adj u s ∨ 2≤nbr H u ((C\Q)∪{a,b}) ∨ 2≤nbr H u (insert e Q)) : gamma H≤13 := by
  classical
  let L := (C\Q)∪{a,b}
  let R := insert e Q
  obtain ⟨se,as',bs⟩ := (additional_mem H).mp sm
  have ea : H.Adj e a := (H.mem_neighborFinset ..).mp (en ▸ mem_insert_self ..)
  have eb : H.Adj e b := (H.mem_neighborFinset ..).mp (en ▸ mem_insert_of_mem (mem_singleton_self _))
  have leftSize : (C\Q).card=2 := by rw [card_sdiff sub,cl.2,two]
  have see {w : V} {A : Finset V} (sz : A.card=2) (all : ∀ z∈A,H.Adj w z) : 2≤nbr H w A := by
    simp [nbr,filter_true_of_mem all,sz]
  have ends (w : V) (wa : H.Adj w a) (wb : H.Adj w b) : 2≤nbr H w L := by
    exact PinnedColor34.two H ab.ne wa wb (mem_union_right _ (mem_insert_self ..))
      (mem_union_right _ (mem_insert_of_mem (mem_singleton_self _)))
  have right (w : V) (ew : H.Adj e w) (hit : ∃ p∈Q,H.Adj w p) : 2≤nbr H w R := by
    obtain ⟨p,pm,wp⟩ := hit
    have ne : e≠p := fun h => ec (h.symm ▸ sub pm)
    exact PinnedColor34.two H ne ew.symm wp
      (mem_insert_self ..) (mem_insert_of_mem pm)
  have fr : Frame H L R := by
    constructor
    · apply disjoint_left.mpr
      intro w wl wr
      rcases mem_union.mp wl with wc|pair
      · exact (mem_insert.mp wr).elim (fun h => ec (h ▸ (mem_sdiff.mp wc).1)) (mem_sdiff.mp wc).2
      · rcases mem_insert.mp pair with rfl|eq
        · exact (mem_insert.mp wr).elim ea.ne.symm aq
        · rw [mem_singleton.mp eq] at wr
          exact (mem_insert.mp wr).elim eb.ne.symm bq
    constructor
    · intro w wl
      rcases mem_union.mp wl with wc|pair
      · obtain ⟨wm,wq⟩ := mem_sdiff.mp wc
        exact (see two (fun z zm => cl.1 wm (sub zm) (fun h => wq (h ▸ zm)))).trans
          (Repair.nbr_mono H w (subset_insert ..))
      · rcases mem_insert.mp pair with rfl|eq
        · exact right _ ea ah
        · rw [mem_singleton.mp eq]; exact right b eb bh
    · intro w wr
      rcases mem_insert.mp wr with rfl|wq
      · exact ends _ ea eb
      · exact (see leftSize (fun z zm => cl.1 (sub wq) (mem_sdiff.mp zm).1
          (fun h => (mem_sdiff.mp zm).2 (h ▸ wq)))).trans (Repair.nbr_mono H w subset_union_left)
  have off : s∉L∪R := by simp [L,R,sc,se,as'.ne.symm,bs.ne.symm,show s∉Q from fun h => sc (sub h)]
  apply absorb_cut H n fr off us (ends s as'.symm bs.symm)
    ((see two sh).trans (Repair.nbr_mono H s (subset_insert ..))) ?_ safe
  intro w wm
  have we : w≠e := fun h => wm (mem_union_right L (h ▸ mem_insert_self ..))
  have wc : w∉C := by
    intro wC
    by_cases wq : w∈Q
    · exact wm (mem_union_right _ (mem_insert_of_mem wq))
    · exact wm (mem_union_left _ (mem_union_left _ (mem_sdiff.mpr ⟨wC,wq⟩)))
  have sear := Four28.ear_one H ab.ne en pos
  have n1 : trianglesAt H w≠1 := fun h => we (fi (h.trans sear.symm))
  have n3 : trianglesAt H w≠3 := fun h => wc ((fi (h.trans sv.symm)) ▸ vc)
  have high := Repair.triangles_le_choose H w
  have positive := pos w
  have dg : 3≤H.degree w := by
    apply Nat.le_of_not_gt
    intro low
    have cap := high.trans (Nat.choose_le_choose 2 (Nat.le_of_lt_succ low : H.degree w≤2))
    rw [Nat.choose_self] at cap; omega
  refine ⟨dg,?_⟩
  intro wu
  have n2 : trianglesAt H w≠2 := fun h => wu (fi (h.trans su.symm))
  apply Nat.le_of_not_gt
  intro low
  have cap := high.trans (Nat.choose_le_choose 2 (Nat.le_of_lt_succ low : H.degree w≤3))
  change trianglesAt H w≤3 at cap; omega

/-- Common neighbors of the fourth vertex and the score-three cubic,
excluding the two ear endpoints. -/
def pinsAvailable (s v a b : V) := (H.neighborFinset s∩H.neighborFinset v)\{a,b}

/-- In a failing original graph, a fourth vertex missing both cubics
cannot have two available pins while both endpoints touch available pins. -/
theorem contact_restriction (t : (types H).card=29) (q : (nonleaves H).card=28) (bad : bound H<gamma H) :
    let J := triangleEdges (H.induce (nonleaves H:Set V))
    J.CliqueFree 5 → ∀ e a b s u v,J.Adj a b → J.neighborFinset e={a,b} →
    s∈additional J e a b → trianglesAt J u=2 → J.degree v=3 → trianglesAt J v=3 →
    ¬J.Adj u s → ¬J.Adj v s →
    let K := pinsAvailable J s v a b
    K.card≤1 ∨ (K.filter (J.Adj a))=∅ ∨ (K.filter (J.Adj b))=∅ := by
  classical
  dsimp only
  intro free e a b s u v ab en sm su dv sv umiss vmiss
  let J := triangleEdges (H.induce (nonleaves H:Set V))
  let C := insert v (J.neighborFinset v)
  let K := pinsAvailable J s v a b
  obtain ⟨n,pos,fi,half,_⟩ := Four28.core_data H t q bad
  obtain ⟨_,da,db,hard,_⟩ := forced_pair H t q bad free e a b ab en
  obtain ⟨_,ss⟩ := hard s sm
  change 4≤trianglesAt J s at ss
  change trianglesAt J u=2 at su
  change trianglesAt J v=3 at sv
  change J.degree v=3 at dv
  have us : u≠s := by intro h; subst s; omega
  have vs : v≠s := by intro h; subst s; omega
  have cl : J.IsNClique 4 C := by
    refine ⟨?_,by simp [C,dv]⟩
    intro p pm r rm pr
    rcases mem_insert.mp pm with h|pN <;> rcases mem_insert.mp rm with k|rN
    · exact (pr (h.trans k.symm)).elim
    · rw [h]; exact (J.mem_neighborFinset ..).mp rN
    · rw [k]; exact ((J.mem_neighborFinset ..).mp pN).symm
    · exact EarAnchor.full_neighbors J dv sv ((J.mem_neighborFinset ..).mp pN) ((J.mem_neighborFinset ..).mp rN) pr
  have ev : e≠v := by
    have se := Four28.ear_one J ab.ne en pos
    intro h; subst e; omega
  have eout : e∉C := by
    intro m; rcases mem_insert.mp m with k|vn
    · exact ev k
    have ge := ((J.mem_neighborFinset ..).mp vn).symm
    have ep : v∈({a,b}:Finset _) := en ▸ (J.mem_neighborFinset ..).mpr ge
    rcases mem_insert.mp ep with eq|other
    · rw [eq] at dv; change 4≤J.degree a at da; omega
    · have eq := mem_singleton.mp other
      rw [eq] at dv; change 4≤J.degree b at db; omega
  have sout : s∉C := fun m => (mem_insert.mp m).elim vs.symm (fun h => vmiss ((J.mem_neighborFinset ..).mp h))
  change K.card≤1 ∨ _=∅ ∨ _=∅
  by_cases small : K.card≤1
  · exact Or.inl small
  by_cases an : (K.filter (J.Adj a))=∅
  · exact Or.inr (Or.inl an)
  by_cases bn : (K.filter (J.Adj b))=∅
  · exact Or.inr (Or.inr bn)
  obtain ⟨x,xm⟩ := nonempty_iff_ne_empty.mpr an
  obtain ⟨y,ym⟩ := nonempty_iff_ne_empty.mpr bn
  obtain ⟨xK,ax⟩ := mem_filter.mp xm
  obtain ⟨yK,by'⟩ := mem_filter.mp ym
  obtain ⟨Q,xy,qK,two⟩ := exists_subsuperset_card_eq (insert_subset xK (singleton_subset_iff.mpr yK))
    (card_le_two (a:=x) (b:=y)) (by omega : 2≤K.card)
  have inside {p} (pm : p∈Q) : p∈(J.neighborFinset s∩J.neighborFinset v) ∧ p∉({a,b}:Finset _) := mem_sdiff.mp (qK pm)
  have save := opposite_pins_saving J n pos fi ab en sm su sv us cl (mem_insert_self ..) eout sout
    (fun p pm => mem_insert_of_mem (mem_inter.mp (inside pm).1).2) two
    (fun h => (inside h).2 (mem_insert_self ..)) (fun h => (inside h).2 (mem_insert_of_mem (mem_singleton_self _)))
    ⟨x,xy (mem_insert_self ..),ax⟩ ⟨y,xy (mem_insert_of_mem (mem_singleton_self _)),by'⟩
    (fun p pm => (J.mem_neighborFinset ..).mp (mem_inter.mp (inside pm).1).1) (Or.inl umiss)
  exact ((Nat.not_succ_le_self 13) (half.trans save)).elim

end Graffiti384b.HighSquare28
#print axioms Graffiti384b.HighSquare28.opposite_pins_saving
#print axioms Graffiti384b.HighSquare28.contact_restriction
