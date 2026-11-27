import SquareCapFactor
import TwinObstruction

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.SquareCap
noncomputable section

universe u
variable {W : Type u} [Fintype W] [DecidableEq W]
variable {G : SimpleGraph W} [DecidableRel G.Adj]

private theorem square_two_neighbors (i : Port) :
    ∃ a b : Port, a ≠ b ∧ ∀ j, square.Adj i j ↔ j = a ∨ j = b := by
  revert i
  decide

private theorem square_common_two (i j : Port) (different : i ≠ j) :
    square.Adj i j ∨ ∃ a b : Port, a ≠ b ∧
      square.Adj i a ∧ square.Adj i b ∧ square.Adj j a ∧ square.Adj j b := by
  revert i j
  decide

abbrev Exterior (f : Port ↪ W) := {v : W // ∀ j, v ≠ f j}

private theorem ext_unique (cub : ∀ x,G.degree x=3) (f : Port ↪ W)
    (induced : ∀ a b,G.Adj (f a) (f b) ↔ square.Adj a b) (i : Port) :
    ∃! w : W, (∀ j, w ≠ f j) ∧ G.Adj (f i) w := by
  obtain ⟨a,b,ab,spec⟩ := square_two_neighbors i
  let N := G.neighborFinset (f i)
  let S : Finset W := {f a,f b}
  have Nadj : ∀ w,w ∈ N ↔ G.Adj (f i) w := mem_neighborFinset _ _
  have sub : S ⊆ N := by
    intro v h
    rw [Nadj]
    simp only [S,mem_insert,mem_singleton] at h
    rcases h with rfl|rfl
    · exact (induced i a).mpr ((spec a).mpr (Or.inl rfl))
    · exact (induced i b).mpr ((spec b).mpr (Or.inr rfl))
  have sizeS : S.card = 2 := by
    have h : f a ≠ f b := fun e => ab (f.injective e)
    simp [S,card_insert_of_not_mem,h]
  have sizeN : N.card = 3 := cub _
  have less : (N \ S).card = 1 := by rw [card_sdiff sub,sizeN,sizeS]
  obtain ⟨q,he⟩ := card_eq_one.mp less
  have props (w : W) : w ∈ N \ S ↔ (∀ j,w ≠ f j) ∧ G.Adj (f i) w := by
    rw [mem_sdiff,Nadj]
    constructor
    · rintro ⟨adj,avoid⟩
      refine ⟨?_,adj⟩
      intro j eq
      have h := (spec j).mp ((induced i j).mp (eq ▸ adj))
      rcases h with rfl|rfl <;> exact avoid (by simp [S,eq])
    · rintro ⟨avoid,adj⟩
      refine ⟨adj,?_⟩
      intro h
      simp only [S,mem_insert,mem_singleton] at h
      exact h.elim (avoid a) (avoid b)
  refine ⟨q,props q |>.mp (he ▸ mem_singleton_self q),?_⟩
  intro w h
  have e : w ∈ N \ S := (props w).mpr h
  rw [he] at e
  exact mem_singleton.mp e

private def portOf (cub : ∀ x,G.degree x=3) (f : Port ↪ W)
    (induced : ∀ a b,G.Adj (f a) (f b) ↔ square.Adj a b) (i : Port) : Exterior f :=
  ⟨(ext_unique cub f induced i).exists.choose,(ext_unique cub f induced i).exists.choose_spec.1⟩

private theorem portOf_adj (cub : ∀ x,G.degree x=3) (f : Port ↪ W)
    (induced : ∀ a b,G.Adj (f a) (f b) ↔ square.Adj a b) (i : Port) :
    G.Adj (f i) (portOf cub f induced i).val :=
  (ext_unique cub f induced i).exists.choose_spec.2

private theorem eq_port_of_adj (cub : ∀ x,G.degree x=3) (f : Port ↪ W)
    (induced : ∀ a b,G.Adj (f a) (f b) ↔ square.Adj a b)
    (i : Port) (v : Exterior f) (h : G.Adj (f i) v.val) : v = portOf cub f induced i := by
  apply Subtype.ext
  rcases ext_unique cub f induced i with ⟨q,hq,all⟩
  exact (all _ ⟨v.property,h⟩).trans (all _
    ⟨(portOf cub f induced i).property,portOf_adj cub f induced i⟩).symm

/-- In a cubic cyclic-four graph of order at least seven an induced
square's four exterior contacts are necessarily distinct. -/
theorem square_distinct_contacts (cub : ∀ x,G.degree x=3)
    (small : SmallTrivial G) (large : 7 ≤ Fintype.card W)
    (f : Port ↪ W) (induced : ∀ a b,G.Adj (f a) (f b) ↔ square.Adj a b) :
    Function.Injective (portOf cub f induced) := by
  intro i j e
  by_contra ne
  let w := (portOf cub f induced i).val
  have hi : G.Adj (f i) w := portOf_adj cub f induced i
  have hj : G.Adj (f j) w := by
    change G.Adj (f j) (portOf cub f induced i).val
    rw [e]
    exact portOf_adj cub f induced j
  rcases square_common_two i j ne with adjacent | ⟨a,b,ab,ia,ib,ja,jb⟩
  · exact TwinObstruction.no_triangle small (by omega) ((induced i j).mpr adjacent)
      hj hi.symm (cub _).le (cub _).le (cub _).le
  · have fa : f a ≠ w := ((portOf cub f induced i).property a).symm
    have fb : f b ≠ w := ((portOf cub f induced i).property b).symm
    exact TwinObstruction.no_three_common_neighbors small large (fun eq => ne (f.injective eq))
      (fun eq => ab (f.injective eq)) fa fb
      ((induced i a).mpr ia) ((induced i b).mpr ib) hi
      ((induced j a).mpr ja) ((induced j b).mpr jb) hj
      (cub _).le (cub _).le (cub _).le (cub _).le (cub _).le

private def squarePorts (cub : ∀ x,G.degree x=3) (small : SmallTrivial G)
    (large : 7 ≤ Fintype.card W) (f : Port ↪ W)
    (pattern : ∀ a b,G.Adj (f a) (f b) ↔ square.Adj a b) : Port ↪ Exterior f :=
  ⟨portOf cub f pattern,square_distinct_contacts cub small large f pattern⟩

abbrev exteriorGraph (G : SimpleGraph W) (f : Port ↪ W) :
    SimpleGraph (Exterior f) := G.induce {w | ∀ j,w ≠ f j}

private def glueEquiv (f : Port ↪ W) : (Exterior f ⊕ Port) ≃ W := by
  classical
  let fn : Exterior f ⊕ Port → W := Sum.elim Subtype.val f
  have bij : Function.Bijective fn := by
    constructor
    · intro a b h
      cases a with
      | inl x => cases b with
        | inl y => exact congrArg Sum.inl (Subtype.ext h)
        | inr y => exact (x.property y h).elim
      | inr x => cases b with
        | inl y => exact (y.property x h.symm).elim
        | inr y => exact congrArg Sum.inr (f.injective h)
    · intro w
      by_cases h : ∃ i,w = f i
      · obtain ⟨i,eq⟩ := h
        exact ⟨Sum.inr i,eq.symm⟩
      · exact ⟨Sum.inl ⟨w,fun i e => h ⟨i,e⟩⟩,rfl⟩
  exact Equiv.ofBijective fn bij

private def squareIso (cub : ∀ x,G.degree x=3) (small : SmallTrivial G)
    (large : 7 ≤ Fintype.card W) (f : Port ↪ W)
    (pattern : ∀ a b,G.Adj (f a) (f b) ↔ square.Adj a b) :
    attach (exteriorGraph G f) square (squarePorts cub small large f pattern) id ≃g G := by
  refine { toEquiv := glueEquiv f, map_rel_iff' := ?_ }
  intro x y
  cases x with
  | inl v =>
    cases y with
    | inl w => rfl
    | inr j =>
      change G.Adj v.val (f j) ↔ ∃ i, portOf cub f pattern i = v ∧ i = j
      constructor
      · intro e
        exact ⟨j,(eq_port_of_adj cub f pattern j v e.symm).symm,rfl⟩
      · rintro ⟨i,h,rfl⟩
        rw [←h]
        exact (portOf_adj cub f pattern i).symm
  | inr i =>
    cases y with
    | inl w =>
      change G.Adj (f i) w.val ↔ ∃ j, portOf cub f pattern j = w ∧ j = i
      constructor
      · intro e
        exact ⟨i,(eq_port_of_adj cub f pattern i w e).symm,rfl⟩
      · rintro ⟨j,h,rfl⟩
        rw [←h]
        exact portOf_adj cub f pattern j
    | inr j => exact pattern i j

private theorem degree_iso {A B : Type*} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {K : SimpleGraph B} [DecidableRel H.Adj] [DecidableRel K.Adj]
    (e : H ≃g K) (v : A) : H.degree v = K.degree (e v) := by
  rw [←card_neighborSet_eq_degree,←card_neighborSet_eq_degree]
  let u : H.neighborSet v ≃ K.neighborSet (e v) := {
    toFun := fun x => ⟨e x.val,e.map_adj_iff.mpr x.property⟩
    invFun := fun y => ⟨e.symm y.val,by
      have h : H.Adj (e.symm (e v)) (e.symm y.val) := e.symm.map_adj_iff.mpr y.property
      simpa using h⟩
    left_inv := fun _ => Subtype.ext (e.toEquiv.symm_apply_apply _)
    right_inv := fun _ => Subtype.ext (e.toEquiv.apply_symm_apply _) }
  exact Fintype.card_congr u

private theorem boundary_iso {A B : Type*} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {K : SimpleGraph B} (e : H ≃g K) (c : A → Bool) :
    (boundary H c).card = (boundary K (c ∘ e.symm)).card := by
  classical
  have memA (z : A×A) : z∈boundary H c ↔ c z.1=true ∧ c z.2=false ∧ H.Adj z.1 z.2 := by
    simp [boundary]
  have memB (z : B×B) : z∈boundary K (c ∘ e.symm) ↔
      c (e.symm z.1)=true ∧ c (e.symm z.2)=false ∧ K.Adj z.1 z.2 := by simp [boundary]
  apply card_bij (fun z _ => (e z.1,e z.2))
  · intro z h
    obtain ⟨f,t,u⟩ := (memA z).mp h
    exact (memB _).mpr ⟨by simpa using f,by simpa using t,e.map_adj_iff.mpr u⟩
  · intro a _ b _ h
    exact Prod.ext (e.toEquiv.injective (congrArg Prod.fst h)) (e.toEquiv.injective (congrArg Prod.snd h))
  · intro z h
    obtain ⟨f,t,u⟩ := (memB z).mp h
    exact ⟨(e.symm z.1,e.symm z.2),(memA _).mpr ⟨f,t,e.symm.map_adj_iff.mpr u⟩,
      Prod.ext (e.toEquiv.apply_symm_apply _) (e.toEquiv.apply_symm_apply _)⟩

private theorem small_iso {A B : Type*} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {K : SimpleGraph B} (e : H ≃g K) (h : SmallTrivial K) :
    SmallTrivial H := by
  intro c near
  rw [boundary_iso e] at near
  rcases h (c ∘ e.symm) near with ts|fs
  · left
    intro x y hx hy
    apply e.toEquiv.injective
    exact ts (e x) (e y) (by simpa using hx) (by simpa using hy)
  · right
    intro x y hx hy
    apply e.toEquiv.injective
    exact fs (e x) (e y) (by simpa using hx) (by simpa using hy)

private theorem omit_iso {A B : Type*} {H : SimpleGraph A} {K : SimpleGraph B}
    (e : H ≃g K) (x y : A) (u v : A) :
    (omitEdge H x y).Adj u v → (omitEdge K (e x) (e y)).Adj (e u) (e v) := by
  rintro ⟨edge,none⟩
  refine ⟨e.map_adj_iff.mpr edge,?_⟩
  intro h
  rcases h with ⟨a,b⟩|⟨a,b⟩
  · exact none (Or.inl ⟨e.toEquiv.injective a,e.toEquiv.injective b⟩)
  · exact none (Or.inr ⟨e.toEquiv.injective a,e.toEquiv.injective b⟩)

/-- For any induced square in an arbitrary eligible graph, the
undesired vertex may be any square vertex and the omitted edge may
be any of its four exterior edges. The proof partitions the
remainder without using any exterior wire. -/
theorem square_f2 (t2 : CyclicT2Promise.{u})
    (cub : ∀ x,G.degree x = 3) (small : SmallTrivial G)
    (large : 7 ≤ Fintype.card W) (order : Fintype.card W%6=4)
    (f : Port ↪ W) (pattern : ∀ a b,G.Adj (f a) (f b) ↔ square.Adj a b)
    (i j : Port) {y : W} (outside : ∀ k,y ≠ f k) (wire : G.Adj (f j) y) :
    FactorOn (omitEdge G (f j) y) (univ.erase (f i)) := by
  classical
  let V := Exterior f
  let p := squarePorts cub small large f pattern
  let H := attach (exteriorGraph G f) square p id
  let e := squareIso cub small large f pattern
  have old := Fintype.card_congr e.toEquiv
  have n : Fintype.card (V⊕Port)=Fintype.card V+4 := by
    rw [Fintype.card_sum]
    rfl
  have all : Fintype.card W = Fintype.card V + 4 := old.symm.trans n
  have vv : 4 < Fintype.card V := by omega
  have cc (z : V⊕Port) : H.degree z = 3 := (degree_iso e z).trans (cub _)
  have ss : SmallTrivial H := small_iso e small
  have oo : Fintype.card (Exterior f ⊕ Port)%6=4 := by rw [old]; exact order
  have part := square_f2_explicit t2 oo vv cc ss i j
  have trans := factor_map e.toEquiv.toEmbedding (omit_iso e (Sum.inr j) (Sum.inl (p j))) part
  have wq : (e (Sum.inl (p j)))=y := by
    change (portOf cub f pattern j).val=y
    exact (congrArg Subtype.val (eq_port_of_adj cub f pattern j ⟨y,outside⟩ wire)).symm
  have hi : e (Sum.inr i)=f i := rfl
  have hj : e (Sum.inr j)=f j := rfl
  rw [Finset.map_erase,map_univ_equiv] at trans
  change FactorOn (omitEdge G (e (Sum.inr j)) (e (Sum.inl (p j))))
    (univ.erase (e (Sum.inr i))) at trans
  rw [hi,hj,wq] at trans
  exact trans

/-- In the relevant class a copy of the square is automatically
induced. An extra diagonal would make a triangle. -/
theorem square_copy_is_induced (cub : ∀ x,G.degree x = 3) (small : SmallTrivial G)
    (large : 7 ≤ Fintype.card W) (f : Port ↪ W)
    (copy : ∀ a b,square.Adj a b → G.Adj (f a) (f b)) :
    ∀ a b,G.Adj (f a) (f b) ↔ square.Adj a b := by
  intro a b
  refine ⟨?_,copy a b⟩
  intro e
  have ab : a ≠ b := fun h => e.ne (congrArg f h)
  rcases square_common_two a b ab with yes|⟨x,_,_,ax,_,bx,_⟩
  · exact yes
  · exact (TwinObstruction.no_triangle small (by omega)
      e (copy _ _ bx) (copy _ _ ax).symm (cub _).le (cub _).le (cub _).le).elim

/-- Both the omitted port and the square root are freely prescribed.
Only the existence of a 4-cycle, not inducedness, is required. -/
theorem four_cycle_f2 (t2 : CyclicT2Promise.{u})
    (cub : ∀ x,G.degree x = 3) (small : SmallTrivial G)
    (large : 7 ≤ Fintype.card W) (order : Fintype.card W%6=4)
    (f : Port ↪ W) (copy : ∀ a b,square.Adj a b → G.Adj (f a) (f b))
    (i j : Port) {y : W} (outside : ∀ k,y ≠ f k) (wire : G.Adj (f j) y) :
    FactorOn (omitEdge G (f j) y) (univ.erase (f i)) :=
  square_f2 t2 cub small large order f (square_copy_is_induced cub small large f copy) i j outside wire

/-- Simultaneously remove every crossing edge from the square to its
exterior while retaining all the other ambient edges. -/
def stripWires (G : SimpleGraph W) (f : Port ↪ W) : SimpleGraph W where
  Adj a b := G.Adj a b ∧ ((∃ x,f x = a) ↔ ∃ y,f y = b)
  symm := fun _ _ h => ⟨h.1.symm,h.2.symm⟩
  loopless := fun v h => G.loopless v h.1

/-- One and the same partition avoids all four wires for any vertex
of a square in an order-four-mod-six cubic cyclic-four graph. -/
theorem four_cycle_root_deletion_without_wires (t2 : CyclicT2Promise.{u})
    (cub : ∀ x,G.degree x = 3) (small : SmallTrivial G)
    (large : 7 ≤ Fintype.card W) (order : Fintype.card W%6=4)
    (f : Port ↪ W) (copy : ∀ a b,square.Adj a b → G.Adj (f a) (f b)) (i : Port) :
    FactorOn (stripWires G f) (univ.erase (f i)) := by
  classical
  let pattern := square_copy_is_induced cub small large f copy
  let V := Exterior f
  let p := squarePorts cub small large f pattern
  let H := attach (exteriorGraph G f) square p id
  let e := squareIso cub small large f pattern
  let B := stripWires G f
  have old := Fintype.card_congr e.toEquiv
  have n : Fintype.card (V⊕Port)=Fintype.card V+4 := by
    rw [Fintype.card_sum]
    rfl
  have ca : Fintype.card W = Fintype.card V + 4 := old.symm.trans n
  have vv : 4 < Fintype.card V := by omega
  have cc (z : V⊕Port) : H.degree z = 3 := (degree_iso e z).trans (cub _)
  have ss : SmallTrivial H := small_iso e small
  have oo : Fintype.card (Exterior f ⊕ Port)%6=4 := by rw [old]; exact order
  let K := B.comap e.toEquiv.toEmbedding
  have lkeep (v w : Exterior f) (h : (exteriorGraph G f).Adj v w) :
      K.Adj (Sum.inl v) (Sum.inl w) := by
    change G.Adj v.val w.val ∧ ((∃ x,f x = v.val) ↔ ∃ y,f y = w.val)
    refine ⟨h,?_⟩
    have nv : ¬ ∃ x,f x = v.val := fun ⟨x,eq⟩ => v.property x eq.symm
    have nw : ¬ ∃ y,f y = w.val := fun ⟨y,eq⟩ => w.property y eq.symm
    simp [nv,nw]
  have rkeep (a b : Port) (h : square.Adj a b) : K.Adj (Sum.inr a) (Sum.inr b) := by
    change G.Adj (f a) (f b) ∧ ((∃ x,f x = f a) ↔ ∃ y,f y = f b)
    exact ⟨copy _ _ h,⟨fun _ => ⟨b,rfl⟩,fun _ => ⟨a,rfl⟩⟩⟩
  have fact := square_root_deletion_avoids_all_wires t2 (by decide) oo vv cc ss i
    (square_root_tile i) K lkeep rkeep
  have trans := factor_map e.toEquiv.toEmbedding (H:=B) (fun _ _ h => h) fact
  rw [Finset.map_erase,map_univ_equiv] at trans
  exact trans

#print axioms square_copy_is_induced
#print axioms four_cycle_f2
#print axioms four_cycle_root_deletion_without_wires

#print axioms square_f2

#print axioms square_distinct_contacts

end
end KelmansCactus.AtomicBridge.SquareCap
