import PentagonCase
import TwinObstruction

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.PentagonCap
open PentagonProfile (Port)
open SquareCap (SmallTrivial boundary CyclicT2Promise FactorOn factor_map omitEdge)
noncomputable section

universe u
variable {W : Type u} [Fintype W] [DecidableEq W]
variable {G : SimpleGraph W} [DecidableRel G.Adj]

def pentagon : SimpleGraph Port where
  Adj a b := (a.val+1)%5=b.val ∨ (b.val+1)%5=a.val
  symm := by intro _ _ h; exact h.elim Or.inr Or.inl
  loopless := by
    have data : ∀ a : Port, ¬ ((a.val+1)%5=a.val ∨ (a.val+1)%5=a.val) := by decide
    exact data

instance : DecidableRel pentagon.Adj := fun a b =>
  inferInstanceAs (Decidable ((a.val+1)%5=b.val ∨ (b.val+1)%5=a.val))

private theorem pentagon_two_neighbors (i : Port) :
    ∃ a b : Port, a ≠ b ∧ ∀ j, pentagon.Adj i j ↔ j = a ∨ j = b := by
  revert i
  decide

private theorem pentagon_common_one (i j : Port) (different : i ≠ j) :
    pentagon.Adj i j ∨ ∃ a : Port, pentagon.Adj i a ∧ pentagon.Adj j a := by
  revert i j
  decide

abbrev Exterior (f : Port ↪ W) := {v : W // ∀ j, v ≠ f j}

private theorem ext_unique (cub : ∀ x,G.degree x=3) (f : Port ↪ W)
    (induced : ∀ a b,G.Adj (f a) (f b) ↔ pentagon.Adj a b) (i : Port) :
    ∃! w : W, (∀ j, w ≠ f j) ∧ G.Adj (f i) w := by
  obtain ⟨a,b,ab,spec⟩ := pentagon_two_neighbors i
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
    (induced : ∀ a b,G.Adj (f a) (f b) ↔ pentagon.Adj a b) (i : Port) : Exterior f :=
  ⟨(ext_unique cub f induced i).exists.choose,(ext_unique cub f induced i).exists.choose_spec.1⟩

private theorem portOf_adj (cub : ∀ x,G.degree x=3) (f : Port ↪ W)
    (induced : ∀ a b,G.Adj (f a) (f b) ↔ pentagon.Adj a b) (i : Port) :
    G.Adj (f i) (portOf cub f induced i).val :=
  (ext_unique cub f induced i).exists.choose_spec.2

private theorem eq_port_of_adj (cub : ∀ x,G.degree x=3) (f : Port ↪ W)
    (induced : ∀ a b,G.Adj (f a) (f b) ↔ pentagon.Adj a b)
    (i : Port) (v : Exterior f) (h : G.Adj (f i) v.val) : v = portOf cub f induced i := by
  apply Subtype.ext
  rcases ext_unique cub f induced i with ⟨q,hq,all⟩
  exact (all _ ⟨v.property,h⟩).trans (all _
    ⟨(portOf cub f induced i).property,portOf_adj cub f induced i⟩).symm

/-- An ambient graph of girth at least five has distinct contacts
at the five corners of its pentagon (after applying cubicity). -/
theorem pentagon_distinct_contacts (cub : ∀ x,G.degree x=3)
    (small : SmallTrivial G) (clean : NoFourCycle G)
    (f : Port ↪ W) (induced : ∀ a b,G.Adj (f a) (f b) ↔ pentagon.Adj a b) :
    Function.Injective (portOf cub f induced) := by
  intro i j e
  by_contra ne
  let w := (portOf cub f induced i).val
  have large : 5≤Fintype.card W := by
    have card := Fintype.card_le_of_injective f f.injective
    simpa using card
  have hi : G.Adj (f i) w := portOf_adj cub f induced i
  have hj : G.Adj (f j) w := by
    change G.Adj (f j) (portOf cub f induced i).val
    rw [e]
    exact portOf_adj cub f induced j
  rcases pentagon_common_one i j ne with adjacent | ⟨a,ia,ja⟩
  · exact TwinObstruction.no_triangle small large ((induced i j).mpr adjacent)
      hj hi.symm (cub _).le (cub _).le (cub _).le
  · have notw : f a ≠ w := ((portOf cub f induced i).property a).symm
    rcases clean _ _ _ _ ((induced _ _).mpr ia) ((induced _ _).mpr ja).symm hj hi.symm with ij|aw
    · exact ne (f.injective ij)
    · exact notw aw

private def pentagonPorts (cub : ∀ x,G.degree x=3) (small : SmallTrivial G)
    (clean : NoFourCycle G) (f : Port ↪ W)
    (pattern : ∀ a b,G.Adj (f a) (f b) ↔ pentagon.Adj a b) : Port ↪ Exterior f :=
  ⟨portOf cub f pattern,pentagon_distinct_contacts cub small clean f pattern⟩

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

private def pentagonIso (cub : ∀ x,G.degree x=3) (small : SmallTrivial G)
    (clean : NoFourCycle G) (f : Port ↪ W)
    (pattern : ∀ a b,G.Adj (f a) (f b) ↔ pentagon.Adj a b) :
    attach (exteriorGraph G f) pentagon (pentagonPorts cub small clean f pattern) id ≃g G := by
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

private theorem small4_iso {A B : Type*} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {K : SimpleGraph B} (e : H ≃g K) (h : SmallFourTrivial K) :
    SmallFourTrivial H := by
  intro c near
  rw [boundary_iso e] at near
  obtain ⟨b,cut⟩ := h (c ∘ e.symm) near
  refine ⟨b,?_⟩
  intro x y z hx hy hz
  rcases cut (e x) (e y) (e z) (by simpa using hx) (by simpa using hy) (by simpa using hz) with xy|xz|yz
  · exact Or.inl (e.toEquiv.injective xy)
  · exact Or.inr (Or.inl (e.toEquiv.injective xz))
  · exact Or.inr (Or.inr (e.toEquiv.injective yz))

private theorem no4_iso {A B : Type*} {H : SimpleGraph A} {K : SimpleGraph B}
    (e : H ≃g K) (clean : NoFourCycle K) : NoFourCycle H := by
  intro a b c d ab bc cd da
  rcases clean _ _ _ _ (e.map_adj_iff.mpr ab) (e.map_adj_iff.mpr bc)
     (e.map_adj_iff.mpr cd) (e.map_adj_iff.mpr da) with ac|bd
  · exact Or.inl (e.toEquiv.injective ac)
  · exact Or.inr (e.toEquiv.injective bd)

/-- A copied 5-cycle is induced in a cyclic-four cubic graph since
any inserted diagonal would close a triangle. -/
theorem pentagon_copy_is_induced (cub : ∀ x,G.degree x = 3) (small : SmallTrivial G)
    (f : Port ↪ W) (copy : ∀ a b,pentagon.Adj a b → G.Adj (f a) (f b)) :
    ∀ a b,G.Adj (f a) (f b) ↔ pentagon.Adj a b := by
  intro a b
  refine ⟨?_,copy a b⟩
  intro e
  have ab : a ≠ b := fun h => e.ne (congrArg f h)
  have large : 5≤Fintype.card W := by
    have card := Fintype.card_le_of_injective f f.injective
    simpa using card
  rcases pentagon_common_one a b ab with yes|⟨x,ax,bx⟩
  · exact yes
  · exact (TwinObstruction.no_triangle small large
      e (copy _ _ bx) (copy _ _ ax).symm (cub _).le (cub _).le (cub _).le).elim

/-- A fully ambient form: choose a 5-cycle and root 0. The target
may omit any edges other than the old exterior graph, the path
1–2–3–4, and the two endpoint wires. This proves F2, in particular,
when its omitted edge is one of the other three pentagon wires. -/
theorem ambient_pentagon_root_case (t2 : CyclicT2Promise.{u})
    (cub : ∀ x,G.degree x=3) (small : SmallTrivial G) (small4 : SmallFourTrivial G)
    (clean : NoFourCycle G) (order : Fintype.card W%6=4)
    (f : Port ↪ W) (copy : ∀ a b,pentagon.Adj a b → G.Adj (f a) (f b))
    (safe : ∀ u v : Exterior f,G.Adj (f 1) u.val → G.Adj (f 4) v.val → ¬G.Adj u.val v.val)
    (H : SimpleGraph W)
    (path12 : H.Adj (f 1) (f 2)) (path23 : H.Adj (f 2) (f 3))
    (path34 : H.Adj (f 3) (f 4))
    (wire1 : ∀ u : Exterior f,G.Adj (f 1) u.val → H.Adj u.val (f 1))
    (wire4 : ∀ u : Exterior f,G.Adj (f 4) u.val → H.Adj u.val (f 4))
    (old : ∀ u v : Exterior f,G.Adj u.val v.val → H.Adj u.val v.val) :
    FactorOn H (univ.erase (f 0)) := by
  classical
  let pattern := pentagon_copy_is_induced cub small f copy
  let p := pentagonPorts cub small clean f pattern
  let e := pentagonIso cub small clean f pattern
  let resid := H.comap e.toEquiv.toEmbedding
  have card := Fintype.card_congr e.toEquiv
  have orderM : Fintype.card (Exterior f ⊕ Port)%6=4 := card.symm ▸ order
  have geometry := small_iso e small
  have four := small4_iso e small4
  have cleanM := no4_iso e clean
  have cubicM (x : Exterior f ⊕ Port) :
      (attach (exteriorGraph G f) pentagon p id).degree x=3 :=
    (degree_iso e x).trans (cub (e x))
  have safeM : ¬ (exteriorGraph G f).Adj (p 1) (p 4) :=
    safe (p 1) (p 4) (portOf_adj cub f pattern 1) (portOf_adj cub f pattern 4)
  have repl := pentagon_root_case_of_cyclic5 t2 geometry four cleanM cubicM orderM
    safeM (by decide : pentagon.Adj 2 3) resid path12 path23 path34
    (wire1 _ (portOf_adj cub f pattern 1)) (wire4 _ (portOf_adj cub f pattern 4)) old
  have mapped := factor_map e.toEquiv.toEmbedding (H:=H) (fun _ _ h=>h) repl
  rw [Finset.map_erase,map_univ_equiv] at mapped
  exact mapped

#print axioms pentagon_distinct_contacts
#print axioms ambient_pentagon_root_case

end
end KelmansCactus.AtomicBridge.PentagonCap
