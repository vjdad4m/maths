import ContactRepair

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge
open PathSlides Substitute
noncomputable section
variable {V X : Type*} [DecidableEq V] [DecidableEq X]
variable {G : SimpleGraph V} {H : SimpleGraph X}

/-- A factor pulls back across any equivalence reflecting all used edges. -/
theorem factor_pullback [Fintype V] [Fintype X] (e : V≃X) (reflect : ∀ a b,H.Adj (e a) (e b)→G.Adj a b)
    (has : KelmansStarter.HasP3Factor H) : KelmansStarter.HasP3Factor G := by
  obtain ⟨P,tile,apart,cov⟩ := has
  let emb : Finset X↪Finset V := ⟨map e.symm.toEmbedding,map_injective _⟩
  refine ⟨P.map emb,?_,?_,?_⟩
  · intro s sm
    obtain ⟨t,tm,rfl⟩ := mem_map.mp sm
    obtain ⟨sz,c,ct,links⟩ := tile t tm
    refine ⟨(card_map _).trans sz,e.symm c,mem_map.mpr ⟨c,ct,rfl⟩,?_⟩
    intro w wm ne
    obtain ⟨u,ut,rfl⟩ := mem_map.mp wm
    apply reflect
    simpa using links u ut (fun h=>ne (congrArg e.symm h))
  · intro t tm u um ne
    obtain ⟨s,sm,rfl⟩ := mem_map.mp tm
    obtain ⟨r,rm,rfl⟩ := mem_map.mp um
    apply disjoint_left.mpr
    intro v vt vu
    obtain ⟨x,xs,rfl⟩ := mem_map.mp vt
    obtain ⟨y,yr,eq⟩ := mem_map.mp vu
    exact disjoint_left.mp (apart _ sm _ rm (fun h=>ne (congrArg emb h)))
      xs ((e.symm.injective eq) ▸ yr)
  · apply eq_univ_of_forall
    intro v
    obtain ⟨t,tm,et⟩ := mem_biUnion.mp (cov.symm ▸ mem_univ (e v))
    exact mem_biUnion.mpr ⟨emb t,mem_map.mpr ⟨t,tm,rfl⟩,mem_map.mpr ⟨e v,et,e.symm_apply_apply v⟩⟩

/-- A factor with a tile consisting of all auxiliary vertices restricts
to an old factor. Here the condition states that every vertex off that
tile is old, not only that the tile has size three. -/
theorem factor_off_auxiliary_tile [Fintype V] [Fintype X] (e : V↪X)
    (reflect : ∀ a b,H.Adj (e a) (e b)→G.Adj a b)
    {P : Parts X} (tile : ∀ t∈P,KelmansStarter.IsTile H t)
    (apart : ∀ t∈P,∀ s∈P,t≠s→Disjoint t s) (cov : P.biUnion id=univ)
    {T : Finset X} (tm : T∈P)
    (rest : ∀ x,x∉T ↔ ∃ a,e a=x) : KelmansStarter.HasP3Factor G := by
  classical
  let D := {x : X // x∉T}
  let iso : V≃D := Equiv.ofBijective
    (fun a=>⟨e a,(rest _).mpr ⟨a,rfl⟩⟩)
    ⟨fun a b eq=>e.injective (congrArg Subtype.val eq),
      fun ⟨x,h⟩=>let ⟨a,ha⟩ := (rest _).mp h; ⟨a,Subtype.ext ha⟩⟩
  let R := P.erase T
  have localP : ∀ t∈R,∀ x∈t,x∉T := by
    intro t ht x hx
    obtain ⟨ne,orig⟩ := mem_erase.mp ht
    exact fun xt=>disjoint_left.mp (apart _ orig _ tm ne) hx xt
  let f (t : Finset X) : Finset D := t.preimage Subtype.val Subtype.val_injective.injOn
  have ev {t : Finset X} {x : D} : x∈f t ↔ x.val∈t := mem_preimage
  let K : SimpleGraph D := H.comap Subtype.val
  have fact : KelmansStarter.HasP3Factor K := by
    let Q := R.image f
    have lift {t : Finset X} {x : X} (ht : t∈R) (xt : x∈t) : x∉T := localP t ht x xt
    have preEq {t : Finset X} (ht : t∈R) :
        (f t).map (Function.Embedding.subtype (fun x : X=>x∉T))=t := by
      ext x
      constructor
      · intro hx
        obtain ⟨u,um,rfl⟩ := mem_map.mp hx
        exact ev.mp um
      · intro hx
        exact mem_map.mpr ⟨⟨x,lift ht hx⟩,ev.mpr hx,rfl⟩
    refine ⟨Q,?_,?_,?_⟩
    · intro s sm
      obtain ⟨t,ht,rfl⟩ := mem_image.mp sm
      obtain ⟨sz,c,ct,star⟩ := tile t (mem_erase.mp ht).2
      let d : D := ⟨c,lift ht ct⟩
      have cs : (f t).card=3 := (card_map _).symm.trans ((congrArg Finset.card (preEq ht)).trans sz)
      refine ⟨cs,d,ev.mpr ct,?_⟩
      intro z zm ne
      exact star z.val (ev.mp zm) (fun h=>ne (Subtype.ext h))
    · intro s sm t tm' ne
      obtain ⟨u,um,rfl⟩ := mem_image.mp sm
      obtain ⟨v,vm,rfl⟩ := mem_image.mp tm'
      apply disjoint_left.mpr
      intro z zu zv
      exact disjoint_left.mp (apart _ (mem_erase.mp um).2 _ (mem_erase.mp vm).2
        (fun h=>ne (congrArg f h))) (ev.mp zu) (ev.mp zv)
    · apply eq_univ_of_forall
      intro x
      obtain ⟨t,tm,xt⟩ := mem_biUnion.mp (cov.symm ▸ mem_univ x.val)
      have nt : t≠T := fun h=>x.property (h ▸ xt)
      exact mem_biUnion.mpr ⟨f t,mem_image.mpr ⟨t,mem_erase.mpr ⟨nt,tm⟩,rfl⟩,ev.mpr xt⟩
  exact factor_pullback (H:=K) iso reflect fact

omit [DecidableEq V] in
/-- A tile with one auxiliary vertex leaves adjacent old vertices if
any two of that auxiliary vertex's old contacts are adjacent after the
old edges are restored. -/
theorem aux_tile_has_adjacent_pair (e : V↪X)
    (reflect : ∀ a b,H.Adj (e a) (e b)→G.Adj a b)
    {t : Finset X} (tile : KelmansStarter.IsTile H t)
    {x : X} (xt : x∈t) (old : ∀ y∈t,y≠x→∃ v,e v=y)
    (contact : ∀ a b,a≠b→H.Adj x (e a)→H.Adj x (e b)→G.Adj a b) :
    ∃ a b,G.Adj a b ∧ e a∈t ∧ e b∈t := by
  obtain ⟨a,b,c,ab,ac,bc,abE,bcE,eq⟩ := (Kelmans.tile_iff_path H t tile.1).mp tile.2
  have aT : a∈t := by simp [eq]
  have bT : b∈t := by simp [eq]
  have cT : c∈t := by simp [eq]
  simp only [eq,mem_insert,mem_singleton] at xt
  rcases xt with rfl|rfl|rfl
  · obtain ⟨u,rfl⟩ := old b bT ab.symm
    obtain ⟨v,rfl⟩ := old c cT ac.symm
    exact ⟨u,v,reflect _ _ bcE,bT,cT⟩
  · obtain ⟨u,rfl⟩ := old a aT ab
    obtain ⟨v,rfl⟩ := old c cT bc.symm
    exact ⟨u,v,contact _ _ (fun h=>ac (congrArg e h)) abE.symm bcE,aT,cT⟩
  · obtain ⟨u,rfl⟩ := old a aT ac
    obtain ⟨v,rfl⟩ := old b bT bc
    exact ⟨u,v,reflect _ _ abE,aT,bT⟩

#print axioms factor_off_auxiliary_tile
#print axioms aux_tile_has_adjacent_pair
end
end KelmansCactus.AtomicBridge
