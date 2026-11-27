import RemoteVacancyReach

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteVacancySeparation
open RemoteVacancyReach (Packing packing_vertex_count Slides OneCleanup cleanup_lower_bound)
open SquareCap (IsTile)
variable {V : Type*} [DecidableEq V]
abbrev Fam (V : Type*) := Finset (Finset V)

def holes [Fintype V] (P : Fam V) : Finset V := univ\P.biUnion id

def UnitPotential (G : SimpleGraph V) (f : V→Nat) : Prop :=
  ∀ a b,G.Adj a b→f a≤f b+1∧f b≤f a+1

omit [DecidableEq V] in
theorem subpacking {G : SimpleGraph V} {P Q : Fam V}
    (h : Packing G P) (sub : Q⊆P) : Packing G Q :=
  ⟨fun T t=>h.1 T (sub t),fun T t S s ne=>h.2 T (sub t) S (sub s) ne⟩

theorem changed_support [Fintype V] {G : SimpleGraph V} {P F : Fam V}
    (hp : Packing G P) (hf : Packing G F) (full : F.biUnion id=univ) :
    (F\P).biUnion id=(P\F).biUnion id∪holes P := by
  ext x
  constructor
  · intro xn
    obtain ⟨T,tn,tx⟩ := mem_biUnion.mp xn
    obtain ⟨tf,tp⟩ := mem_sdiff.mp tn
    by_cases inP : x∈P.biUnion id
    · obtain ⟨A,ap,ax⟩ := mem_biUnion.mp inP
      have af : A∉F := by
        intro am
        have ne : T≠A := fun e=>tp (e.symm ▸ ap)
        exact disjoint_left.mp (hf.2 T tf A am ne) tx ax
      exact mem_union_left _ (mem_biUnion.mpr ⟨A,mem_sdiff.mpr ⟨ap,af⟩,ax⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_univ _,inP⟩)
  · intro hx
    have inF : x ∈ F.biUnion id := full.symm ▸ mem_univ x
    obtain ⟨T,tf,tx⟩ := mem_biUnion.mp inF
    have nP : T∉P := by
      intro tp
      rcases mem_union.mp hx with left|right
      · obtain ⟨A,ac,ax⟩ := mem_biUnion.mp left
        obtain ⟨ap,af⟩ := mem_sdiff.mp ac
        have ne : T≠A := fun e=>af (e ▸ tf)
        exact disjoint_left.mp (hp.2 T tp A ap ne) tx ax
      · exact (mem_sdiff.mp right).2 (mem_biUnion.mpr ⟨T,tp,tx⟩)
    exact mem_biUnion.mpr ⟨T,mem_sdiff.mpr ⟨tf,nP⟩,tx⟩

theorem old_holes_apart [Fintype V] (P F : Fam V) :
    Disjoint ((P\F).biUnion id) (holes P) := by
  apply disjoint_left.mpr
  intro a ax ay
  obtain ⟨T,tm,ta⟩ := mem_biUnion.mp ax
  exact (mem_sdiff.mp ay).2 (mem_biUnion.mpr ⟨T,(mem_sdiff.mp tm).1,ta⟩)

/-- Unless a tile itself uses the threshold level, a unit-potential
cannot place both a low and a high vertex in that connected tile. -/
theorem tile_on_one_side {G : SimpleGraph V} {f : V→Nat}
    (lip : UnitPotential G f) {T : Finset V} (tile : IsTile G T)
    (k : Nat) (none : ∀ x∈T,f x≠k) :
    ∀ a∈T,f a<k→∀ b∈T,f b<k := by
  obtain ⟨_,c,cm,adj⟩ := tile
  intro a am low b bm
  have clow : f c<k := by
    by_cases ca : a=c
    · rwa [ca] at low
    · have bound := (lip c a (adj a am ca)).1
      have nc := none c cm
      omega
  by_cases bc : b=c
  · exact bc.symm ▸ clow
  · have bd := (lip c b (adj b bm bc)).2
    have nb := none b bm
    omega

def lowFam (P : Fam V) (f : V→Nat) (k : Nat) : Fam V :=
   P.filter (fun T => ∀ x∈T,f x<k)

omit [DecidableEq V] in
theorem low_fam_subset (P : Fam V) (f : V→Nat) (k : Nat) : lowFam P f k⊆P := by
  unfold lowFam
  exact filter_subset _ _

theorem low_cover {G : SimpleGraph V} {P : Fam V} {f : V→Nat}
    (lip : UnitPotential G f) (pack : Packing G P) (k : Nat)
    (none : ∀ x∈P.biUnion id,f x≠k) :
    (lowFam P f k).biUnion id=(P.biUnion id).filter (fun x=>f x<k) := by
  ext x
  constructor
  · intro xx
    obtain ⟨T,t,tx⟩ := mem_biUnion.mp xx
    obtain ⟨tm,all⟩ := mem_filter.mp t
    exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨T,tm,tx⟩,all x tx⟩
  · intro xx
    obtain ⟨xm,xl⟩ := mem_filter.mp xx
    obtain ⟨T,tm,tx⟩ := mem_biUnion.mp xm
    have no : ∀ y∈T,f y≠k := fun y yt=>none y (mem_biUnion.mpr ⟨T,tm,yt⟩)
    have all := tile_on_one_side lip (pack.1 T tm) k no x tx xl
    exact mem_biUnion.mpr ⟨T,mem_filter.mpr ⟨tm,all⟩,tx⟩

/-- A single original hole isolated by a wide potential interval forces
many *original* tiles to change in any full factor. Each empty level
would cut off a region whose old/new tile counts differ by one vertex
modulo three. -/
theorem separation_forces_changes [Fintype V] {G : SimpleGraph V}
    {P F : Fam V} (hp : Packing G P) (hf : Packing G F) (full : F.biUnion id=univ)
    {f : V→Nat} (lip : UnitPotential G f) {a : V} (ah : a∈holes P) (zero : f a=0)
    (d : Nat) (others : ∀ x∈holes P,x≠a→d≤f x) :
    d≤3*(P\F).card+1 := by
  by_contra! tooFar
  let old : Finset V := (P\F).biUnion id
  let new : Finset V := (F\P).biUnion id
  let levels := (range d).erase 0
  have hOld : old.card=3*(P\F).card :=
    packing_vertex_count (subpacking hp sdiff_subset)
  have levelCard : levels.card=d-1 := by
    dsimp [levels]
    rw [card_erase_of_mem (mem_range.mpr (by omega)),card_range]
  have missing : ¬levels⊆old.image f := by
    intro sub
    have b := card_le_card sub
    have c : (old.image f).card≤old.card := card_image_le
    omega
  obtain ⟨k,km,avoid⟩ := Finset.not_subset.mp missing
  have p : 0<k := Nat.pos_of_ne_zero (mem_erase.mp km).1
  have q : k<d := mem_range.mp (mem_erase.mp km).2
  have oldNo : ∀ x∈old,f x≠k := fun x hx eq=>avoid (mem_image.mpr ⟨x,hx,eq⟩)
  have holeNo : ∀ x∈holes P,f x≠k := by
    intro x hx e
    by_cases xA : x=a
    · subst x
      omega
    · have fX := others x hx xA
      omega
  have eq : new=old∪holes P := changed_support hp hf full
  have newNo : ∀ x∈new,f x≠k := by
    intro x hx
    exact (mem_union.mp (eq ▸ hx)).elim (oldNo x) (holeNo x)
  have single : (holes P).filter (fun x=>f x<k)={a} := by
    ext x
    constructor
    · intro hx
      obtain ⟨h,lt⟩ := mem_filter.mp hx
      apply mem_singleton.mpr
      by_contra ne
      have e := others x h ne
      omega
    · intro m
      obtain rfl:=mem_singleton.mp m
      exact mem_filter.mpr ⟨ah,by omega⟩
  have oldSame := low_cover lip (subpacking hp (Q:=P\F) sdiff_subset) k oldNo
  have newSame := low_cover lip (subpacking hf (Q:=F\P) sdiff_subset) k newNo
  let O := lowFam (P\F) f k
  let N := lowFam (F\P) f k
  have dis : Disjoint (old.filter (fun x=>f x<k)) ({a}:Finset V) := by
    rw [←single]
    exact (old_holes_apart P F).mono (filter_subset _ _) (filter_subset _ _)
  have filt : new.filter (fun x=>f x<k) =
      old.filter (fun x=>f x<k) ∪ {a} := by rw [eq,filter_union,single]
  have oldCount : (O.biUnion id).card=3*O.card :=
    packing_vertex_count (subpacking hp ((low_fam_subset _ _ _).trans sdiff_subset))
  have newCount : (N.biUnion id).card=3*N.card :=
    packing_vertex_count (subpacking hf ((low_fam_subset _ _ _).trans sdiff_subset))
  have gap : (N.biUnion id).card=(O.biUnion id).card+1 := by
    rw [newSame,oldSame,filt,card_union_of_disjoint dis,card_singleton]
  omega

/-- This applies even to nonmonotone slides; no fixed final factor or
choice of intermediate board is imposed in the bound. -/
theorem one_cleanup_separation_bound [Fintype V] {G : SimpleGraph V}
    {P Q F : Fam V} (hp : Packing G P) (hf : Packing G F) (full : F.biUnion id=univ)
    {f : V→Nat} (lip : UnitPotential G f) {a : V} (ah : a∈holes P) (zero : f a=0)
    (d : Nat) (others : ∀ x∈holes P,x≠a→d≤f x)
    {n : Nat} (steps : Slides n P Q) (clean : OneCleanup Q F) :
    d≤3*(n+1)+1 := by
  have changes := separation_forces_changes hp hf full lip ah zero d others
  have keep := cleanup_lower_bound steps clean
  have split := card_sdiff_add_card_inter P F
  omega

#print axioms separation_forces_changes
#print axioms one_cleanup_separation_bound
end KelmansCactus.AtomicBridge.RemoteVacancySeparation
