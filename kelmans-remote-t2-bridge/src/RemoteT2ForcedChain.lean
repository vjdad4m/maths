import SquareCapFactor

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteT2ForcedChain
open SquareCap (FactorOn IsTile)

variable {V : Type*} [DecidableEq V]

private theorem factor_rest {H : SimpleGraph V} {S T : Finset V}
    {P : Finset (Finset V)} (tiles : ∀ A ∈ P, IsTile H A)
    (apart : ∀ A ∈ P, ∀ B ∈ P, A≠B → Disjoint A B)
    (cover : P.biUnion id=S) (tm : T∈P) :
    FactorOn H (S \ T) := by
  classical
  refine ⟨P.erase T,?_,?_,?_⟩
  · intro A Ains
    exact tiles A (mem_erase.mp Ains).2
  · intro A Ains B Bins ne
    exact apart A (mem_erase.mp Ains).2 B (mem_erase.mp Bins).2 ne
  · ext z
    constructor
    · intro hz
      obtain ⟨A,ha,ham⟩ := mem_biUnion.mp hz
      obtain ⟨at',ap⟩ := mem_erase.mp ha
      exact mem_sdiff.mpr ⟨cover ▸ mem_biUnion.mpr ⟨A,ap,ham⟩,
        fun h=>disjoint_left.mp (apart A ap T tm at') ham h⟩
    · intro hz
      obtain ⟨zs,zt⟩ := mem_sdiff.mp hz
      obtain ⟨A,ha,ham⟩ := mem_biUnion.mp (cover.symm ▸ zs)
      exact mem_biUnion.mpr ⟨A,mem_erase.mpr ⟨fun e=>zt (e ▸ ham),ha⟩,ham⟩

private theorem factor_add {H : SimpleGraph V} {S T : Finset V} (sub : T⊆S)
    (tile : IsTile H T) (h : FactorOn H (S \ T)) :
    FactorOn H S := by
  classical
  obtain ⟨P,tiles,apart,cover⟩ := h
  have d (A : Finset V) (ap : A∈P) : Disjoint A T := by
    apply disjoint_left.mpr
    intro z az tz
    have t : z∈S\T := cover ▸ mem_biUnion.mpr ⟨A,ap,az⟩
    exact (mem_sdiff.mp t).2 tz
  refine ⟨insert T P,?_,?_,?_⟩
  · intro A hA
    rcases mem_insert.mp hA with rfl|ap
    · exact tile
    · exact tiles A ap
  · intro A Ains B Bins ne
    rcases mem_insert.mp Ains with rfl|ap <;> rcases mem_insert.mp Bins with rfl|bp
    · contradiction
    · exact (d B bp).symm
    · exact d A ap
    · exact apart A ap B bp ne
  · ext z
    constructor
    · intro hz
      obtain ⟨A,ha,ham⟩ := mem_biUnion.mp hz
      rcases mem_insert.mp ha with rfl|ap
      · exact sub ham
      · exact (mem_sdiff.mp (cover ▸ mem_biUnion.mpr ⟨A,ap,ham⟩)).1
    · intro hz
      by_cases t : z∈T
      · exact mem_biUnion.mpr ⟨T,mem_insert_self _ _,t⟩
      · obtain ⟨A,ha,ham⟩ := mem_biUnion.mp (cover.symm ▸ mem_sdiff.mpr ⟨hz,t⟩)
        exact mem_biUnion.mpr ⟨A,mem_insert_of_mem ha,ham⟩

/-- Three-vertex chain at a leaf is an exact reduction for P3 factors:
if u's sole available neighbor is w, and w's available neighbors are u
and q, the tile {u,w,q} is forced. No edges outside the support matter. -/
theorem factor_iff_strip_leaf_chain {H : SimpleGraph V} {S : Finset V} {u w q : V}
    (us : u∈S) (ws : w∈S) (qs : q∈S) (uq : u≠q)
    (uw : H.Adj u w) (wq : H.Adj w q)
    (hu : ∀ v∈S,H.Adj u v → v=w)
    (hw : ∀ v∈S,H.Adj w v → v=u ∨ v=q) :
    FactorOn H S ↔ FactorOn H (S \ ({u,w,q}:Finset V)) := by
  classical
  let T : Finset V := {u,w,q}
  have uh := uw.ne
  have wh := wq.ne
  have cardT : T.card=3 := by simp [T,uh,uq,wh]
  have tile : IsTile H T := by
    refine ⟨cardT,w,by simp [T],?_⟩
    intro z zm zw
    simp only [T,mem_insert,mem_singleton] at zm
    rcases zm with rfl|rfl|rfl
    · exact uw.symm
    · contradiction
    · exact wq
  have sub : T⊆S := by
    intro z zm
    simp only [T,mem_insert,mem_singleton] at zm
    rcases zm with rfl|rfl|rfl <;> assumption
  constructor
  · rintro ⟨P,tiles,apart,cover⟩
    obtain ⟨A,ap,um⟩ := mem_biUnion.mp (cover.symm ▸ us)
    obtain ⟨size,m,ma,center⟩ := tiles A ap
    have ASub : A⊆S := fun _ zA=>cover ▸ mem_biUnion.mpr ⟨A,ap,zA⟩
    have mne : m≠u := by
      intro e
      subst m
      have sub' : A⊆({u,w}:Finset V) := by
        intro z zm
        by_cases zz : z=u
        · simp [zz]
        · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (hu z (ASub zm) (center z zm zz))))
      have le := (card_le_card sub').trans card_le_two
      omega
    have mw : m=w := hu m (ASub ma) (center u um mne.symm).symm
    subst m
    have incl : A⊆T := by
      intro z az
      by_cases zw : z=w
      · simp [T,zw]
      · rcases hw z (ASub az) (center z az zw) with rfl|rfl <;> simp [T]
    have eq : A=T := Finset.eq_of_subset_of_card_le incl (by omega)
    rw [eq] at ap
    exact factor_rest tiles apart cover ap
  · exact factor_add sub tile

#print axioms factor_iff_strip_leaf_chain
end KelmansCactus.AtomicBridge.RemoteT2ForcedChain
