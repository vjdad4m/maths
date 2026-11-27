import SevenBudget
import Mathlib.Tactic.FinCases

namespace Graffiti384b.Seven
open SimpleGraph Finset HighEar
abbrev Id := Fin 7
def arrows : Finset (Id × Id) :=
  {(0,1),(0,3),(1,3),(1,4),(3,4),(2,3),(2,4),(2,5),(2,6),(3,5),(3,6),(4,5),(4,6)}
def K : SimpleGraph Id where
  Adj i j := (i,j)∈arrows ∨ (j,i)∈arrows
  symm := fun _ _ h => h.symm
  loopless := by unfold Irreflexive; decide
instance : DecidableRel K.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
def inner : Finset Id := {0,1,2}
def spines : Finset Id := {3,4}
def tips : Finset Id := {5,6}
def border := spines∪tips
def pins (a : Id) := insert 1 (spines∪tips.erase a)
def lost (v : Id) := (pairs K (K.neighborFinset v)).filter (fun E => ¬Disjoint E inner)
theorem finite_geometry :
    Disjoint spines tips ∧ border∪inner=univ ∧ Disjoint border inner ∧
    spines.card=2 ∧ tips.card=2 ∧ (∀ i∈spines,nbr K i border=3 ∧ (lost i).card≤5) ∧
    (∀ i∈tips,nbr K i border=2 ∧ (lost i).card≤2) ∧
    (∀ a∈tips,(pins a).card=4 ∧ TwoDominates K (pins a)) := by unfold TwoDominates; decide

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
structure Pattern where
  f : Id ↪ V
  induced : ∀ i j,H.Adj (f i) (f j) ↔ K.Adj i j
  closed : ∀ i∈inner,∀ w,H.Adj (f i) w → w∈univ.map f

namespace Pattern
variable {H} (M : Pattern H)
def exterior := (univ.map M.f)ᶜ
omit [Fintype V] [DecidableEq V] in
theorem restrict_nbr (i : Id) (B : Finset Id) : nbr H (M.f i) (B.map M.f)=nbr K i B := by
  have eq : (B.map M.f).filter (H.Adj (M.f i))=(B.filter (K.Adj i)).map M.f := by
    ext v; constructor
    · intro h; obtain ⟨j,jm,rfl⟩ := mem_map.mp (mem_filter.mp h).1
      exact mem_map.mpr ⟨j,mem_filter.mpr ⟨jm,(M.induced ..).mp (mem_filter.mp h).2⟩,rfl⟩
    · intro h; obtain ⟨j,jm,rfl⟩ := mem_map.mp h
      exact mem_filter.mpr ⟨mem_map.mpr ⟨j,(mem_filter.mp jm).1,rfl⟩,(M.induced ..).mpr (mem_filter.mp jm).2⟩
  exact (congrArg card eq).trans (card_map ..)

omit [Fintype V] [DecidableEq V] [DecidableRel H.Adj] in
private theorem member (i : Id) (B : Finset Id) : M.f i∈B.map M.f ↔ i∈B := mem_map' ..

omit [DecidableRel H.Adj] in
theorem no_inner {w : V} (wm : w∈M.exterior) {i : Id} (inside : i∈inner) : ¬H.Adj w (M.f i) :=
  fun edge => mem_compl.mp wm (M.closed i inside w edge.symm)

open private ThreeChoice.pair_turan from ThreeGeometry33
private theorem turan {v : V} {B : Finset V} (free : H.CliqueFree 5) (sub : B⊆H.neighborFinset v)
    (b : B.card≤10) : (pairs H B).card≤RankTable.cap B.card 3 := by
  have no (Q : Finset V) (qb : Q⊆B) (cl : H.IsNClique (3+1) Q) :=
    free (insert v Q) (cl.insert (fun y ym => (H.mem_neighborFinset ..).mp (sub (qb ym))))
  have up := ThreeChoice.pair_turan H B (by decide : 0<3) no
  exact up.trans_eq (RankTable.cap_table ⟨B.card,by omega⟩ ⟨3,by decide⟩ (by decide))

/-- Deleting the three closed vertices costs only the counted template triangles. -/
theorem boundary_score (free : H.CliqueFree 5) (i : Id) :
    let d := nbr H (M.f i) M.exterior+nbr K i border
    d≤10 → trianglesAt H (M.f i)≤(lost i).card+RankTable.cap d 3 := by
  classical
  let v := M.f i
  let N := H.neighborFinset v
  let Z := inner.map M.f
  let B := N\Z
  let f := fun E : Finset Id => E.map M.f
  have cover : pairs H N⊆(lost i).image f ∪ pairs H B := by
    intro E em
    obtain ⟨y,yn,z,zn,yz,rfl⟩ := (pair_mem H).mp em
    have lift (a b : V) (an : a∈N) (bn : b∈N) (ab : H.Adj a b) (az : a∈Z) :
        {a,b}∈(lost i).image f := by
      obtain ⟨j,jm,rfl⟩ := mem_map.mp az
      obtain ⟨k,_,rfl⟩ := mem_map.mp (M.closed j jm b ab)
      have ij := (M.induced ..).mp ((H.mem_neighborFinset ..).mp an)
      have ik := (M.induced ..).mp ((H.mem_neighborFinset ..).mp bn)
      have jk := (M.induced ..).mp ab
      refine mem_image.mpr ⟨{j,k},mem_filter.mpr ⟨(pair_mem K).mpr ⟨j,(K.mem_neighborFinset ..).mpr ij,k,(K.mem_neighborFinset ..).mpr ik,jk,rfl⟩,
        fun dis => disjoint_left.mp dis (mem_insert_self ..) jm⟩,?_⟩
      simp [f]
    by_cases yy : y∈Z
    · exact mem_union_left _ (lift y z yn zn yz yy)
    by_cases zz : z∈Z
    · exact mem_union_left _ (pair_comm z y ▸ lift z y zn yn yz.symm zz)
    exact mem_union_right _ ((pair_mem H).mpr ⟨y,mem_sdiff.mpr ⟨yn,yy⟩,z,mem_sdiff.mpr ⟨zn,zz⟩,yz,rfl⟩)
  have ds : Disjoint M.exterior (border.map M.f) := disjoint_left.mpr (by
    intro w wm am; obtain ⟨j,_,rfl⟩ := mem_map.mp am
    exact mem_compl.mp wm (mem_map.mpr ⟨j,mem_univ _,rfl⟩))
  have eq : B=M.exterior.filter (H.Adj v)∪(border.map M.f).filter (H.Adj v) := by
    ext w; simp only [B,N,mem_sdiff,H.mem_neighborFinset,mem_union,mem_filter]
    by_cases outside : w∈M.exterior
    · have no {L : Finset Id} : w∉L.map M.f := by
        intro m; obtain ⟨j,_,rfl⟩ := mem_map.mp m; exact mem_compl.mp outside (mem_map.mpr ⟨j,mem_univ _,rfl⟩)
      simp [outside,no,Z]
    · have m : w∈univ.map M.f := not_not.mp (fun off => outside (mem_compl.mpr off))
      obtain ⟨j,_,rfl⟩ := mem_map.mp m
      have part : j∈border ↔ j∉inner := (show ∀ l : Id,l∈border ↔ l∉inner by decide) j
      simp [outside,Z,M.member,part,and_comm]
  have sz : B.card=nbr H v M.exterior+nbr K i border := by
    rw [eq,card_union_of_disjoint (ds.mono (filter_subset ..) (filter_subset ..)),←M.restrict_nbr i border]; rfl
  dsimp only
  intro small
  have up := (card_le_card cover).trans (card_union_le ..)
  have im := card_image_le (s:=lost i) (f:=f)
  have b := turan free (v:=v) (B:=B) sdiff_subset (by rw [sz]; exact small)
  rw [sz] at b
  change (pairs H N).card≤_
  exact up.trans (Nat.add_le_add im b)

end Pattern
end Graffiti384b.Seven
#print axioms Graffiti384b.Seven.finite_geometry
#print axioms Graffiti384b.Seven.Pattern.boundary_score
