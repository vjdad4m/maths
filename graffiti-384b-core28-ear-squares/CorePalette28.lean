import ShoreSample28
import ShoreEquality28
namespace Graffiti384b.Core28
open Finset SimpleGraph JointRank
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def lowPalette := types G ∩ Icc 1 6
private def slots (A : Finset ℕ) (c : ℕ) := (A.filter (·≤c)).card+(c-6)
private def degreeAt (A : Finset ℕ) (r i : ℕ) :=
  ((List.range 10).find? (fun d => decide (i<slots A (RankTable.cap d r)))).getD 10
private def passing (A : Finset ℕ) (r : ℕ) := r=3 ∧ 1∈A ∧ 5≤A.card
private instance (A : Finset ℕ) (r : ℕ) : Decidable (passing A r) := by unfold passing; infer_instance

private theorem floor_check (A : Finset ℕ) (r i : ℕ) :
    degreeAt A r i ≤ 10 ∧ (∀ d : Fin 10, d.val < degreeAt A r i → slots A (RankTable.cap d r) ≤ i) := by
  unfold degreeAt
  cases eq : (List.range 10).find? (fun d => decide (i<slots A (RankTable.cap d r))) with
  | none =>
    simp only [Option.getD_none,le_refl,true_and]
    intro d _
    simpa using (List.find?_range_eq_none.mp eq d d.isLt)
  | some x =>
    obtain ⟨_,xm,prior⟩ := List.find?_range_eq_some.mp eq
    simp only [Option.getD_some]
    exact ⟨(List.mem_range.mp xm).le,fun d lt => by simpa using prior d lt⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private theorem rows : ∀ A∈(Icc 1 6 : Finset ℕ).powerset,∀ r∈({2,3}:Finset ℕ),
    ¬passing A r → (∑ i∈range 28,FiniteRange.badCount 28 10 (degreeAt A r i))<4*(28:ℕ).choose 10 := by
  unfold passing degreeAt slots RankTable.cap FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide

private theorem count_slots (p : ∀ v,0<trianglesAt G v) (fi : Function.Injective (trianglesAt G))
    (v : V) (c : ℕ) (sc : trianglesAt G v≤c) :
    rank univ (trianglesAt G) v<slots (lowPalette G) c := by
  classical
  let S := univ.filter (fun w => trianglesAt G w<trianglesAt G v)
  let B := insert v S
  have vs : v∉S := by simp [S]
  have cover : B.image (trianglesAt G)⊆((lowPalette G).filter (·≤c))∪Icc 7 c := by
    intro s sm
    obtain ⟨w,wm,rfl⟩ := mem_image.mp sm
    have le : trianglesAt G w≤c := by
      rcases mem_insert.mp wm with rfl|lo
      · exact sc
      · exact (mem_filter.mp lo).2.le.trans sc
    by_cases small : trianglesAt G w≤6
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_inter.mpr ⟨mem_image_of_mem _ (mem_univ w),mem_Icc.mpr ⟨p w,small⟩⟩,le⟩)
    · exact mem_union_right _ (mem_Icc.mpr ⟨by omega,le⟩)
  have lim := (card_le_card cover).trans (card_union_le _ _)
  rw [card_image_of_injective _ fi,show B.card=S.card+1 from card_insert_of_not_mem vs,Nat.card_Icc] at lim
  change S.card<_+(c-6)
  omega

theorem density_profile (pos : ∀ v,0<trianglesAt G v) (fi : Function.Injective (trianglesAt G))
    (n : Fintype.card V=28) (hf : Fintype.card V≤2*gamma G) {r : ℕ} (rm : r∈({2,3}:Finset ℕ))
    (cf : G.CliqueFree (r+2)) : r=3 ∧ 1∈lowPalette G ∧ 5≤(lowPalette G).card := by
  classical
  let A := lowPalette G
  let rk := rank univ (trianglesAt G)
  change passing A r
  by_contra no
  have sub : A⊆Icc 1 6 := inter_subset_right
  have finish := rows A (mem_powerset.mpr sub) r rm no
  have lower (v : V) : degreeAt A r (rk v)≤G.degree v := by
    by_contra! lt
    have tabD := floor_check A r (rk v)
    have d := tabD.2 ⟨G.degree v,by omega⟩ lt
    change slots A (RankTable.cap (G.degree v) r)≤rk v at d
    have rpos : 0<r := by simp only [mem_insert,mem_singleton] at rm; omega
    have rsmall : r<10 := by simp only [mem_insert,mem_singleton] at rm; omega
    have loc := RankTuran.local_turan G r rpos cf v
    have tab := RankTable.cap_table ⟨G.degree v,by omega⟩ ⟨r,rsmall⟩ rpos
    change (turanGraph (G.degree v) r).edgeFinset.card=RankTable.cap (G.degree v) r at tab
    exact (Nat.not_lt_of_ge d) (count_slots G pos fi v _ (loc.trans_eq tab))
  have b := degree_budget G 28 10 n (n ▸ hf) (fun v => degreeAt A r (rk v)) lower
  have sum := sum_by_rank univ (trianglesAt G) fi.injOn (fun i => FiniteRange.badCount 28 10 (degreeAt A r i))
  rw [card_univ,n] at sum
  rw [show (∑ v,FiniteRange.badCount 28 10 (degreeAt A r (rk v)))=_ from sum] at b
  omega
end Graffiti384b.Core28
#print axioms Graffiti384b.Core28.density_profile
