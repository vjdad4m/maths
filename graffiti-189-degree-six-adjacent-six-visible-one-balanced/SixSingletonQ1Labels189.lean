import SixSingletonQ1TagScore189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset ArticulationPair
open private Cmp from SixCutFar189
open private Vis vis_sub from AdjacentCutFiveComponents189
open private Dark Common from SixSingletonGeometry189
open private nearBal from SixSingletonFiveGeometry189
open private EA EB from SixSingletonMultiZeroGeom189
open private Shore shore_off from AdjacentCutFiveActual189
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b s z : V} {D : Cmp G a b}
set_option linter.unusedSectionVars false

def widenQ1 {n : ℕ} {k : ℕ} (h : k≤n) (i : Fin k) : Fin n := ⟨i.val,lt_of_lt_of_le i.isLt h⟩
theorem widenQ1_injective {n k : ℕ} (h : k≤n) : Function.Injective (widenQ1 h) :=
  fun _ _ e=>Fin.ext (congrArg (@Fin.val n) e)

def addQ1 (f : Fin 9→V) (z : V) (i : Fin 10) : V :=
  if h : i.val<9 then f ⟨i.val,h⟩ else z

theorem addQ1_lower (f : Fin 9→V) (z : V) (i : Fin 9) :
    addQ1 f z (widenQ1 (by decide : 9≤10) i)=f i := by simp [addQ1,widenQ1,i.isLt]

theorem addQ1_last (f : Fin 9→V) (z : V) : addQ1 f z 9=z := by rfl

theorem addQ1_image (f : Fin 9→V) (z : V) :
    univ.image (addQ1 f z)=insert z (univ.image f) := by
  ext w
  simp only [mem_image,mem_univ,true_and,mem_insert]
  constructor
  · rintro ⟨i,rfl⟩
    by_cases h : i.val<9
    · right
      exact ⟨⟨i.val,h⟩,by simp [addQ1,h]⟩
    left
    simp [addQ1,h]
  rintro (rfl|⟨i,rfl⟩)
  · exact ⟨9,rfl⟩
  exact ⟨widenQ1 (by decide : 9≤10) i,addQ1_lower f z i⟩

theorem addQ1_inj (f : Fin 9→V) (z : V) (inj : Function.Injective f)
    (fresh : z∉univ.image f) : Function.Injective (addQ1 f z) := by
  intro i j e
  apply Fin.ext
  by_cases li : i.val<9 <;> by_cases lj : j.val<9
  · exact congrArg (@Fin.val 9) (inj (by simpa [addQ1,li,lj] using e))
  · exact (fresh (mem_image.mpr ⟨⟨i.val,li⟩,mem_univ _,by simpa [addQ1,li,lj] using e⟩)).elim
  · exact (fresh (mem_image.mpr ⟨⟨j.val,lj⟩,mem_univ _,by simpa [addQ1,li,lj] using e.symm⟩)).elim
  omega

theorem q1_exterior_coverage (F : SixVisibleData G D s) (n : Fintype.card V=16)
    (f : Fin 9→V) (fa : f 6=a) (fb : f 7=b) (fs : f 8=s)
    (ports : univ.image (fun i : Fin 6=>f (widenQ1 (by decide : 6≤9) i)) = Vis D) :
    univ.image f=univ\Dark D ∧ Function.Injective f := by
  classical
  have image : univ.image f=univ\Dark D := by
    ext w
    simp only [mem_image,mem_univ,true_and,mem_sdiff]
    constructor
    · rintro ⟨j,rfl⟩
      have noc (w : V) (wv : w∈Vis D) : w∉Dark D := fun wd=>(mem_sdiff.mp wd).2 wv
      fin_cases j
      all_goals first
        | exact noc _ (ports ▸ mem_image.mpr ⟨0,mem_univ _,rfl⟩)
        | exact noc _ (ports ▸ mem_image.mpr ⟨1,mem_univ _,rfl⟩)
        | exact noc _ (ports ▸ mem_image.mpr ⟨2,mem_univ _,rfl⟩)
        | exact noc _ (ports ▸ mem_image.mpr ⟨3,mem_univ _,rfl⟩)
        | exact noc _ (ports ▸ mem_image.mpr ⟨4,mem_univ _,rfl⟩)
        | exact noc _ (ports ▸ mem_image.mpr ⟨5,mem_univ _,rfl⟩)
        | exact fun h=> (shore_off D).1 (mem_sdiff.mp (fa ▸ h)).1
        | exact fun h=> (shore_off D).2 (mem_sdiff.mp (fb ▸ h)).1
        | exact fun h=> F.sOff ((mem_sdiff.mp (fs ▸ h)).1)
    intro wn
    rcases F.cover w with rfl|rfl|rfl|wv|wd
    · exact ⟨6,fa⟩
    · exact ⟨7,fb⟩
    · exact ⟨8,fs⟩
    · obtain ⟨j,_,eq⟩ := mem_image.mp (ports.symm ▸ wv)
      exact ⟨widenQ1 (by decide : 6≤9) j,eq⟩
    exact (wn wd).elim
  refine ⟨image,?_⟩
  have ce : (univ.image f).card=(univ : Finset (Fin 9)).card := by
    rw [image,card_sdiff (subset_univ _),card_univ,n,F.dark7,card_univ]
    decide
  exact fun i j he=>(card_image_iff.mp ce) (mem_univ i) (mem_univ j) he

theorem q1_exterior_add_balance (F : SixVisibleData G D s) (bal : nearBal D={z})
    (f : Fin 9→V) (image : univ.image f=univ\Dark D) (inj : Function.Injective f) :
    univ.image (addQ1 f z)=univ\(Dark D).erase z ∧ Function.Injective (addQ1 f z) := by
  have zm : z∈Dark D := by rw [←F.darkPart,bal]; simp
  have fresh : z∉univ.image f := by simp [image,zm]
  refine ⟨?_,addQ1_inj f z inj fresh⟩
  rw [addQ1_image,image]
  ext w
  simp only [mem_insert,mem_sdiff,mem_univ,true_and,mem_erase]
  by_cases e : w=z <;> simp [e]

#print axioms q1_exterior_coverage
#print axioms q1_exterior_add_balance
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
