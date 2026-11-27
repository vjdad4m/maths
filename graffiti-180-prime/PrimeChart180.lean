import TrueChart180
import PrimeQuotient180
import RootPairParity180
import FoldTwin180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 PortParity
open Classical
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
variable {H : SimpleGraph V} {G : SimpleGraph B} {f : V→B} {s : B→V} {r : V}

omit [Fintype V] [Fintype B] [DecidableEq B] in
theorem TrueChart.ind_image (h : TrueChart H G f s r) {I : Finset B} (ii : Indep G I) :
    Indep H (I.image s) := by
  rintro _ xm _ ym _ ed
  obtain ⟨i,im,rfl⟩ := mem_image.mp xm
  obtain ⟨j,jm,rfl⟩ := mem_image.mp ym
  have e := h.oldAdj.mp ed
  exact ii _ im _ jm e.ne e

omit [Fintype V] [DecidableEq B] in
theorem TrueChart.ind_pull (h : TrueChart H G f s r) {A : Finset V} (ai : Indep H A) :
    Indep G (pull s A) := by
  intro i im j jm ne ed
  exact ai _ (mem_pull.mp im) _ (mem_pull.mp jm) (h.sec.injective.ne ne) (h.oldAdj.mpr ed)

omit [Fintype V] [DecidableEq B] in
theorem TrueChart.image_pull (h : TrueChart H G f s r) {A : Finset V} (ra : r∉A) :
    (pull s A).image s=A := by
  ext x
  constructor
  · rintro xm
    obtain ⟨i,im,rfl⟩ := mem_image.mp xm
    exact mem_pull.mp im
  · intro xm
    obtain ⟨i,rfl⟩ := (h.all x).resolve_left (fun eq => ra (eq ▸ xm))
    exact mem_image_of_mem s (mem_pull.mpr xm)

theorem twinChart (G : SimpleGraph B) (a : B) :
    TrueChart (ear G (twinPorts G a true)) G (foldTwin a) Sum.inl (.inr ()) := by
  refine ⟨twin_bags G a true,fun _ => rfl,fun _ => by simp,?_,?_⟩
  · rintro (x|⟨⟩)
    · exact Or.inr ⟨x,rfl⟩
    · exact Or.inl rfl
  · change a∈twinPorts G a true
    simp [twinPorts]

theorem pairChart (H : SimpleGraph V) (r y : V) (ry : r≠y) (hom : Homogeneous H {r,y}) (ed : H.Adj r y) :
    TrueChart H (side H (reps {r,y} y)) (collapse {r,y} y) Subtype.val r := by
  classical
  let M : Finset V := {r,y}
  have rm : r∈M := by simp [M]
  have ym : y∈M := by simp [M]
  have out : r∉reps M y := by simp [reps,rm,ry]
  refine ⟨module_bags H M hom y ym,?_,?_,?_,?_⟩
  · intro i
    apply Subtype.ext
    rw [collapse_val]
    rcases mem_insert.mp i.property with iy|im
    · simp [iy,ym]
    · exact if_neg (mem_sdiff.mp im).2
  · intro i eq
    exact out (eq ▸ i.property)
  · intro x
    by_cases xr : x=r
    · exact Or.inl xr
    · have mem : x∈reps M y := by
        by_cases xy : x=y
        · exact xy ▸ mem_insert_self ..
        · exact mem_insert_of_mem (mem_sdiff.mpr ⟨mem_univ _,by simp [M,xr,xy]⟩)
      exact Or.inr ⟨⟨x,mem⟩,rfl⟩
  · simpa [collapse_val,rm,M] using ed

#print axioms TrueChart.image_pull
#print axioms twinChart
#print axioms pairChart
end Minimal180.Substitution
