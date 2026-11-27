import Protected180

set_option warningAsError true
namespace Minimal180.Transversals
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem recolor_isolated (G : SimpleGraph V) (Z : Finset V) (r : V) (a : Bool) (c : V→Bool)
    (good : ProperOn G Z c) (iso : ∀ x∈Z,¬G.Adj r x) :
    ProperOn G Z (fun x => if x=r then a else c x) := by
  intro x xm y ym ed
  have xr : x≠r := fun eq => iso y ym (eq ▸ ed)
  have yr : y≠r := fun eq => iso x xm (eq ▸ ed.symm)
  simpa [xr,yr] using good x xm y ym ed

omit [Fintype V] in
theorem add_mono (G : SimpleGraph V) (Z : Finset V) (v : V) (a : Bool) (c : V→Bool)
    (good : ProperOn G Z c) (mono : ∀ x∈Z,G.Adj v x → c x=a) :
    TwoColor G (insert v Z) := by
  apply (color_function ..).mpr
  refine ⟨fun x => if x=v then !a else c x,fun x xm y ym ed => ?_⟩
  by_cases xv : x=v <;> by_cases yv : y=v
  · exact (ed.ne (xv.trans yv.symm)).elim
  · have cs := mono y ((mem_insert.mp ym).resolve_left yv) (xv ▸ ed)
    simp [xv,yv,cs]
  · have cs := mono x ((mem_insert.mp xm).resolve_left xv) (yv ▸ ed.symm)
    simp [xv,yv,cs]
  · simpa [xv,yv] using good x ((mem_insert.mp xm).resolve_left xv) y ((mem_insert.mp ym).resolve_left yv) ed

/-- Any isolated-root witness can be enlarged by the port v when v has
at most one neighbor outside the root's closed neighborhood. -/
theorem enlarge_isolated (G : SimpleGraph V) (r v : V) (rv : G.Adj r v)
    (small : (G.neighborFinset v\insert r (G.neighborFinset r)).card≤1)
    (Z : Finset V) (col : TwoColor G Z) (iso : ∀ x∈Z,¬G.Adj r x) :
    TwoColor G (insert v Z) ∧ (insert v Z).card=Z.card+1 := by
  classical
  obtain ⟨c,good⟩ := (color_function ..).mp col
  let F := G.neighborFinset v\insert r (G.neighborFinset r)
  have tone : ∃ a,∀ x∈F,c x=a := by
    by_cases hit : F.Nonempty
    · obtain ⟨w,wm⟩ := hit
      exact ⟨c w,fun x xm => congrArg c (card_le_one.mp small x xm w wm)⟩
    · exact ⟨false,fun x xm => (hit ⟨x,xm⟩).elim⟩
  obtain ⟨a,mono⟩ := tone
  let d x := if x=r then a else c x
  have vc : v∉Z := fun m => iso v m rv
  refine ⟨add_mono G Z v a d (recolor_isolated G Z r a c good iso) ?_,card_insert_of_not_mem vc⟩
  intro x xm vx
  by_cases xr : x=r
  · simp [d,xr]
  · have far : x∈F := mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr vx,fun m =>
      iso x xm ((G.mem_neighborFinset _ _).mp ((mem_insert.mp m).resolve_left xr))⟩
    simp [d,xr,mono x far]

/-- In this graph-wide root class the adjacent-twin credit is dispensable
at every independent marking that contains the root. There is no restriction
on odd-cycle transversal number. -/
theorem credit_iff (G : SimpleGraph V) (r v : V) (rv : G.Adj r v)
    (small : (G.neighborFinset v\insert r (G.neighborFinset r)).card≤1)
    (I : Finset V) (ir : r∈I) : OddRootTest G r I ↔ Protected G r true I := by
  classical
  let Q := parity G r true
  have pins : I∩insert r Q=insert r (I∩Q) := by ext x;by_cases eq : x=r <;> simp [eq,ir]
  constructor
  · rintro ⟨Z,col,keep,ok⟩
    by_cases iso : ∀ x∈Z,¬G.Adj r x
    · obtain ⟨bi,sz⟩ := enlarge_isolated G r v rv small Z col iso
      refine ⟨insert v Z,bi,(pins ▸ keep).trans (subset_insert ..),?_⟩
      rw [bonus,if_pos iso] at ok;rw [sz];omega
    · refine ⟨Z,col,pins ▸ keep,?_⟩
      simpa [bonus,iso] using ok
  · rintro ⟨Z,col,keep,ok⟩
    exact ⟨Z,col,pins ▸ keep,ok.trans (Nat.le_add_right _ _)⟩

#print axioms enlarge_isolated
#print axioms credit_iff
end Minimal180.Transversals
