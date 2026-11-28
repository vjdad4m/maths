import SingleTriangleLoss
import PivotWithLeaf
import OddQuota384b
namespace Graffiti384b.EarRooted
open Finset SimpleGraph Exterior FiveChoice
open private Repair.isolate Repair.edge_info Repair.triangles_le_choose from Repair384b
open private Prune.outside_zero from Prune384b
open private OddQuota.core_data from OddQuota384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- At minimum nonleaf quota the original positive vertices have distinct positive scores. -/
private theorem original_scores (few : (nonleaves G).card<(types G).card) :
    (types G).card=(nonleaves G).card+1 ∧
      (∀v∈nonleaves G,0<trianglesAt G v) ∧ Set.InjOn (trianglesAt G) (nonleaves G : Set V) := by
  classical
  obtain ⟨count,pos,inj⟩ := OddQuota.core_data G few
  have same (v : {w // w∈nonleaves G}) :
      trianglesAt (G.induce (nonleaves G:Set V)) v=trianglesAt G v.val :=
    Prune.counts_preserved G (nonleaves G) Subset.rfl v
  refine ⟨count,fun v vm => (same ⟨v,vm⟩) ▸ pos ⟨v,vm⟩,?_⟩
  intro u hu v hv eq
  exact congrArg Subtype.val (inj ((same ⟨u,hu⟩).trans (eq.trans (same ⟨v,hv⟩).symm)))

/-- At q=t-1 a leaf attached to the vertex of triangle count one gives the catalogue bound.
The pivot may have arbitrary further neighbors, including edges belonging to no triangle. -/
theorem leaf_at_single_triangle (few : (nonleaves G).card<(types G).card)
    {e z : V} (score : trianglesAt G e=1) (leaf : G.degree z=1) (ez : G.Adj e z) :
    gamma G≤bound G := by
  classical
  let S := nonleaves G
  let H := Repair.isolate G e
  obtain ⟨count,positive,injective⟩ := original_scores G few
  have core {v : V} (pos : 0<trianglesAt G v) : v∈S := by
    by_contra out
    exact (Nat.ne_of_gt pos) (Prune.outside_zero G out)
  have zs : z∉S := by intro zm; have d := (mem_filter.mp zm).2; omega
  have es : e∈S := core (by omega)
  obtain ⟨p,one⟩ := card_eq_one.mp (show (link G e).card=1 from score)
  have pm : p∈link G e := one ▸ mem_singleton_self _
  obtain ⟨sub,size,cl⟩ := Repair.edge_info G pm
  obtain ⟨a,b,ne,shape⟩ := card_eq_two.mp size
  have ap : a∈p := shape ▸ mem_insert_self ..
  have bp : b∈p := shape ▸ mem_insert_of_mem (mem_singleton_self _)
  have ea := (G.mem_neighborFinset ..).mp (sub ap)
  have eb := (G.mem_neighborFinset ..).mp (sub bp)
  have ab := cl a ap b bp ne
  have abH : H.Adj a b := ⟨ab,ea.ne.symm,eb.ne.symm⟩
  have ga : a∈S := core (card_pos.mpr ⟨{e,b},mem_pair G ea.symm ab eb⟩)
  have gb : b∈S := core (card_pos.mpr ⟨{e,a},mem_pair G eb.symm ab.symm ea⟩)
  have one' : link G e={{a,b}} := shape ▸ one
  have lossA : trianglesAt G a=trianglesAt H a+1 := by simpa [H] using isolated_score G ea.ne.symm one'
  have lossB : trianglesAt G b=trianglesAt H b+1 := by simpa [H] using isolated_score G eb.ne.symm one'
  have same {x : V} (xe : x≠e) (xa : x≠a) (xb : x≠b) : trianglesAt G x=trianglesAt H x := by
    simpa [H,xa,xb] using isolated_score G xe one'
  have lower {x : V} (xs : x∈S) (xe : x≠e) : 2≤trianglesAt G x := by
    have pos := positive x xs
    have n : trianglesAt G x≠1 := fun eq => xe (injective xs es (eq.trans score.symm))
    omega
  have pa := lower ga ea.ne.symm
  have pb := lower gb eb.ne.symm
  have diff : trianglesAt H a≠trianglesAt H b := fun eq => ne (injective ga gb (by omega))
  have en (x : V) (xp : 0<trianglesAt H x) : x≠e := by
    rintro rfl
    have hz : trianglesAt H x=0 := isolated_zero G x
    omega
  have rich (v : V) (va : v≠a) (vb : v≠b) (vp : 0<trianglesAt H v) : 2≤trianglesAt H v := by
    have s := same (en v vp) va vb
    rw [←s]; exact lower (core (s ▸ vp)) (en v vp)
  have inj (x y : V) (xa : x≠a) (xb : x≠b) (ya : y≠a) (yb : y≠b)
      (xp : 0<trianglesAt H x) (yp : 0<trianglesAt H y) (eq : trianglesAt H x=trianglesAt H y) : x=y := by
    have sx := same (en x xp) xa xb
    have sy := same (en y yp) ya yb
    exact injective (core (sx ▸ xp)) (core (sy ▸ yp)) (sx.trans (eq.trans sy.symm))
  obtain ⟨P,Q,al,br,pins⟩ := prescribed_edge H abH (by omega) (by omega) diff rich inj
  have val := shared_omission G es zs ez ea eb (fun h => zs (h ▸ ga)) (fun h => zs (h ▸ gb)) al br pins (by
    intro v vs ve vl vr
    have va : v≠a := fun eq => vl (eq ▸ al)
    have vb : v≠b := fun eq => vr (eq ▸ br)
    have s := same ve va vb
    have sc := lower vs ve
    by_contra! small
    change H.degree v<3 at small
    have cap := (Repair.triangles_le_choose H v).trans (Nat.choose_le_choose 2 (by omega : H.degree v≤2))
    rw [Nat.choose_self] at cap; omega)
  unfold bound; rw [count]; exact val

end Graffiti384b.EarRooted
#print axioms Graffiti384b.EarRooted.leaf_at_single_triangle
