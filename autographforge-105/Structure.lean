import Counts
import ChordalBasis

namespace Hereditary105
open Finset SimpleGraph AutoGraphPowerBurning CographRadius
variable {V : Type*} (G : SimpleGraph V)

def SquareFree := ¬∃ f : Fin 4 ↪ V, ∀ i j, G.Adj (f i) (f j) ↔ TriangleChain.consecutive i j

private theorem square {a b c d : V} (ab : G.Adj a b) (bc : G.Adj b c)
    (cd : G.Adj c d) (da : G.Adj d a) (ac : a ≠ c) (bd : b ≠ d)
    (nac : ¬ G.Adj a c) (nbd : ¬ G.Adj b d) : ¬SquareFree G := by
  let f : Fin 4 → V := ![a,b,c,d]
  have inj : Function.Injective f := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [f,ab.ne,bc.ne,cd.ne,da.ne,ac,bd,
      Ne.symm ab.ne,Ne.symm bc.ne,Ne.symm cd.ne,Ne.symm da.ne,Ne.symm ac,Ne.symm bd]
  have ca : ¬ G.Adj c a := fun h => nac h.symm
  have db : ¬ G.Adj d b := fun h => nbd h.symm
  have ba := ab.symm
  have cb := bc.symm
  have dc := cd.symm
  have ad := da.symm
  intro free
  apply free
  refine ⟨⟨f,inj⟩,?_⟩
  intro i j
  change G.Adj (f i) (f j) ↔ _
  fin_cases i <;> fin_cases j <;> simp [f,TriangleChain.consecutive, *]

/-- Two nonclique shores of a proper join exhibit an induced square. -/
theorem universal_of_join (free : SquareFree G) {A : V → Prop} {a b : V}
    (ha : A a) (hb : ¬ A b) (cross : ∀ u v, A u → ¬ A v → G.Adj u v) :
    ∃ x, Universal G x := by
  classical
  by_cases leftClique : ∀ u v, A u → A v → u ≠ v → G.Adj u v
  · refine ⟨a,fun y ne => ?_⟩
    by_cases h : A y
    · exact leftClique a y ha h ne
    · exact cross a y ha h
  · push_neg at leftClique
    obtain ⟨u,v,hu,hv,uv,nuv⟩ := leftClique
    refine ⟨b,fun y byNe => ?_⟩
    by_cases hy : A y
    · exact (cross y b hy hb).symm
    · by_contra missing
      exact square G (cross u b hu hb) (cross v b hv hb).symm
        (cross v y hv hy) (cross u y hu hy).symm uv byNe nuv missing free

theorem cograph_restrict {U : Type*} (f : U ↪ V) (h : Cograph G) : Cograph (G.comap f) :=
  fun ⟨g,e⟩ => h ⟨g.trans f,e⟩

theorem square_restrict {U : Type*} (f : U ↪ V) (h : SquareFree G) : SquareFree (G.comap f) :=
  fun ⟨g,e⟩ => h ⟨g.trans f,e⟩

theorem exact [Fintype V] (cog : Cograph G) (free : SquareFree G) :
    domination G = components G ∧ power G = components G := by
  classical
  apply exact_of_centers
  intro c
  let x : c.supp := ⟨c.out,c.out_eq⟩
  by_cases hn : Nontrivial c.supp
  · letI := hn
    letI : Fintype c.supp := Fintype.ofFinite _
    let f := Function.Embedding.subtype (· ∈ c.supp)
    have localCog : Cograph (G.induce c.supp) := cograph_restrict G f cog
    have localFree : SquareFree (G.induce c.supp) := square_restrict G f free
    obtain ⟨A,b,ha,hb,cross⟩ := join_at _ c.connected_induce_supp localCog x
    obtain ⟨u,univVertex⟩ := universal_of_join _ localFree ha hb cross
    exact ⟨u,u.property,fun v vc ne => (univVertex ⟨v,vc⟩ (fun h => ne (congrArg Subtype.val h.symm))).symm⟩
  · have sub := not_nontrivial_iff_subsingleton.mp hn
    exact ⟨x,x.property,fun v vc ne => (ne (congrArg Subtype.val (sub.elim (⟨v,vc⟩ : c.supp) x))).elim⟩

theorem row105 [Fintype V] (_order : 2 ≤ Fintype.card V)
    (chordal : TriangleChain.Chordal G) (cog : Cograph G) : domination G ≤ power G := by
  obtain ⟨d,p⟩ := exact G cog (chordal 4 (by decide))
  exact (d.trans p.symm).le

#print axioms universal_of_join
#print axioms exact
#print axioms row105
end Hereditary105
