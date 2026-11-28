import ExtremalSplitShape189
import ShoreDegrees189
import MinimalCycleBound189
import StarExceptionalSplit189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack Graffiti189LongestPath.Normalize
open Graffiti189LongestPath.ExtremalSplitShape Graffiti189LongestPath.ShoreDegrees
open Graffiti189LongestPath.MinimalCycleBound Graffiti189LongestPath.StarExceptionalSplit
open Graffiti189LongestPath.StarCycleClosure
open private Graffiti189LongestPath.Rigidity.mem_omittedStar from Rigidity189
set_option warningAsError true
set_option maxHeartbeats 6000000
namespace Graffiti189LongestPath.OddMinimum
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The odd minimum-height separated double is ruled out by the
ordinary Dirac-length cycle, including its exact equality geometry and
the one allowable low ambient-degree vertex. -/
theorem odd_minimum_no_dirac_cycle (hc : G.Connected) (k : Nat) (hk : 7≤k)
    (cap : ∀ v,(EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V,S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    (fail : ¬∃ (u v : V) (q : G.Walk u v),q.IsPath ∧ ∀ z,z∈q.support)
    {a b x y : V} {p : G.Walk a b} (hp : EdgeMinAvoid (k+2) p) (hx : x∉p.support)
    (hy : y∉p.support) (xy : G.Adj x y)
    (double : (Pins p x).card=2) (sep : PairedPins p x=∅)
    (high : k+2≤G.degree x)
    (large : 10<(OmittedStar p x).card) (height : (OmittedStar p x).card=k+1)
    (odd : (OmittedStar p x).card%2=1)
    (cyc : ∃ a, ∃ c : (G.induce (((OmittedStar p x).erase x : Finset V) : Set V)).Walk a a,
      c.IsCycle ∧ 2*((OmittedStar p x).card/2-1)≤c.length) : False := by
  classical
  let A := OmittedStar p x
  let T := A.erase x
  let W := ↥(T : Set V)
  let J := G.induce (T : Set V)
  let m := k/2-1
  have ac : A.card=k+1 := height
  have od : A.card%2=1 := odd
  have big : 10<A.card := large
  have k2 : k=2*m+2 := by dsimp [m]; omega
  have m4 : 4≤m := by omega
  have xa : x∈A := Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have tc : T.card=k := by rw [card_erase_of_mem xa,ac,Nat.add_sub_cancel]
  have wo : Fintype.card W=k := by
    change Fintype.card ↥T=k
    exact (Fintype.card_coe T).trans tc
  obtain ⟨r,c,cc,low⟩ := cyc
  change 2*(A.card/2-1)≤c.length at low
  have upper := minimum_height_cycles_le_order_sub_two hc k hk cap conn deg fail
    hp hx hy xy double sep high large height c cc
  have len : c.length=2*m := by omega
  have max : ∀ r (q : J.Walk r r),q.IsCycle → q.length≤c.length := by
    intro r q qc
    have h := minimum_height_cycles_le_order_sub_two hc k hk cap conn deg fail
      hp hx hy xy double sep high large height q qc
    omega
  let C := c.support.toFinset
  let R := (univ : Finset W)\C
  have cc' : C.card=c.length := cycle_card_support c cc
  have rc : R.card=2 := by
    have s := card_sdiff_add_card_eq_card (subset_univ C)
    change R.card+C.card=(univ : Finset W).card at s
    rw [card_univ,wo] at s
    omega
  obtain ⟨u,ur,v,vr,uv⟩ := one_lt_card.mp (by omega : 1<R.card)
  have uc : u∉c.support := fun e => (mem_sdiff.mp ur).2 (List.mem_toFinset.mpr e)
  have vc : v∉c.support := fun e => (mem_sdiff.mp vr).2 (List.mem_toFinset.mpr e)
  have RR : ({u,v}:Finset W)=R := eq_of_subset_of_card_le (by
    intro z h
    rcases mem_insert.mp h with rfl|h
    · exact ur
    · exact (mem_singleton.mp h).symm ▸ vr) (by simp [uv,rc])
  have cv (w : W) : w∈c.support ∨ w=u ∨ w=v := by
    by_cases wc : w∈c.support
    · exact Or.inl wc
    have e : w∈R := mem_sdiff.mpr ⟨mem_univ _,fun h => wc (List.mem_toFinset.mp h)⟩
    rw [←RR] at e
    exact Or.inr (by simpa using e)
  have Jmin (w : W) : 3≤J.degree w := by
    have d := (separated_root_deleted_degrees hc k (by omega) cap conn deg fail
      hp.1.1 hx hy xy double sep w).1
    change A.card≤2*J.degree w+5 at d
    omega
  have Jhigh (w : W) (d : k+2≤G.degree w.val) : m≤J.degree w := by
    have q := (separated_root_deleted_degrees hc k (by omega) cap conn deg fail
      hp.1.1 hx hy xy double sep w).2 d
    change A.card≤2*J.degree w+3 at q
    omega
  have pair (u v : W) (ne : u≠v) : m≤J.degree u ∨ m≤J.degree v :=
    (deg u.val v.val (fun e => ne (Subtype.ext e))).imp (Jhigh u) (Jhigh v)
  have shape : ∃ X L : Finset W, X∪L=univ ∧ Disjoint X L ∧ X.card=m ∧ L.card=m+2 ∧
      (∀ u∈L,∀ v∈L,¬J.Adj u v) ∧
      (∀ u∈L,m≤J.degree u → ∀ v∈X,J.Adj u v) := by
    rcases pair u v uv with uh|vh
    · exact exact_cycle_forces_split c cc m m4 len max uc vc uv cv uh (Jmin v) pair
    · exact exact_cycle_forces_split c cc m m4 len max vc uc uv.symm
        (fun w => (cv w).imp id (fun h => h.elim Or.inr Or.inl)) vh (Jmin u) pair
  obtain ⟨X,L,part,dis,xcard,lcard,ind,attach⟩ := shape
  obtain ⟨e,el,other⟩ : ∃ e∈L,∀ v∈L,v≠e → m≤J.degree v := by
    by_cases b : ∃ e∈L,¬m≤J.degree e
    · obtain ⟨e,el,low⟩ := b
      exact ⟨e,el,fun v _ ne => (pair v e ne).resolve_right low⟩
    · obtain ⟨e,el⟩ := card_pos.mp (by omega : 0<L.card)
      exact ⟨e,el,fun v vl _ => Classical.byContradiction (fun low => b ⟨v,vl,low⟩)⟩
  let inc : W ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let S := insert x (X.map inc)
  let B := L.map inc
  have ex : x∉X.map inc := by
    intro h
    obtain ⟨v,_,q⟩ := mem_map.mp h
    exact (mem_erase.mp v.property).1 q
  have dis' : Disjoint S B := disjoint_left.mpr (by
    intro z sz zb
    obtain ⟨v,vl,q⟩ := mem_map.mp zb
    rcases mem_insert.mp sz with zx|zx
    · exact (mem_erase.mp v.property).1 (q.trans zx)
    obtain ⟨u,ux,r⟩ := mem_map.mp zx
    exact disjoint_left.mp dis ux ((inc.injective (r.trans q.symm)).symm ▸ vl))
  have part' : S∪B=OmittedStar p x := by
    change S∪B=A
    ext z
    constructor
    · intro h
      rcases mem_union.mp h with hs|hb
      · rcases mem_insert.mp hs with rfl|hs
        · exact xa
        obtain ⟨v,_,rfl⟩ := mem_map.mp hs
        exact (mem_erase.mp v.property).2
      · obtain ⟨v,_,rfl⟩ := mem_map.mp hb
        exact (mem_erase.mp v.property).2
    · intro za
      by_cases xx : z=x
      · exact mem_union.mpr (Or.inl (mem_insert.mpr (Or.inl xx)))
      let v : W := ⟨z,mem_erase.mpr ⟨xx,za⟩⟩
      have h : v∈X∪L := part.symm ▸ mem_univ _
      rcases mem_union.mp h with vx|vl
      · have zx : z∈X.map inc := mem_map.mpr ⟨v,vx,rfl⟩
        exact mem_union.mpr (Or.inl (mem_insert.mpr (Or.inr zx)))
      · have zb : z∈B := mem_map.mpr ⟨v,vl,rfl⟩
        exact mem_union.mpr (Or.inr zb)
  have ss : S.card=m+1 := by rw [card_insert_of_not_mem ex,card_map,xcard]
  have bs : B.card=m+2 := by rw [card_map,lcard]
  have ind' : ∀ u∈B,∀ v∈B,¬G.Adj u v := by
    intro u ub v vb ed
    obtain ⟨w,wl,rfl⟩ := mem_map.mp ub
    obtain ⟨q,ql,rfl⟩ := mem_map.mp vb
    exact ind w wl q ql ed
  have cross : ∀ s∈S,∀ l∈B,l≠e.val → G.Adj s l := by
    intro s ss l ll e'
    obtain ⟨v,vl,rfl⟩ := mem_map.mp ll
    rcases mem_insert.mp ss with rfl|sx
    · have va := (mem_erase.mp v.property).2
      have vv := (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp va).2
      exact vv.resolve_left (mem_erase.mp v.property).1
    obtain ⟨w,wx,rfl⟩ := mem_map.mp sx
    exact (attach v vl (other v vl (fun q => e' (congrArg Subtype.val q))) w wx).symm
  have nb : (J.neighborFinset e).map inc⊆S.filter (G.Adj e.val) := by
    intro z zz
    obtain ⟨u,un,rfl⟩ := mem_map.mp zz
    have uAdj := (J.mem_neighborFinset _ _).mp un
    have ux : u∈X := by
      have h : u∈X∪L := part.symm ▸ mem_univ _
      exact (mem_union.mp h).elim id (fun ul => (ind e el u ul uAdj).elim)
    exact mem_filter.mpr ⟨mem_insert.mpr (Or.inr (mem_map.mpr ⟨u,ux,rfl⟩)),uAdj⟩
  have nz := card_le_card nb
  rw [card_map,J.card_neighborFinset_eq_degree] at nz
  exact separated_double_no_one_exception_split hc k (by omega) cap conn deg hp hx hy xy
    high double sep S B part' dis' height (by omega) e.val (mem_map.mpr ⟨e,el,rfl⟩)
    cross ((Jmin e).trans nz) ind'

#print axioms odd_minimum_no_dirac_cycle
end Graffiti189LongestPath.OddMinimum
