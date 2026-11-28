import StarSize189
import UltraOrder189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath Graffiti189LongestPath.Rigidity
open Graffiti189LongestPath.OneSlack Graffiti189LongestPath.SingleStar Graffiti189LongestPath.StarSize
open Graffiti189LongestPath.UltraOrder
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.dist_two
  Graffiti189LongestPath.distance_on_geodesic from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.mem_omittedStar Graffiti189LongestPath.Rigidity.mem_external
  Graffiti189LongestPath.Rigidity.pin_pos from Rigidity189
open private Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary
  Graffiti189LongestPath.OneSlack.cardinal_flankVertices Graffiti189LongestPath.OneSlack.first_eq_if_no_pair from OneSlack189
set_option warningAsError true
set_option maxHeartbeats 2000000
namespace Graffiti189LongestPath.FlankIllumination
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In the tight singleton/fourth-shell configuration, every vertex not
already charged to the pin, its flank, the cut or the far tip must
be reached through a boundary vertex which misses both the pin and the chosen flank. -/
theorem order_upper_unlit_ports (hc : G.Connected) (k : Nat) (hk : 5≤k)
    (cap : ∀ v, (EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x∉p.support)
    (one : (Pins p x).card=1) (far : (Shell G x 4).Nonempty)
    {i : Nat} (hi : i∈Pins p x)
    {f : V} (hf : f∈FlankVertices p x) :
    let t := p.getVert i
    let B := External G (OmittedStar p x)
    let M := (B.erase t).filter (fun v => ¬G.Adj t v ∧ ¬G.Adj f v)
    Fintype.card V≤3*(k+2)+1+M.card*(k+2) := by
  classical
  dsimp only
  let d := k+2
  let t := p.getVert i
  let A := OmittedStar p x
  let B := External G A
  let F := FlankVertices p x
  let E := Shell G x 4
  let R := (univ : Finset V) \ (A∪B)
  let L := DistanceTwo G f
  let M := (B.erase t).filter (fun v => ¬G.Adj t v ∧ ¬G.Adj f v)
  let U := M.biUnion (fun b => R.filter (G.Adj b))
  have cap2 (v : V) : (DistanceTwo G v).card≤d := distanceTwo_le_of_even d v (cap v)
  have full := singleton_star_budget hc k conn hp hx one (cap x)
  obtain ⟨bcard,rigid⟩ := full.2.2.2.2.1 far
  change DistanceTwo G x \ B = F at rigid
  have ec : E.card≤1 := by
    have s := full.2.2.2.1
    have f := full.2.2.1
    change B.card+(DistanceTwo G x \ B).card+E.card≤k+3 at s
    change 2≤(DistanceTwo G x \ B).card at f
    change B.card=k at bcard
    omega
  have sing : Pins p x={i} := by
    apply (eq_of_subset_of_card_le _ _).symm
    · intro z hz
      exact (mem_singleton.mp hz).symm ▸ hi
    · rw [card_singleton,one]
  have fc : F.card≤2 := by
    change (FlankVertices p x).card≤2
    rw [Graffiti189LongestPath.OneSlack.cardinal_flankVertices hp]
    simp only [FlankIndices,sing,image_singleton]
    exact (card_union_le _ _).trans (by simp)
  have tx : G.Adj t x := (Graffiti189LongestPath.pin_data hi).2.symm
  have ta : t∉A := fun h => (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp h).1 (p.getVert_mem_support i)
  have xa : x∈A := Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have tb : t∈B := Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary hx
    (mem_image.mpr ⟨i,hi,rfl⟩)
  have goodF : ∀ u∈F, G.Adj t u := by
    intro u hu
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hu
    rcases mem_union.mp hj with h|h
    · obtain ⟨l,hl,rfl⟩ := mem_image.mp h
      rw [sing] at hl
      have e : l=i := mem_singleton.mp hl
      subst l
      have pos := Graffiti189LongestPath.Rigidity.pin_pos hp hx hi
      have up := (Graffiti189LongestPath.pin_data hi).1
      have e := p.adj_getVert_succ (i:=i-1) (by omega)
      rw [show i-1+1=i by omega] at e
      exact e.symm
    · obtain ⟨l,hl,rfl⟩ := mem_image.mp h
      rw [sing] at hl
      have e : l=i := mem_singleton.mp hl
      subst l
      exact p.adj_getVert_succ (Graffiti189LongestPath.pin_data hi).1
  have ft : G.Adj t f := goodF f hf
  have fnot := (mem_sdiff.mp (flanks_outside_boundary hc hp hx hf)).2
  have fA : f∉A := by
    intro ha
    obtain ⟨j,_,e⟩ := mem_image.mp hf
    exact (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp ha).1
      (e ▸ p.getVert_mem_support j)
  have rad : ∀ u, G.dist x u≤4 :=
    diameter_bound_from_inner_even_layers hc d k 1 cap conn (by dsimp [d]; omega) x
  have rA {z : V} (hz : z∈R) : z∉A := fun h => (mem_sdiff.mp hz).2 (mem_union.mpr (Or.inl h))
  have rB {z : V} (hz : z∈R) : z∉B := fun h => (mem_sdiff.mp hz).2 (mem_union.mpr (Or.inr h))
  have noA {z u : V} (hz : z∈R) (ha : u∈A) : ¬G.Adj z u :=
    fun e => rB hz (Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨rA hz,u,ha,e.symm⟩)
  have coveredA {z : V} (za : z∈A) : z∈L ∨ z∈DistanceTwo G t := by
    by_cases e : G.Adj t z
    · have no : ¬G.Adj f z := fun h => fnot
        (Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨fA,z,za,h.symm⟩)
      exact Or.inl (Graffiti189LongestPath.mem_distanceTwo.mpr
        (Graffiti189LongestPath.dist_two hc (fun h => fA (h.symm ▸ za)) no ft.symm e))
    · right
      rcases (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp za).2 with h|h
      · exact (e (h.symm ▸ tx)).elim
      · exact Graffiti189LongestPath.mem_distanceTwo.mpr
          (Graffiti189LongestPath.dist_two hc (fun h => ta (h.symm ▸ za)) e tx h)
  have coveredR {z : V} (zr : z∈R) :
      z∈F ∨ z∈E ∨ z∈DistanceTwo G t ∨ z∈L ∨ z∈U := by
    have h := rad z
    have nz : x≠z := fun e => rA zr (e ▸ xa)
    have nx : ¬G.Adj x z := fun e => noA zr xa e.symm
    have h2 := hc.one_lt_dist_of_ne_of_not_adj nz nx
    have cases : G.dist x z=2 ∨ G.dist x z=3 ∨ G.dist x z=4 := by omega
    rcases cases with e|e|e
    · exact Or.inl (rigid ▸ mem_sdiff.mpr ⟨Graffiti189LongestPath.mem_distanceTwo.mpr e,rB zr⟩)
    · by_cases pt : G.Adj t z
      · have hz := Graffiti189LongestPath.dist_two hc nz nx tx.symm pt
        omega
      obtain ⟨q,ql⟩ := hc.exists_walk_length_eq_dist x z
      have len : q.length=3 := ql.trans e
      let s := q.getVert 2
      have ds : G.dist x s=2 :=
        Graffiti189LongestPath.distance_on_geodesic hc q ql 2 (by omega)
      have sz : G.Adj s z := by
        have ed := q.adj_getVert_succ (i:=2) (by omega : 2<q.length)
        rwa [show q.getVert 3=z by rw [← len,getVert_length]] at ed
      have st : s≠t := by
        intro e'
        have h' : G.dist x t=1 := dist_eq_one_iff_adj.mpr tx.symm
        rw [e'] at ds
        omega
      have can (edge : G.Adj t s) : z∈DistanceTwo G t :=
        Graffiti189LongestPath.mem_distanceTwo.mpr
          (Graffiti189LongestPath.dist_two hc (fun h => rB zr (h ▸ tb)) pt edge sz)
      by_cases sb : s∈B
      · by_cases edge : G.Adj t s
        · exact Or.inr (Or.inr (Or.inl (can edge)))
        · by_cases fs : G.Adj f s
          · by_cases fz : G.Adj f z
            · exact Or.inr (Or.inr (Or.inl
                (Graffiti189LongestPath.mem_distanceTwo.mpr
                  (Graffiti189LongestPath.dist_two hc (fun h => rB zr (h ▸ tb)) pt ft fz))))
            · by_cases eq : z=f
              · exact Or.inl (eq.symm ▸ hf)
              · exact Or.inr (Or.inr (Or.inr (Or.inl
                  (Graffiti189LongestPath.mem_distanceTwo.mpr
                    (Graffiti189LongestPath.dist_two hc (Ne.symm eq) fz fs sz)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_biUnion.mpr
              ⟨s,mem_filter.mpr ⟨mem_erase.mpr ⟨st,sb⟩,edge,fs⟩,mem_filter.mpr ⟨zr,sz⟩⟩))))
      · have fs : s∈F := rigid ▸ mem_sdiff.mpr ⟨Graffiti189LongestPath.mem_distanceTwo.mpr ds,sb⟩
        exact Or.inr (Or.inr (Or.inl (can (goodF s fs))))
    · exact Or.inr (Or.inl (mem_shell.mpr e))
  have ub (s : V) (hs : s∈M) : (R.filter (G.Adj s)).card≤d := by
    have sb : s∈B := (mem_erase.mp (mem_filter.mp hs).1).2
    obtain ⟨_,u,ua,us⟩ := Graffiti189LongestPath.Rigidity.mem_external.mp sb
    have cover : R.filter (G.Adj s)⊆ DistanceTwo G u := by
      intro z hz
      obtain ⟨zr,sz⟩ := mem_filter.mp hz
      exact Graffiti189LongestPath.mem_distanceTwo.mpr
        (Graffiti189LongestPath.dist_two hc (fun e => rA zr (e ▸ ua))
          (fun e => noA zr ua e.symm) us sz)
    exact (card_le_card cover).trans (cap2 u)
  have uc : U.card≤M.card*d := card_biUnion_le_card_mul M _ d ub
  have l : L.card≤d := cap2 f
  have cov : (univ:Finset V) ⊆ B∪L∪F∪E∪DistanceTwo G t∪U := by
    intro z _
    by_cases zb : z∈B
    · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl (mem_union.mpr (Or.inl
        (mem_union.mpr (Or.inl (mem_union.mpr (Or.inl zb)))))))))
    by_cases za : z∈A
    · rcases coveredA za with h|h
      · simp only [mem_union]
        tauto
      · simp only [mem_union]
        tauto
    have zr : z∈R := mem_sdiff.mpr ⟨mem_univ _,fun h => (mem_union.mp h).elim za zb⟩
    have zr' := coveredR zr
    simp only [mem_union]
    tauto
  have c := card_le_card cov
  rw [card_univ] at c
  have c₁ := card_union_le B L
  have c₂ := card_union_le (B∪L) F
  have c₃ := card_union_le (B∪L∪F) E
  have c₄ := card_union_le (B∪L∪F∪E) (DistanceTwo G t)
  have c₅ := card_union_le (B∪L∪F∪E∪DistanceTwo G t) U
  have dt := cap2 t
  change B.card=k at bcard
  change Fintype.card V≤3*d+1+M.card*d
  dsimp [d] at l dt uc ⊢
  omega

/-- The far singleton cannot be part of a counterexample if its pin
with one flank jointly sees all other cut vertices, or misses only one at threshold d≥10. -/
theorem traceable_of_few_unlit_ports (hc : G.Connected) (k : Nat) (hk : 5≤k)
    (cap : ∀ v, (EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V, u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x∉p.support)
    (one : (Pins p x).card=1) (far : (Shell G x 4).Nonempty)
    {i : Nat} (hi : i∈Pins p x)
    {f : V} (hf : f∈FlankVertices p x)
    (short : let t := p.getVert i; let B := External G (OmittedStar p x)
      let M := (B.erase t).filter (fun v => ¬G.Adj t v ∧ ¬G.Adj f v)
      M.card=0 ∨ (8≤k ∧ M.card≤1)) :
    ∃ (u v : V) (q : G.Walk u v), q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  apply Classical.byContradiction
  intro fail
  have floor := order_lower_wings_sharp hc k hk cap conn deg fail
  let M := ((External G (OmittedStar p x)).erase (p.getVert i)).filter (fun v => ¬G.Adj (p.getVert i) v ∧ ¬G.Adj f v)
  have bound := order_upper_unlit_ports hc k hk cap conn hp hx one far hi hf
  change Fintype.card V≤3*(k+2)+1+M.card*(k+2) at bound
  change M.card=0 ∨ (8≤k ∧ M.card≤1) at short
  rcases short with h|⟨hk',hm⟩
  · rw [h,zero_mul] at bound
    omega
  · have small := Nat.mul_le_mul_right (k+2) hm
    rw [one_mul] at small
    omega

#print axioms order_upper_unlit_ports
#print axioms traceable_of_few_unlit_ports
end Graffiti189LongestPath.FlankIllumination
