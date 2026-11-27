import Rooted185

namespace Graffiti179
open Finset SimpleGraph Short177
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable [DecidableRel G.Adj]

theorem claw_state_keep_root {s : Finset V} (b : Block G univ s)
    {r a₁ a₂ a₃ : V} (hr : r ∈ b.A ∪ b.B)
    (a₁m : a₁ ∈ b.A ∪ b.B) (a₂m : a₂ ∈ b.A ∪ b.B) (a₃m : a₃ ∈ b.A ∪ b.B)
    (ar₁ : G.Adj a₁ r) (ar₂ : G.Adj a₂ r) (ar₃ : G.Adj a₃ r)
    (ne₁₂ : a₁ ≠ a₂) (ne₁₃ : a₁ ≠ a₃) (ne₂₃ : a₂ ≠ a₃) :
    ∃ D, r ∈ D ∧ State G 2 (b.A ∪ b.B) D := by
  classical
  let T := b.A ∪ b.B
  let W := (T : Set V)
  let H := G.induce W
  let o : W := ⟨r,hr⟩
  let p := Rooted.chooseParent (show H.Connected from b.conn) o
  let χ (x : W) := decide (x.val ∈ b.A)
  obtain ⟨x,y,xy,xe,ye,same⟩ :=
    p.two_ends_same_color (show H.Connected from b.conn) χ
      (a:=⟨a₁,a₁m⟩) (b:=⟨a₂,a₂m⟩) (c:=⟨a₃,a₃m⟩)
      ar₁ ar₂ ar₃
      (fun h => ne₁₂ (congrArg Subtype.val h))
      (fun h => ne₁₃ (congrArg Subtype.val h))
      (fun h => ne₂₃ (congrArg Subtype.val h))
  let R : Set W := {w | w = x ∨ w = y}
  let K : Finset V := T \ {x.val,y.val}
  have es : ∀ v ∈ R, p.End v := by
    rintro z (rfl | rfl)
    · exact xe
    · exact ye
  have mem (v : W) : v ∉ R ↔ v.val ∈ K := by
    simp [R,K,v.property,Subtype.ext_iff,not_or]
  have rm : o ∉ R := fun rr => (es _ rr).1 rfl
  let inc : H.induce Rᶜ →g G.induce (K : Set V) :=
    { toFun := fun z => ⟨z.val.val,(mem z.val).mp z.property⟩
      map_rel' := fun e => e }
  have conn : Graffiti177.Con G K := by
    apply (connected_iff_exists_forall_reachable _).mpr
    refine ⟨inc ⟨o,rm⟩,fun z => ?_⟩
    have zm : z.val ∈ T := (mem_sdiff.mp z.property).1
    let z' : W := ⟨z.val,zm⟩
    have ok : z' ∉ R := (mem z').mpr z.property
    exact ((p.reach_keep R es z' ok).map inc).symm
  have parents {u : W} (ur : u ∈ R) : u.val ∈ closed G K := by
    have no : p.next u ∉ R := fun emp => (es _ emp).2 u (es u ur).1 rfl
    exact (mem_closed G).mpr (Or.inr ⟨(p.next u).val,(mem (p.next u)).mp no,(p.step u (es u ur).1).1⟩)
  have sameA : x.val ∈ b.A ↔ y.val ∈ b.A := by
    change decide (x.val ∈ b.A) = decide (y.val ∈ b.A) at same
    constructor <;> intro h
    · simpa [h] using same.symm
    · simpa [h] using same
  have act : (x.val ∈ b.A ∧ y.val ∈ b.A) ∨ (x.val ∈ b.B ∧ y.val ∈ b.B) := by
    by_cases h : x.val ∈ b.A
    · exact Or.inl ⟨h,sameA.mp h⟩
    · exact Or.inr ⟨(mem_union.mp x.property).resolve_left h,
        (mem_union.mp y.property).resolve_left (fun yy => h (sameA.mpr yy))⟩
  have dom : closed G T ⊆ closed G K := by
    intro z hz
    by_cases za : z = x.val
    · subst z
      exact parents (show x ∈ R from Or.inl rfl)
    by_cases zb : z = y.val
    · subst z
      exact parents (show y ∈ R from Or.inr rfl)
    by_cases havez : z ∈ T
    · exact (mem_closed G).mpr (Or.inl (by simp [K,havez,za,zb]))
    obtain ⟨A,B⟩ := b.maximal (mem_univ z) havez (((mem_closed G).mp hz).resolve_left havez)
    rcases act with ⟨xa,ya⟩ | ⟨xb,yb⟩
    · obtain ⟨v,vb,e⟩ := B
      have xn : v ≠ x.val := fun h => (disjoint_left.mp b.disjoint) xa (h ▸ vb)
      have yn : v ≠ y.val := fun h => (disjoint_left.mp b.disjoint) ya (h ▸ vb)
      exact (mem_closed G).mpr (Or.inr ⟨v,by simp [K,T,mem_union_right _ vb,xn,yn],e⟩)
    · obtain ⟨v,va,e⟩ := A
      have xn : v ≠ x.val := fun h => (disjoint_left.mp b.disjoint) (h ▸ va) xb
      have yn : v ≠ y.val := fun h => (disjoint_left.mp b.disjoint) (h ▸ va) yb
      exact (mem_closed G).mpr (Or.inr ⟨v,by simp [K,T,mem_union_left _ va,xn,yn],e⟩)
  have sub : ({x.val,y.val} : Finset V) ⊆ T := by simp [insert_subset_iff,x.property,y.property]
  have cnt := card_sdiff_add_card_eq_card sub
  rw [card_pair (fun h => xy (Subtype.ext h))] at cnt
  exact ⟨K,(mem o).mp rm,⟨⟨b.A,b.B,b.disjoint,rfl,b.indA,b.indB⟩,conn,cnt.le,dom⟩⟩

theorem rooted_dom_of_local_claw (hc : G.Connected) (r : V) (large : 3 ≤ localInd G r) :
    ∃ E B : Finset V, r ∈ E ∧ r ∈ B ∧ Graffiti177.Con G E ∧
      closed G E = univ ∧ TwoColor G B ∧ E.card + 2 ≤ B.card := by
  classical
  letI := hc.nonempty
  let choices := (G.neighborFinset r).powerset.filter (Indep G)
  have ready : choices.Nonempty := ⟨∅,by simp [choices,Indep]⟩
  obtain ⟨A,aM,amax⟩ := exists_max_image choices Finset.card ready
  have leA : localInd G r ≤ A.card := Finset.sup_le amax
  obtain ⟨T,tA,tc⟩ := Finset.exists_subset_card_eq (large.trans leA)
  obtain ⟨nA,iA⟩ := mem_filter.mp aM
  have nT : T ⊆ G.neighborFinset r := tA.trans (mem_powerset.mp nA)
  have iT : Indep G T := fun a ha b hb => iA a (tA ha) b (tA hb)
  have notR : r ∉ T := fun h => G.not_mem_neighborFinset_self r (nT h)
  let S := insert r T
  have sc : Graffiti177.Con G S :=
    Graffiti177.con_of_neighbors G (Graffiti177.con_single G r) (by simp [S]) (by
      intro v hv miss
      have ne : v ≠ r := by simpa using miss
      have nv := nT ((mem_insert.mp hv).resolve_left ne)
      exact ⟨r,by simp,((G.mem_neighborFinset r _).mp nv).symm⟩)
  have bc : TwoColor G S := by
    refine ⟨{r},T,disjoint_singleton_left.mpr notR,?_,?_,iT⟩
    · ext v; simp [S]
    · simp [Indep]
  obtain ⟨b⟩ := exists_block G (subset_univ S) sc bc
  obtain ⟨a₁,a₂,a₃,ne₁₂,ne₁₃,ne₂₃,e⟩ := card_eq_three.mp tc
  have inc : ∀ v ∈ T, v ∈ b.A ∪ b.B := fun v h => b.seeded (mem_insert_of_mem h)
  have R := b.seeded (mem_insert_self r T)
  have h1 : a₁ ∈ T := by simp [e]
  have h2 : a₂ ∈ T := by simp [e]
  have h3 : a₃ ∈ T := by simp [e]
  obtain ⟨D,hrD,st⟩ := claw_state_keep_root G b R (inc _ h1) (inc _ h2) (inc _ h3)
    ((G.mem_neighborFinset r _).mp (nT h1)).symm
    ((G.mem_neighborFinset r _).mp (nT h2)).symm
    ((G.mem_neighborFinset r _).mp (nT h3)).symm ne₁₂ ne₁₃ ne₂₃
  exact complete_state_rooted G hc (trim_one G) 2 (b.A ∪ b.B) D st ⟨r,R⟩ r hrD R


#print axioms rooted_dom_of_local_claw
end Graffiti179
