import ThetaSevenFaithfulTiny
import Mathlib.Tactic.FinCases

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteT2PairCounts
open SquareCap (boundary)
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in
def extend (c : V→Bool) (x y : V) (a b : Bool) : V→Bool :=
  fun z=>if z=x then a else if z=y then b else c z

def innerCut (c : V→Bool) (x y : V) : Finset (V×V) :=
  (boundary G c).filter (fun e=>e.1≠x ∧ e.1≠y ∧ e.2≠x ∧ e.2≠y)

def row (c : V→Bool) (x y : V) (a : Bool) : Finset V :=
  ((G.neighborFinset x).erase y).filter (fun v=>c v≠a)

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem in_boundary {c : V→Bool} {u v : V} :
    (u,v)∈boundary G c ↔ c u=true∧c v=false∧G.Adj u v := by
  classical
  simp [boundary]

private theorem in_row {c : V→Bool} {x y v : V} {a : Bool} :
    v∈row G c x y a ↔ v≠y∧G.Adj x v∧c v≠a := by
  simp [row,mem_neighborFinset,and_assoc]

omit [Fintype V] [DecidableEq V] in
private def orient (x : V) (a : Bool) (v : V) : V×V :=
  if a then (x,v) else (v,x)

omit [Fintype V] [DecidableEq V] in
private theorem orient_inj (x : V) (a : Bool) : Function.Injective (orient x a) := by
  intro u v e
  cases a
  · exact congrArg Prod.fst e
  · exact congrArg Prod.snd e

omit [Fintype V] [DecidableEq V] in
def mismatch (a b : Bool) : ℕ := if a=b then 0 else 1

/-- Exact cut accounting after setting the two colors of an adjacent
pair. The four terms are internal surviving edges, the two port rows,
and the single mutual edge. -/
theorem extended_boundary (c : V→Bool) {x y : V} (xy : G.Adj x y) (a b : Bool) :
    (boundary G (extend c x y a b)).card =
      (innerCut G c x y).card+(row G c x y a).card+(row G c y x b).card+mismatch a b := by
  classical
  let I := innerCut G c x y
  let X := (row G c x y a).image (orient x a)
  let Y := (row G c y x b).image (orient y b)
  let E : Finset (V×V) := if a=b then ∅ else {orient x a y}
  have nx : x≠y := xy.ne
  have Xshape (e : V×V) (h : e∈X) :
      (e.1=x∧e.2≠x∧e.2≠y) ∨ (e.2=x∧e.1≠x∧e.1≠y) := by
    obtain ⟨v,hv,rfl⟩ := mem_image.mp h
    obtain ⟨vy,ed,_⟩ := (in_row G).mp hv
    cases a
    · exact Or.inr ⟨rfl,ed.ne.symm,vy⟩
    · exact Or.inl ⟨rfl,ed.ne.symm,vy⟩
  have Yshape (e : V×V) (h : e∈Y) :
      (e.1=y∧e.2≠x∧e.2≠y) ∨ (e.2=y∧e.1≠x∧e.1≠y) := by
    obtain ⟨v,hv,rfl⟩ := mem_image.mp h
    obtain ⟨vx,ed,_⟩ := (in_row G).mp hv
    cases b
    · exact Or.inr ⟨rfl,vx,ed.ne.symm⟩
    · exact Or.inl ⟨rfl,vx,ed.ne.symm⟩
  have Eshape (e : V×V) (h : e∈E) :
      (e.1=x∧e.2=y)∨(e.1=y∧e.2=x) := by
    have h' : e=orient x a y := by
      by_cases he : a=b <;> simp [E,he] at h ⊢
      exact h
    subst e
    cases a <;> simp [orient]
  have apart1 : Disjoint I X := by
    rw [disjoint_left]
    intro e hi hx
    have h := (mem_filter.mp hi).2
    rcases Xshape e hx with ⟨p,_,_⟩|⟨p,_,_⟩
    · exact h.1 p
    · exact h.2.2.1 p
  have apart2 : Disjoint (I∪X) Y := by
    rw [disjoint_left]
    intro e hi hy
    rcases mem_union.mp hi with hi|hx
    · have h := (mem_filter.mp hi).2
      rcases Yshape e hy with ⟨p,_,_⟩|⟨p,_,_⟩
      · exact h.2.1 p
      · exact h.2.2.2 p
    · rcases Xshape e hx with ⟨ex,e2x,e2y⟩|⟨ex,e1x,e1y⟩ <;>
        rcases Yshape e hy with ⟨ey,o2x,o2y⟩|⟨ey,o1x,o1y⟩
      · exact xy.ne (ex.symm.trans ey)
      · exact e2y ey
      · exact e1y ey
      · exact xy.ne (ex.symm.trans ey)
  have apart3 : Disjoint ((I∪X)∪Y) E := by
    rw [disjoint_left]
    intro e hi he
    rcases mem_union.mp hi with hi|hy
    · rcases mem_union.mp hi with hi|hx
      · have h := (mem_filter.mp hi).2
        rcases Eshape e he with ⟨p,_⟩|⟨p,_⟩
        · exact h.1 p
        · exact h.2.1 p
      · rcases Xshape e hx with ⟨eq,_,notY⟩|⟨eq,_,notY⟩ <;>
          rcases Eshape e he with ⟨u,v⟩|⟨u,v⟩
        · exact notY v
        · exact nx (eq.symm.trans u)
        · exact nx (eq.symm.trans v)
        · exact notY u
    · rcases Yshape e hy with ⟨hy,n1,_⟩|⟨hy,n1,_⟩ <;> rcases Eshape e he with ⟨u,v⟩|⟨u,v⟩
      · exact xy.ne (u.symm.trans hy)
      · exact n1 v
      · exact n1 u
      · exact xy.ne (v.symm.trans hy)
  have split : boundary G (extend c x y a b)=((I∪X)∪Y)∪E := by
    ext ⟨u,v⟩
    constructor
    · intro h
      obtain ⟨ht,hf,hg⟩ := (in_boundary G).mp h
      by_cases ux : u=x
      · subst u
        by_cases vy : v=y
        · subst v
          have at' : a=true := by simpa [extend] using ht
          have bf : b=false := by simpa [extend,nx.symm] using hf
          apply mem_union_right
          simp [E,orient,at',bf]
        · have vx : v≠x := hg.ne.symm
          have at' : a=true := by simpa [extend] using ht
          have cf : c v=false := by simpa [extend,vx,vy] using hf
          have vr : v∈row G c x y a := (in_row G).mpr ⟨vy,hg,by simp [at',cf]⟩
          exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨v,vr,by simp [orient,at']⟩)))
      · by_cases uy : u=y
        · subst u
          by_cases vx : v=x
          · subst v
            have af : a=false := by simpa [extend] using hf
            have bt : b=true := by simpa [extend,nx.symm] using ht
            apply mem_union_right
            simp [E,orient,af,bt]
          · have vy : v≠y := hg.ne.symm
            have bt : b=true := by simpa [extend,nx.symm] using ht
            have cf : c v=false := by simpa [extend,vx,vy] using hf
            have vr : v∈row G c y x b := (in_row G).mpr ⟨vx,hg,by simp [bt,cf]⟩
            exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨v,vr,by simp [orient,bt]⟩))
        · by_cases vx : v=x
          · subst v
            have af : a=false := by simpa [extend] using hf
            have ct : c u=true := by simpa [extend,ux,uy] using ht
            have ur : u∈row G c x y a := (in_row G).mpr ⟨uy,hg.symm,by simp [af,ct]⟩
            exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨u,ur,by simp [orient,af]⟩)))
          · by_cases vy : v=y
            · subst v
              have bf : b=false := by simpa [extend,nx.symm] using hf
              have ct : c u=true := by simpa [extend,ux,uy] using ht
              have ur : u∈row G c y x b := (in_row G).mpr ⟨ux,hg.symm,by simp [bf,ct]⟩
              exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨u,ur,by simp [orient,bf]⟩))
            · have ct : c u=true := by simpa [extend,ux,uy] using ht
              have cf : c v=false := by simpa [extend,vx,vy] using hf
              exact mem_union_left _ (mem_union_left _ (mem_union_left _
                (mem_filter.mpr ⟨(in_boundary G).mpr ⟨ct,cf,hg⟩,ux,uy,vx,vy⟩)))
    · intro h
      rcases mem_union.mp h with h|h
      · rcases mem_union.mp h with h|h
        · rcases mem_union.mp h with h|h
          · obtain ⟨old,ux,uy,vx,vy⟩ := mem_filter.mp h
            obtain ⟨ct,cf,adj⟩ := (in_boundary G).mp old
            exact (in_boundary G).mpr ⟨by simpa [extend,ux,uy] using ct,
              by simpa [extend,vx,vy] using cf,adj⟩
          · obtain ⟨z,hz,e⟩ := mem_image.mp h
            change orient x a z=(u,v) at e
            obtain ⟨zy,adj,ne⟩ := (in_row G).mp hz
            have zx := adj.ne.symm
            cases a
            · have zt : c z=true := by cases h : c z <;> simp_all
              obtain ⟨rfl,rfl⟩ := Prod.mk.inj e
              apply (in_boundary G).mpr
              exact ⟨by simp [extend,zx,zy,zt],by simp [extend],adj.symm⟩
            · have zf : c z=false := by cases h : c z <;> simp_all
              obtain ⟨rfl,rfl⟩ := Prod.mk.inj e
              apply (in_boundary G).mpr
              exact ⟨by simp [extend],by simp [extend,zx,zy,zf],adj⟩
        · obtain ⟨z,hz,e⟩ := mem_image.mp h
          change orient y b z=(u,v) at e
          obtain ⟨zx,adj,ne⟩ := (in_row G).mp hz
          have zy := adj.ne.symm
          cases b
          · have zt : c z=true := by cases h : c z <;> simp_all
            obtain ⟨rfl,rfl⟩ := Prod.mk.inj e
            apply (in_boundary G).mpr
            exact ⟨by simp [extend,zx,zy,zt],by simp [extend,nx.symm],adj.symm⟩
          · have zf : c z=false := by cases h : c z <;> simp_all
            obtain ⟨rfl,rfl⟩ := Prod.mk.inj e
            apply (in_boundary G).mpr
            exact ⟨by simp [extend,nx.symm],by simp [extend,zx,zy,zf],adj⟩
      · cases a <;> cases b
        · simp [E] at h
        · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (by simpa [E,orient,eq_comm] using h : (y,x)=(u,v))
          exact (in_boundary G).mpr ⟨by simp [extend,nx.symm],by simp [extend],xy.symm⟩
        · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (by simpa [E,orient,eq_comm] using h : (x,y)=(u,v))
          exact (in_boundary G).mpr ⟨by simp [extend],by simp [extend,nx.symm],xy⟩
        · simp [E] at h
  rw [split,card_union_of_disjoint apart3,card_union_of_disjoint apart2,card_union_of_disjoint apart1]
  simp [I,X,Y,card_image_of_injective _ (orient_inj x a),card_image_of_injective _ (orient_inj y b)]
  by_cases h : a=b <;> simp [E,mismatch,h]

theorem row_sum (c : V→Bool) {x y : V} (xy : G.Adj x y) (cub : G.degree x=3) :
    (row G c x y false).card+(row G c x y true).card=2 := by
  have eq : row G c x y false ∪ row G c x y true=(G.neighborFinset x).erase y := by
    ext z
    cases h : c z <;> simp [row,h]
  have d : Disjoint (row G c x y false) (row G c x y true) := by
    rw [disjoint_left]
    intro z a b
    have az := ((in_row G).mp a).2.2
    have bz := ((in_row G).mp b).2.2
    cases h : c z <;> contradiction
  rw [←card_union_of_disjoint d,eq,card_erase_of_mem ((mem_neighborFinset _ _ _).mpr xy),
    card_neighborFinset_eq_degree,cub]

omit [Fintype V] in
def OutsideTwo (c : V→Bool) (x y : V) (b : Bool) : Prop :=
  ∃ u v : V,u≠x∧u≠y∧v≠x∧v≠y∧u≠v∧c u=b∧c v=b

omit [DecidableRel G.Adj] in
theorem extended_lower (small : SquareCap.SmallTrivial G) (c : V→Bool) (x y : V)
    (pos : OutsideTwo c x y true) (neg : OutsideTwo c x y false) (a b : Bool) :
    4≤(boundary G (extend c x y a b)).card := by
  by_contra! fail
  rcases small (extend c x y a b) (by omega) with hp|hn
  · obtain ⟨u,v,ux,uy,vx,vy,ne,cu,cv⟩ := pos
    exact ne (hp u v (by simp [extend,ux,uy,cu]) (by simp [extend,vx,vy,cv]))
  · obtain ⟨u,v,ux,uy,vx,vy,ne,cu,cv⟩ := neg
    exact ne (hn u v (by simp [extend,ux,uy,cu]) (by simp [extend,vx,vy,cv]))

/-- In a cyclic-four cubic graph, an outside cut with two or more
vertices on each side must still have width at least 2 after the
marked adjacent pair is removed. At width 2, each shore meets one
neighbor of each removed vertex, no more and no less. -/
theorem outside_cut_balance (small : SquareCap.SmallTrivial G)
    (c : V→Bool) {x y : V} (xy : G.Adj x y) (cx : G.degree x=3) (cy : G.degree y=3)
    (pos : OutsideTwo c x y true) (neg : OutsideTwo c x y false) :
    2≤(innerCut G c x y).card ∧
      ((innerCut G c x y).card=2 →
        (row G c x y false).card=1 ∧ (row G c x y true).card=1 ∧
        (row G c y x false).card=1 ∧ (row G c y x true).card=1) := by
  have a0 := extended_lower G small c x y pos neg false false
  have a1 := extended_lower G small c x y pos neg true true
  have b0 := extended_lower G small c x y pos neg false true
  have b1 := extended_lower G small c x y pos neg true false
  rw [extended_boundary G c xy] at a0 a1 b0 b1
  have s := row_sum G c xy cx
  have t := row_sum G c xy.symm cy
  simp [mismatch] at a0 a1 b0 b1
  omega

#print axioms extended_boundary
#print axioms outside_cut_balance
end
end KelmansCactus.AtomicBridge.RemoteT2PairCounts
