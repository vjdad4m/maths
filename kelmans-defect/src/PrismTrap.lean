import CenterRigidity
import FourReplace
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Tactic.FinCases

open Finset SimpleGraph
namespace KelmansCactus.PrismTrap
open CenterRigidity FourReplace

abbrev m (k : ℕ) := 9*k+3
abbrev span (k : ℕ) := 3*k+1

local macro "lomega" : tactic => `(tactic| (first | omega | (simp only [m,span] at * <;> omega)))
abbrev Vertex (k : ℕ) := Fin (m k) ⊕ Fin (m k)

private def swap (k x : ℕ) : ℕ :=
  if x/3<k ∧ x%3=1 then x+1 else
  if x/3<k ∧ x%3=2 then x-1 else
  if k<x/3 ∧ x/3≤2*k ∧ x%3=0 then x+1 else
  if k<x/3 ∧ x/3≤2*k ∧ x%3=1 then x-1 else x

theorem swap_near (k x : ℕ) : swap k x ≤ x+1 ∧ x≤swap k x+1 := by
  unfold swap
  split <;> try lomega
  split <;> try lomega
  split <;> try lomega
  split <;> lomega

private theorem swap_bound {k x : ℕ} (h : x < m k) : swap k x < m k := by
  unfold swap
  split <;> try lomega
  split <;> try lomega
  split <;> try lomega
  split <;> lomega

private theorem swap_sq (k x : ℕ) : swap k (swap k x)=x := by
  by_cases a : x/3<k ∧ x%3=1
  · have q : (x+1)/3=x/3 := by lomega
    have t : (x+1)%3=2 := by lomega
    rw [show swap k x=x+1 by simp [swap,a]]
    have a0 : ¬ ((x+1)/3<k ∧ (x+1)%3=1) := by lomega
    have a1 : (x+1)/3<k ∧ (x+1)%3=2 := by lomega
    simp [swap,a0,a1]
  by_cases b : x/3<k ∧ x%3=2
  · have q : (x-1)/3=x/3 := by lomega
    have t : (x-1)%3=1 := by lomega
    rw [show swap k x=x-1 by simp [swap,a,b]]
    have a0 : (x-1)/3<k ∧ (x-1)%3=1 := by lomega
    rw [show swap k (x-1)=x-1+1 by simp [swap,a0]]
    lomega
  by_cases c : k<x/3 ∧ x/3≤2*k ∧ x%3=0
  · have q : (x+1)/3=x/3 := by lomega
    have t : (x+1)%3=1 := by lomega
    rw [show swap k x=x+1 by simp [swap,a,b,c]]
    have a0 : ¬ ((x+1)/3<k ∧ (x+1)%3=1) := by lomega
    have a1 : ¬ ((x+1)/3<k ∧ (x+1)%3=2) := by lomega
    have c0 : ¬ (k<(x+1)/3 ∧ (x+1)/3≤2*k ∧ (x+1)%3=0) := by lomega
    have c1 : k<(x+1)/3 ∧ (x+1)/3≤2*k ∧ (x+1)%3=1 := by lomega
    simp only [swap,if_neg a0,if_neg a1,if_neg c0,if_pos c1]
    lomega
  by_cases d : k<x/3 ∧ x/3≤2*k ∧ x%3=1
  · have q : (x-1)/3=x/3 := by lomega
    have t : (x-1)%3=0 := by lomega
    rw [show swap k x=x-1 by simp only [swap,if_neg a,if_neg b,if_neg c,if_pos d]]
    have a0 : ¬ ((x-1)/3<k ∧ (x-1)%3=1) := by lomega
    have a1 : ¬ ((x-1)/3<k ∧ (x-1)%3=2) := by lomega
    have c0 : k<(x-1)/3 ∧ (x-1)/3≤2*k ∧ (x-1)%3=0 := by lomega
    rw [show swap k (x-1)=x-1+1 by simp only [swap,if_neg a0,if_neg a1,if_pos c0]]
    lomega
  · rw [show swap k x=x by simp [swap,a,b,c,d],show swap k x=x by simp [swap,a,b,c,d]]

def rung (k : ℕ) : Fin (m k) ≃ Fin (m k) where
  toFun x := ⟨swap k x.val,swap_bound x.isLt⟩
  invFun x := ⟨swap k x.val,swap_bound x.isLt⟩
  left_inv x := Fin.ext (swap_sq k x.val)
  right_inv x := Fin.ext (swap_sq k x.val)

def graph (k : ℕ) : SimpleGraph (Vertex k) :=
  glue (cycleGraph (m k)) (cycleGraph (m k)) id (rung k)

instance (k : ℕ) : DecidableRel (graph k).Adj := by
  unfold graph
  infer_instance

private theorem rail_del_one (n : ℕ) (D : Finset (Fin (n+3))) (small : D.card≤1) :
    ((cycleGraph (n+3)).induce (remains D)).Connected := by
  by_cases empty : D.card=0
  · rw [card_eq_zero.mp empty]
    let f : cycleGraph (n+3) →g (cycleGraph (n+3)).induce (remains (∅ : Finset (Fin (n+3)))) :=
      ⟨fun x => ⟨x,not_mem_empty x⟩,fun h => h⟩
    exact cycleGraph_connected.map f (fun y => ⟨y.val,Subtype.ext rfl⟩)
  · have one : D.card=1 := by lomega
    obtain ⟨d,rfl⟩ := card_eq_one.mp one
    let f : pathGraph (n+2) →g (cycleGraph (n+3)).induce (remains ({d} : Finset (Fin (n+3)))) := by
      refine ⟨fun u => ⟨d+u.succ,?_⟩,?_⟩
      · change d+u.succ ∉ ({d} : Finset (Fin (n+3)))
        intro h
        have h' : d+u.succ=d+0 := by simpa using mem_singleton.mp h
        exact Fin.succ_ne_zero u (add_left_cancel h')
      · intro x y h
        change (cycleGraph (n+3)).Adj (d+x.succ) (d+y.succ)
        rw [cycleGraph_adj',add_sub_add_left_eq_sub,add_sub_add_left_eq_sub]
        have hh := pathGraph_adj.mp h
        rcases hh with hh | hh
        · right
          rw [Fin.coe_sub_iff_le.mpr (by change x.val+1≤y.val+1; lomega)]
          change y.val+1-(x.val+1)=1
          lomega
        · left
          rw [Fin.coe_sub_iff_le.mpr (by change y.val+1≤x.val+1; lomega)]
          change x.val+1-(y.val+1)=1
          lomega
    apply (pathGraph_connected (n+1)).map f
    intro v
    have nv : v.val-d≠0 := by
      intro h
      exact v.property (mem_singleton.mpr (sub_eq_zero.mp h))
    refine ⟨(v.val-d).pred nv,?_⟩
    apply Subtype.ext
    change d + ((v.val-d).pred nv).succ = v.val
    rw [Fin.succ_pred]
    calc
      d+(v.val-d)=(v.val-d)+d := add_comm _ _
      _ = v.val := sub_add_cancel _ _

theorem cubic (k : ℕ) (x : Vertex k) : (graph k).degree x=3 := by
  cases x with
  | inl v =>
    unfold graph
    rw [left_degree Function.injective_id,if_pos (show ∃ i, id i=v from ⟨v,rfl⟩)]
    exact congrArg (·+1) (cycleGraph_degree_three_le (n:=9*k) (v:=v))
  | inr v =>
    unfold graph
    rw [right_degree (rung k).injective,if_pos ((rung k).surjective v)]
    exact congrArg (·+1) (cycleGraph_degree_three_le (n:=9*k) (v:=v))

theorem three_connected (k : ℕ) : KelmansStarter.ThreeConnected (graph k) := by
  exact perfect_rail_glue_three_connected (Equiv.refl _) (rung k)
    (by simp) (rail_del_one (9*k)) (rail_del_one (9*k))

def column (k : ℕ) : Vertex k → ℕ
  | .inl x => x.val
  | .inr x => x.val

def potential (k : ℕ) (x : Vertex k) : ℕ :=
  min (column k x) (m k-column k x)

theorem cyclic_neighbor {n : ℕ} (u v : Fin n)
    (a : (cycleGraph n).Adj u v) :
    u.val≤v.val+1 ∧ v.val≤u.val+1 ∨
      (u.val=0 ∧ v.val+1=n) ∨ (v.val=0 ∧ u.val+1=n) := by
  have hu := u.isLt
  have hv := v.isLt
  have h := cycleGraph_adj'.mp a
  haveI : NeZero n := ⟨by lomega⟩
  rcases h with h | h
  · rw [Fin.sub_def] at h
    change (n-v.val+u.val)%n=1 at h
    have q := Nat.div_add_mod (n-v.val+u.val) n
    have q' : (n-v.val+u.val)/n ≤ 1 := by
      apply Nat.lt_succ_iff.mp
      apply (Nat.div_lt_iff_lt_mul (by lomega)).mpr
      lomega
    have eqs := Nat.le_one_iff_eq_zero_or_eq_one.mp q'
    rcases eqs with eq|eq <;> simp only [eq,h,zero_mul,one_mul,zero_add] at q <;> lomega
  · rw [Fin.sub_def] at h
    change (n-u.val+v.val)%n=1 at h
    have q := Nat.div_add_mod (n-u.val+v.val) n
    have q' : (n-u.val+v.val)/n ≤ 1 := by
      apply Nat.lt_succ_iff.mp
      apply (Nat.div_lt_iff_lt_mul (by lomega)).mpr
      lomega
    have eqs := Nat.le_one_iff_eq_zero_or_eq_one.mp q'
    rcases eqs with eq|eq <;> simp only [eq,h,zero_mul,one_mul,zero_add] at q <;> lomega

theorem potential_near (k : ℕ) (x y : Vertex k) (h : (graph k).Adj x y) :
    potential k y ≤ potential k x+1 := by
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      change (cycleGraph (m k)).Adj x y at h
      have hh := cyclic_neighbor x y h
      change min y.val (m k-y.val) ≤ min x.val (m k-x.val)+1
      lomega
    | inr y =>
      change ∃ i, id i=x ∧ rung k i=y at h
      obtain ⟨i,rfl,rfl⟩ := h
      have hh := swap_near k i.val
      change min (swap k i.val) (m k-swap k i.val) ≤ min i.val (m k-i.val)+1
      lomega
  | inr x =>
    cases y with
    | inl y =>
      change ∃ i, id i=y ∧ rung k i=x at h
      obtain ⟨i,rfl,rfl⟩ := h
      have hh := swap_near k i.val
      change min i.val (m k-i.val) ≤ min (swap k i.val) (m k-swap k i.val)+1
      lomega
    | inr y =>
      change (cycleGraph (m k)).Adj x y at h
      have hh := cyclic_neighbor x y h
      change min y.val (m k-y.val) ≤ min x.val (m k-x.val)+1
      lomega

#print axioms cubic
#print axioms three_connected
#print axioms potential_near

private def oldLeft (k c : ℕ) : Prop :=
   (c<span k ∧ c%3=2) ∨
   (span k<c ∧ c<2*span k ∧ c%3=0) ∨
   (2*span k<c ∧ c%3=1)

private instance (k c : ℕ) : Decidable (oldLeft k c) := by unfold oldLeft; infer_instance

private def standard (k : ℕ) (x : Vertex k) : Prop := column k x%3=1
private instance (k : ℕ) (x : Vertex k) : Decidable (standard k x) := by unfold standard; infer_instance

private def oldCenter (k : ℕ) : Vertex k → Prop
  | .inl c => oldLeft k c.val
  | .inr c => c.val%3=1

private instance (k : ℕ) (x : Vertex k) : Decidable (oldCenter k x) := by cases x <;> unfold oldCenter <;> infer_instance

def oldCenters (k : ℕ) : Finset (Vertex k) := univ.filter (oldCenter k)
def stdCenters (k : ℕ) : Finset (Vertex k) := univ.filter (standard k)

private def p0 {k : ℕ} (v : Fin (m k)) : Fin (m k) := ⟨v.val-1,by have := v.isLt; lomega⟩
private def p2 {k : ℕ} (v : Fin (m k)) : Fin (m k) := ⟨min (v.val+1) (m k-1),by have := v.isLt; lomega⟩

def block (k : ℕ) : Vertex k → Finset (Vertex k)
  | .inl v => {Sum.inl (p0 v), Sum.inl v, Sum.inl (p2 v)}
  | .inr v => {Sum.inr (p0 v), Sum.inr v, Sum.inr (p2 v)}

def inner (k : ℕ) (v : Vertex k) : Prop :=
  1 ≤ column k v ∧ column k v+1 < m k

theorem block_mem {k : ℕ} {v x : Vertex k} (hv : inner k v) :
    x∈block k v ↔ (v.isLeft=x.isLeft) ∧
      column k x≤column k v+1 ∧ column k v≤column k x+1 := by
  have num {u w : Fin (m k)} (h : 1≤u.val ∧ u.val+1<m k) :
      (w=p0 u ∨ w=u ∨ w=p2 u) ↔ w.val≤u.val+1 ∧ u.val≤w.val+1 := by
    have mx : min (u.val+1) (m k-1)=u.val+1 := Nat.min_eq_left (by lomega)
    simp only [Fin.ext_iff,p0,p2,mx]
    lomega
  cases v <;> cases x
  · simpa only [block,mem_insert,mem_singleton,Sum.inl.injEq,Sum.isLeft,true_and] using num hv
  · simp [block]
  · simp [block]
  · simpa only [block,mem_insert,mem_singleton,Sum.inr.injEq,Sum.isLeft,true_and] using num hv

private theorem block_shape {k : ℕ} {v : Vertex k} (hv : inner k v) :
    (block k v).card=3 ∧ v∈block k v ∧ ∀ x∈block k v, x≠v → (graph k).Adj v x := by
  have hcr (x : Fin (m k)) (hi : 1≤x.val ∧ x.val+1<m k) :
      p0 x≠x ∧ p0 x≠p2 x ∧ x≠p2 x := by
    simp only [ne_eq,Fin.ext_iff,p0,p2]
    lomega
  have card : (block k v).card=3 := by
    cases v with
    | inl c =>
      obtain ⟨ha,hb,hc⟩ := hcr c hv
      simp [block,ha,hb,hc]
    | inr c =>
      obtain ⟨ha,hb,hc⟩ := hcr c hv
      simp [block,ha,hb,hc]
  refine ⟨card,(block_mem hv).mpr ⟨rfl,by lomega,by lomega⟩,?_⟩
  intro x hx ne
  have hh := (block_mem hv).mp hx
  cases v with
  | inl c =>
    cases x with
    | inl v =>
      have nn : v.val≠c.val := fun eq => ne (congrArg Sum.inl (Fin.ext eq))
      change (cycleGraph (m k)).Adj c v
      apply pathGraph_le_cycleGraph
      rw [pathGraph_adj]
      have hh2 : v.val≤c.val+1 ∧ c.val≤v.val+1 := hh.2
      lomega
    | inr v => cases hh.1
  | inr c =>
    cases x with
    | inl v => cases hh.1
    | inr v =>
      have nn : v.val≠c.val := fun eq => ne (congrArg Sum.inr (Fin.ext eq))
      change (cycleGraph (m k)).Adj c v
      apply pathGraph_le_cycleGraph
      rw [pathGraph_adj]
      have hh2 : v.val≤c.val+1 ∧ c.val≤v.val+1 := hh.2
      lomega

private theorem std_inner (k : ℕ) {x : Vertex k} (hx : standard k x) : inner k x := by
  have lim : column k x<m k := by cases x <;> exact Fin.isLt _
  unfold standard at hx
  unfold inner
  lomega

theorem old_inner (k : ℕ) {x : Vertex k} (hx : oldCenter k x) : inner k x := by
  cases x with
  | inr x => exact std_inner k (x:=Sum.inr x) hx
  | inl x =>
    have lim := x.isLt
    change oldLeft k x.val at hx
    unfold oldLeft at hx
    change 1≤x.val ∧ x.val+1<m k
    lomega

private theorem left_spread {k c d : ℕ} (h : oldLeft k c) (h' : oldLeft k d) (ne : c≠d) :
    c+3≤d ∨ d+3≤c := by
  unfold oldLeft at h h'
  rcases h with h|h|h <;> rcases h' with h'|h'|h' <;> lomega

private theorem old_spread (k : ℕ) {c d : Vertex k} (cn : oldCenter k c) (dn : oldCenter k d)
    (same : c.isLeft=d.isLeft) (ne : c≠d) :
    column k c+3≤column k d ∨ column k d+3≤column k c := by
  cases c <;> cases d
  · exact left_spread cn dn (fun eq => ne (congrArg Sum.inl (Fin.ext eq)))
  · cases same
  · cases same
  · rename_i c d
    have nn : c.val≠d.val := fun eq => ne (congrArg Sum.inr (Fin.ext eq))
    change c.val%3=1 at cn
    change d.val%3=1 at dn
    change c.val+3≤d.val ∨ d.val+3≤c.val
    lomega

private theorem std_spread (k : ℕ) {c d : Vertex k} (cn : standard k c) (dn : standard k d)
    (same : c.isLeft=d.isLeft) (ne : c≠d) :
    column k c+3≤column k d ∨ column k d+3≤column k c := by
  unfold standard at cn dn
  have neq : column k c ≠ column k d := by
    intro h
    apply ne
    cases c <;> cases d
    · exact congrArg Sum.inl (Fin.ext h)
    · cases same
    · cases same
    · exact congrArg Sum.inr (Fin.ext h)
  lomega

def hole (k : ℕ) (i : Fin 3) : Vertex k :=
  Sum.inl ⟨if i.val=0 then 0 else if i.val=1 then span k else 2*span k,by
    split <;> try lomega
    split <;> lomega⟩

def holes (k : ℕ) : Finset (Vertex k) := univ.image (hole k)

theorem three_holes (k : ℕ) : (holes k).card=3 := by
  have inj : Function.Injective (hole k) := by
    intro i j eq
    have e := congrArg (column k) eq
    fin_cases i <;> fin_cases j <;> first | rfl | (simp [hole,column] at e ⊢)
  simp [holes,card_image_of_injective _ inj]

theorem holes_left (k : ℕ) (x : Fin (m k)) :
    Sum.inl x∈holes k ↔ x.val=0 ∨ x.val=span k ∨ x.val=2*span k := by
  constructor
  · intro h
    obtain ⟨i,_,eq⟩ := mem_image.mp h
    have e := congrArg (column k) eq
    fin_cases i <;> simp [hole,column] at e <;> lomega
  · intro h
    rcases h with h|h|h
    · exact mem_image.mpr ⟨0,mem_univ _,congrArg Sum.inl (Fin.ext h.symm)⟩
    · exact mem_image.mpr ⟨1,mem_univ _,congrArg Sum.inl (Fin.ext h.symm)⟩
    · exact mem_image.mpr ⟨2,mem_univ _,congrArg Sum.inl (Fin.ext h.symm)⟩

theorem holes_right (k : ℕ) (x : Fin (m k)) : Sum.inr x∉holes k := by
  intro h
  obtain ⟨i,_,eq⟩ := mem_image.mp h
  cases eq

private theorem interval_center {s t x : ℕ} (lo : s≤x) (hi : x<s+3*t) :
    ∃ c, s+1≤c ∧ c+1<s+3*t ∧ c%3=(s+1)%3 ∧ x≤c+1 ∧ c≤x+1 := by
  refine ⟨s+3*((x-s)/3)+1,?_⟩
  lomega

private theorem old_covering (k : ℕ) {x : Vertex k} (hx : x∉holes k) :
    ∃ c∈oldCenters k, x∈block k c := by
  cases x with
  | inr x =>
    have lim := x.isLt
    obtain ⟨c,cl,ch,cm,cx,xc⟩ := interval_center (s:=0) (t:=3*k+1) (x:=x.val) (by lomega) (by lomega)
    let y : Fin (m k) := ⟨c,by lomega⟩
    have hy : Sum.inr y∈oldCenters k := mem_filter.mpr ⟨mem_univ _,by change c%3=1; lomega⟩
    exact ⟨Sum.inr y,hy,(block_mem (old_inner k (mem_filter.mp hy).2)).mpr ⟨rfl,cx,xc⟩⟩
  | inl x =>
    have lim := x.isLt
    have nh : ¬ (x.val=0 ∨ x.val=span k ∨ x.val=2*span k) := fun h => hx ((holes_left k x).mpr h)
    suffices ∃ c, c<m k ∧ oldLeft k c ∧ x.val≤c+1 ∧ c≤x.val+1 by
      obtain ⟨c,lim,cc,cx,xc⟩ := this
      let y : Fin (m k) := ⟨c,lim⟩
      have hy : Sum.inl y∈oldCenters k := mem_filter.mpr ⟨mem_univ _,cc⟩
      exact ⟨Sum.inl y,hy,(block_mem (old_inner k (mem_filter.mp hy).2)).mpr ⟨rfl,cx,xc⟩⟩
    by_cases a : x.val<span k
    · obtain ⟨c,cl,ch,cm,cx,xc⟩ := interval_center (s:=1) (t:=k) (x:=x.val) (by lomega) (by lomega)
      exact ⟨c,by lomega,Or.inl ⟨by lomega,by lomega⟩,cx,xc⟩
    · by_cases b : x.val<2*span k
      · obtain ⟨c,cl,ch,cm,cx,xc⟩ := interval_center (s:=span k+1) (t:=k) (x:=x.val) (by lomega) (by lomega)
        exact ⟨c,by lomega,Or.inr (Or.inl ⟨by lomega,by lomega,by lomega⟩),cx,xc⟩
      · obtain ⟨c,cl,ch,cm,cx,xc⟩ := interval_center (s:=2*span k+1) (t:=k) (x:=x.val) (by lomega) (by lomega)
        exact ⟨c,by lomega,Or.inr (Or.inr ⟨by lomega,by lomega⟩),cx,xc⟩

private theorem old_block_avoids (k : ℕ) {c x : Vertex k} (hc : c∈oldCenters k)
    (hx : x∈block k c) : x∉holes k := by
  have hc' := (mem_filter.mp hc).2
  have h := (block_mem (old_inner k hc')).mp hx
  cases x with
  | inr x => exact holes_right k x
  | inl x =>
    rw [holes_left]
    cases c with
    | inr c => cases h.1
    | inl c =>
      change oldLeft k c.val at hc'
      have nn : x.val≤c.val+1 ∧ c.val≤x.val+1 := h.2
      unfold oldLeft at hc'
      lomega

theorem old_layout (k : ℕ) :
    Layout (graph k) (oldCenters k) (univ\holes k) (block k) := by
  refine ⟨fun c hc => block_shape (old_inner k (mem_filter.mp hc).2),?_,?_⟩
  · intro c hc d hd ne
    change Disjoint (block k c) (block k d)
    rw [disjoint_left]
    intro v cv dv
    have cp := (mem_filter.mp hc).2
    have dp := (mem_filter.mp hd).2
    obtain ⟨sc,a,b⟩ := (block_mem (old_inner k cp)).mp cv
    obtain ⟨sd,e,f⟩ := (block_mem (old_inner k dp)).mp dv
    have q := old_spread k cp dp (sc.trans sd.symm) ne
    lomega
  · ext x
    constructor
    · intro h
      obtain ⟨c,hc,cx⟩ := mem_biUnion.mp h
      exact mem_sdiff.mpr ⟨mem_univ _,old_block_avoids k hc cx⟩
    · intro h
      obtain ⟨c,hc,cx⟩ := old_covering k (mem_sdiff.mp h).2
      exact mem_biUnion.mpr ⟨c,hc,cx⟩

theorem std_layout (k : ℕ) : Layout (graph k) (stdCenters k) univ (block k) := by
  refine ⟨fun c hc => block_shape (std_inner k (mem_filter.mp hc).2),?_,?_⟩
  · intro c hc d hd ne
    change Disjoint (block k c) (block k d)
    rw [disjoint_left]
    intro v cv dv
    have cp := (mem_filter.mp hc).2
    have dp := (mem_filter.mp hd).2
    obtain ⟨sc,a,b⟩ := (block_mem (std_inner k cp)).mp cv
    obtain ⟨sd,e,f⟩ := (block_mem (std_inner k dp)).mp dv
    have q := std_spread k cp dp (sc.trans sd.symm) ne
    lomega
  · apply eq_univ_of_forall
    intro x
    have lim : column k x < m k := by cases x <;> exact Fin.isLt _
    obtain ⟨c,cl,ch,cm,cx,xc⟩ := interval_center (s:=0) (t:=3*k+1) (x:=column k x) (by lomega) (by lomega)
    let y : Fin (m k) := ⟨c,by lomega⟩
    cases x
    · have hy : Sum.inl y∈stdCenters k := mem_filter.mpr ⟨mem_univ _,by change c%3=1; lomega⟩
      exact mem_biUnion.mpr ⟨Sum.inl y,hy,(block_mem (std_inner k (mem_filter.mp hy).2)).mpr ⟨rfl,cx,xc⟩⟩
    · have hy : Sum.inr y∈stdCenters k := mem_filter.mpr ⟨mem_univ _,by change c%3=1; lomega⟩
      exact mem_biUnion.mpr ⟨Sum.inr y,hy,(block_mem (std_inner k (mem_filter.mp hy).2)).mpr ⟨rfl,cx,xc⟩⟩

#print axioms old_layout
#print axioms std_layout

def exceptional (k : ℕ) : Vertex k := Sum.inr ⟨span k,by lomega⟩

def mate (k : ℕ) : Vertex k → Vertex k
  | .inl v => Sum.inr (rung k v)
  | .inr v => Sum.inl (rung k v)

theorem mate_injective (k : ℕ) : Function.Injective (mate k) := by
  intro x y e
  cases x <;> cases y
  · exact congrArg Sum.inl ((rung k).injective (Sum.inr.inj e))
  · cases e
  · cases e
  · exact congrArg Sum.inr ((rung k).injective (Sum.inl.inj e))

private theorem to_right_center {k x : ℕ} (ox : oldLeft k x) :
    (swap k x)%3=1 := by
  unfold oldLeft at ox
  rcases ox with ⟨h,mod⟩ | ⟨a,b,mod⟩ | ⟨a,mod⟩
  · have a : x/3<k ∧ x%3=2 := by lomega
    have b : ¬ (x/3<k ∧ x%3=1) := by lomega
    rw [show swap k x=x-1 by simp [swap,a,b]]
    lomega
  · have c : k<x/3 ∧ x/3≤2*k ∧ x%3=0 := by lomega
    have h₁ : ¬ (x/3<k ∧ x%3=1) := by lomega
    have h₂ : ¬ (x/3<k ∧ x%3=2) := by lomega
    rw [show swap k x=x+1 by simp [swap,h₁,h₂,c]]
    lomega
  · have t : 2*k < x/3 := by lomega
    have a0 : ¬ (x/3<k ∧ x%3=1) := by lomega
    have a1 : ¬ (x/3<k ∧ x%3=2) := by lomega
    have a2 : ¬ (k<x/3 ∧ x/3≤2*k ∧ x%3=0) := by lomega
    have a3 : ¬ (k<x/3 ∧ x/3≤2*k ∧ x%3=1) := by lomega
    rw [show swap k x=x by simp [swap,a0,a1,a2,a3]]
    exact mod

private theorem to_left_center {k x : ℕ} (mod : x%3=1) (ne : x≠span k) :
    oldLeft k (swap k x) := by
  by_cases h : x/3<k
  · unfold oldLeft
    rw [show swap k x=x+1 by simp [swap,h,mod]]
    lomega
  · have a : k<x/3 := by lomega
    by_cases hb : x/3≤2*k
    · have z : k<x/3 ∧ x/3≤2*k ∧ x%3=1 := ⟨a,hb,mod⟩
      rw [show swap k x=x-1 by simp [swap,h,mod,z]]
      unfold oldLeft
      lomega
    · have z : ¬(k<x/3 ∧ x/3≤2*k ∧ x%3=1) := by lomega
      rw [show swap k x=x by simp [swap,h,mod,z,hb]]
      unfold oldLeft
      lomega

theorem mate_old (k : ℕ) (c : Vertex k) (hc : c∈oldCenters k\{exceptional k}) :
    mate k c∈oldCenters k ∧ mate k c≠c := by
  obtain ⟨cC,cE⟩ := mem_sdiff.mp hc
  have ctr := (mem_filter.mp cC).2
  cases c with
  | inl c =>
    refine ⟨mem_filter.mpr ⟨mem_univ _,?_⟩,by simp [mate]⟩
    exact to_right_center ctr
  | inr c =>
    refine ⟨mem_filter.mpr ⟨mem_univ _,?_⟩,by simp [mate]⟩
    have ne : c.val≠span k := by
      intro eq
      exact cE (mem_singleton.mpr (congrArg Sum.inr (Fin.ext eq)))
    exact to_left_center ctr ne

theorem kept_neighbors (k : ℕ) (c : Vertex k) (hc : c∈oldCenters k\{exceptional k})
    (v : Vertex k) (e : (graph k).Adj c v) : v∈block k c ∨ v=mate k c := by
  have hi := old_inner k (mem_filter.mp (mem_sdiff.mp hc).1).2
  cases c with
  | inl c =>
    cases v with
    | inl v =>
      left
      have h := cyclic_neighbor c v e
      have h0 : 1≤c.val ∧ c.val+1<m k := hi
      apply (block_mem hi).mpr
      refine ⟨rfl,?_⟩
      change v.val≤c.val+1 ∧ c.val≤v.val+1
      lomega
    | inr v =>
      right
      change ∃ i, i=c ∧ rung k i=v at e
      obtain ⟨i,rfl,h⟩ := e
      exact congrArg Sum.inr h.symm
  | inr c =>
    cases v with
    | inl v =>
      right
      change ∃ i, i=v ∧ rung k i=c at e
      obtain ⟨i,rfl,h⟩ := e
      apply congrArg Sum.inl
      rw [← h]
      exact (rung k).left_inv i |>.symm
    | inr v =>
      left
      have h := cyclic_neighbor c v e
      have h0 : 1≤c.val ∧ c.val+1<m k := hi
      apply (block_mem hi).mpr
      refine ⟨rfl,?_⟩
      change v.val≤c.val+1 ∧ c.val≤v.val+1
      lomega

private theorem holes_nonadjacent (k : ℕ) (hk : 1≤k)
    {u v : Vertex k} (uh : u∈holes k) (vh : v∈holes k) : ¬ (graph k).Adj u v := by
  obtain ⟨i,_,rfl⟩ := mem_image.mp uh
  obtain ⟨j,_,rfl⟩ := mem_image.mp vh
  intro e
  let f : Fin 3 → Fin (m k) := fun i => ⟨if i.val=0 then 0 else if i.val=1 then span k else 2*span k, by
    split <;> try lomega
    split <;> lomega⟩
  have e' : (cycleGraph (m k)).Adj (f i) (f j) := e
  have ee := cyclic_neighbor (f i) (f j) e'
  fin_cases i <;> fin_cases j <;> simp [f] at ee
  all_goals first | exact (cycleGraph (m k)).loopless _ e' | lomega

theorem old_inclusion_maximal (k : ℕ) (hk : 1≤k) :
    ¬ ∃ t⊆holes k, KelmansStarter.IsTile (graph k) t := by
  rintro ⟨t,ts,hc,c,ct,star⟩
  have nt : ¬ t⊆{c} := by
    intro hn
    have sz := card_le_card hn
    rw [hc,card_singleton] at sz
    lomega
  obtain ⟨x,xt,xn⟩ := Finset.not_subset.mp nt
  exact holes_nonadjacent k hk (ts ct) (ts xt) (star x xt (fun ee => xn (mem_singleton.mpr ee)))

/-- Even allowing the leaves of every retained centre to move,
arbitrarily many old centres may need replacement. -/
theorem required_drops (k : ℕ) {C' : Finset (Vertex k)} {B' : Vertex k→Finset (Vertex k)}
    (fresh : Layout (graph k) C' univ B') :
    3*k+1 ≤ 6*((oldCenters k)\C').card+5 := by
  have ha : hole k 0∈holes k := mem_image.mpr ⟨0,mem_univ _,rfl⟩
  have hb : hole k 1∈holes k := mem_image.mpr ⟨1,mem_univ _,rfl⟩
  have h := rigidity_potential (mate k) (old_layout k) fresh (three_holes k)
    (mate_old k) (mate_injective k).injOn (kept_neighbors k) ha hb (potential k) (potential_near k)
  have r0 : potential k (hole k 0)=0 := by simp [potential,hole,column]
  have r1 : potential k (hole k 1)=3*k+1 := by
    change min (3*k+1) (m k-(3*k+1))=3*k+1
    exact Nat.min_eq_left (by lomega)
  rw [r0,r1,card_singleton] at h
  lomega

theorem ordinary_factor (k : ℕ) : KelmansStarter.HasP3Factor (graph k) := by
  obtain ⟨P,hP⟩ := layout_local (std_layout k)
  exact ⟨P,hP.tile,hP.disj,hP.cover⟩

/-- On a cubic 3-connected graph already known to have a factor, a
near-perfect inclusion-maximal packing can be inaccessible by any fixed
bound on old-centre replacements. This is not a Kelmans counterexample. -/
theorem beyond_budget (d : ℕ) :
    let k := 2*d+2
    6 ∣ Fintype.card (Vertex k) ∧
    KelmansStarter.ThreeConnected (graph k) ∧
    (∀ v, (graph k).degree v=3) ∧
    KelmansStarter.HasP3Factor (graph k) ∧
    (holes k).card=3 ∧
    Layout (graph k) (oldCenters k) (univ\holes k) (block k) ∧
    (¬ ∃ t⊆holes k, KelmansStarter.IsTile (graph k) t) ∧
    ∀ {C' : Finset (Vertex k)} {B' : Vertex k→Finset (Vertex k)},
      Layout (graph k) C' univ B' → d < ((oldCenters k)\C').card := by
  dsimp only
  let k := 2*d+2
  have div : 6 ∣ Fintype.card (Vertex k) := by
    simp only [Fintype.card_sum,Fintype.card_fin]
    exact ⟨3*k+1,by lomega⟩
  refine ⟨div,three_connected k,cubic k,ordinary_factor k,three_holes k,old_layout k,
    old_inclusion_maximal k (by lomega),?_⟩
  intro C' B' h
  have z := required_drops k h
  change d < ((oldCenters k)\C').card
  dsimp [k] at z ⊢
  lomega


/-- A centre-free statement of the lower bound: any factor must break
more than d old tiles, regardless of how one orients the new factor. -/
theorem beyond_tile_budget (d : ℕ) :
    let k := 2*d+2
    ∀ P : Finset (Finset (Vertex k)), Assemble.LocalPart (graph k) P univ →
      d < ((oldCenters k).filter (fun c => block k c∉P)).card := by
  dsimp only
  let k := 2*d+2
  intro P hp
  obtain ⟨C',B',h,sub⟩ := keep_common_tiles (old_layout k) hp
  have cap := card_le_card sub
  have req := required_drops k h
  change d < ((oldCenters k).filter (fun c => block k c∉P)).card
  dsimp [k] at req cap ⊢
  lomega

#print axioms beyond_tile_budget

#print axioms required_drops
#print axioms beyond_budget
end KelmansCactus.PrismTrap
