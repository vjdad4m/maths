import ThetaAsymmetricFaithful
import Mathlib.Tactic.FinCases

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaAsymmetricFaithfulGeometry
open SquareCap (boundary)
open ThetaAsymmetricFaithfulTable (Wire oldWires newWires cost)
open ThetaAsymmetricFaithful (ambient candidate glue link linkAdj)
open ThetaSevenFaithfulCap (core9 core3 edges9 edges3)
noncomputable section

variable {V T : Type*} [Fintype V] [Fintype T]

omit [Fintype V] [Fintype T] in
private def adjacency (B : SimpleGraph V) (K : SimpleGraph T) (p : Wire→V)
    (r : Wire→T) : V⊕T→V⊕T→Prop
  | .inl x,.inl y => B.Adj x y
  | .inr x,.inr y => K.Adj x y
  | .inl x,.inr y => ∃ i,p i=x∧r i=y
  | .inr y,.inl x => ∃ i,p i=x∧r i=y

omit [Fintype V] [Fintype T] in
def attach (B : SimpleGraph V) (K : SimpleGraph T) (p : Wire→V) (r : Wire→T) : SimpleGraph (V⊕T) where
  Adj := adjacency B K p r
  symm := by intro x y h; cases x <;> cases y <;> first | exact h | exact h.symm
  loopless := by intro x h; cases x; exact B.loopless _ h; exact K.loopless _ h

omit [Fintype V] [Fintype T] in
instance [DecidableEq V] [DecidableEq T] (B : SimpleGraph V) [DecidableRel B.Adj]
    (K : SimpleGraph T) [DecidableRel K.Adj] (p : Wire→V) (r : Wire→T) :
    DecidableRel (attach B K p r).Adj := by
  rintro (x|x) (y|y)
  · exact inferInstanceAs (Decidable (B.Adj x y))
  · exact inferInstanceAs (Decidable (∃ i : Wire,p i=x∧r i=y))
  · exact inferInstanceAs (Decidable (∃ i : Wire,p i=y∧r i=x))
  · exact inferInstanceAs (Decidable (K.Adj x y))

private theorem in_boundary {G : SimpleGraph V} {c : V → Bool} {e : V × V} :
    e ∈ boundary G c ↔ c e.1 = true ∧ c e.2 = false ∧ G.Adj e.1 e.2 := by
  classical
  simp [boundary]

omit [Fintype V] [Fintype T] in
private def sideEdge (p : Wire → V) (r : Wire → T) (c : V → Bool)
    (i : Wire) : (V ⊕ T) × (V ⊕ T) :=
  if c (p i) then (Sum.inl (p i),Sum.inr (r i)) else (Sum.inr (r i),Sum.inl (p i))

omit [Fintype V] [Fintype T] in
private theorem inj_sideEdge (p : Wire → V) (r : Wire → T) (c : V → Bool)
    (inj : Function.Injective (fun i=>(p i,r i))) :
    Function.Injective (sideEdge p r c) := by
  intro i j h
  apply inj
  unfold sideEdge at h
  split at h <;> split at h <;> simp_all [Prod.mk.injEq]

/-- Exact boundary count: outside, interior gadget, and port wires have
disjoint edge supports; each mismatched wire contributes one edge. -/
theorem attach_boundary (G : SimpleGraph V) (P : SimpleGraph T) (p : Wire → V)
    (r : Wire → T) (c : V → Bool) (s : T → Bool)
    (inj : Function.Injective (fun i=>(p i,r i))) :
    (boundary (attach G P p r) (Sum.elim c s)).card =
      (boundary G c).card + (boundary P s).card + ((univ : Finset Wire).filter (fun i => c (p i) ≠ s (r i))).card := by
  classical
  let i : V ↪ V ⊕ T := ⟨Sum.inl,Sum.inl_injective⟩
  let j : T ↪ V ⊕ T := ⟨Sum.inr,Sum.inr_injective⟩
  let A := (boundary G c).map (i.prodMap i)
  let B := (boundary P s).map (j.prodMap j)
  let X := (univ.filter (fun a : Wire => c (p a) ≠ s (r a))).image (sideEdge p r c)
  have XA (u v : V) : (Sum.inl u,Sum.inl v) ∉ X := by
    intro h
    obtain ⟨a,_,eq⟩ := mem_image.mp h
    unfold sideEdge at eq
    split at eq <;> simp at eq
  have XB (u v : T) : (Sum.inr u,Sum.inr v) ∉ X := by
    intro h
    obtain ⟨a,_,eq⟩ := mem_image.mp h
    unfold sideEdge at eq
    split at eq <;> simp at eq
  have split :
      boundary (attach G P p r) (Sum.elim c s) = (A ∪ B) ∪ X := by
    ext ⟨u,v⟩
    rw [in_boundary,mem_union,mem_union]
    cases u with
    | inl u => cases v with
      | inl v =>
        simp [A,B, i,j, mem_map, Function.Embedding.prodMap, XA,in_boundary,attach,adjacency]
      | inr v =>
        have left : (c u = true ∧ s v = false ∧ ∃ i, p i = u ∧ r i = v) ↔
            (Sum.inl u,Sum.inr v) ∈ X := by
          constructor
          · rintro ⟨ht,hf,a,rfl,rfl⟩
            exact mem_image.mpr ⟨a,mem_filter.mpr ⟨mem_univ _,by simp [ht,hf]⟩,by simp [sideEdge,ht]⟩
          · intro h
            obtain ⟨a,hi,eq⟩ := mem_image.mp h
            have ne := (mem_filter.mp hi).2
            unfold sideEdge at eq
            split at eq
            · rename_i ht
              obtain ⟨rfl,rfl⟩ := Prod.mk.inj (by simpa using eq)
              exact ⟨ht,by cases hs : s (r a) <;> simp_all, a,rfl,rfl⟩
            · simp at eq
        simpa [A,B, i,j, mem_map, Function.Embedding.prodMap,attach,adjacency] using left
    | inr u => cases v with
      | inl v =>
        have left : (s u = true ∧ c v = false ∧ ∃ i, p i = v ∧ r i = u) ↔
            (Sum.inr u,Sum.inl v) ∈ X := by
          constructor
          · rintro ⟨ht,hf,a,rfl,rfl⟩
            exact mem_image.mpr ⟨a,mem_filter.mpr ⟨mem_univ _,by simp [ht,hf]⟩,by simp [sideEdge,hf]⟩
          · intro h
            obtain ⟨a,hi,eq⟩ := mem_image.mp h
            have ne := (mem_filter.mp hi).2
            unfold sideEdge at eq
            split at eq
            · simp at eq
            · rename_i ht
              obtain ⟨rfl,rfl⟩ := Prod.mk.inj (by simpa using eq)
              exact ⟨by cases hs : s (r a) <;> simp_all, by simpa using ht,a,rfl,rfl⟩
        simpa [A,B, i,j, mem_map, Function.Embedding.prodMap,attach,adjacency] using left
      | inr v =>
        simp [A,B, i,j, mem_map, Function.Embedding.prodMap, XB, in_boundary,attach,adjacency]
  have disj1 : Disjoint A B := by
    rw [disjoint_left]
    intro e ha hb
    obtain ⟨⟨u,v⟩,_,rfl⟩ := mem_map.mp ha
    simp [B, i,j, mem_map, Function.Embedding.prodMap] at hb
  have disj2 : Disjoint (A ∪ B) X := by
    rw [disjoint_left]
    intro e h hx
    rcases mem_union.mp h with a|b
    · obtain ⟨⟨u,v⟩,_,rfl⟩ := mem_map.mp a
      exact XA _ _ hx
    · obtain ⟨⟨u,v⟩,_,rfl⟩ := mem_map.mp b
      exact XB _ _ hx
  rw [split, card_union_of_disjoint disj2, card_union_of_disjoint disj1]
  simp [A,B,X,card_image_of_injective _ (inj_sideEdge p r c inj)]



omit [Fintype V] [Fintype T] in
private def leftNeighborMap (G : SimpleGraph V) (P : SimpleGraph T) (p : Wire → V)
    (r : Wire → T) (x : V) :
    G.neighborSet x ⊕ {i : Wire // p i = x} →
      (attach G P p r).neighborSet (Sum.inl x)
  | .inl v => ⟨Sum.inl v.val,v.property⟩
  | .inr i => ⟨Sum.inr (r i.val),⟨i.val,i.property,rfl⟩⟩

omit [Fintype V] [Fintype T] in
private theorem leftNeighbor_bij (G : SimpleGraph V) (P : SimpleGraph T) (p : Wire → V)
    (r : Wire → T) (x : V) (inj : Function.Injective (fun i=>(p i,r i))) :
    Function.Bijective (leftNeighborMap G P p r x) := by
  constructor
  · intro a b eq
    have h := congrArg Subtype.val eq
    cases a with
    | inl u => cases b with
      | inl v =>
        exact congrArg Sum.inl (Subtype.ext (Sum.inl_injective h))
      | inr i => simp [leftNeighborMap] at h
    | inr i => cases b with
      | inl v => simp [leftNeighborMap] at h
      | inr j =>
        exact congrArg Sum.inr (Subtype.ext (inj (Prod.ext (i.property.trans j.property.symm) (Sum.inr_injective h))))
  · rintro ⟨a,h⟩
    cases a with
    | inl u => exact ⟨Sum.inl ⟨u,h⟩,rfl⟩
    | inr t =>
      obtain ⟨i,pv,rt⟩ : ∃ i, p i = x ∧ r i = t := h
      refine ⟨Sum.inr ⟨i,pv⟩,Subtype.ext ?_⟩
      exact congrArg Sum.inr rt

omit [Fintype V] [Fintype T] in
private def rightNeighborMap (G : SimpleGraph V) (P : SimpleGraph T) (p : Wire → V)
    (r : Wire → T) (x : T) :
    {i : Wire // r i = x} ⊕ P.neighborSet x →
      (attach G P p r).neighborSet (Sum.inr x)
  | .inl i => ⟨Sum.inl (p i.val),⟨i.val,rfl,i.property⟩⟩
  | .inr v => ⟨Sum.inr v.val,v.property⟩

omit [Fintype V] [Fintype T] in
private theorem rightNeighbor_bij (G : SimpleGraph V) (P : SimpleGraph T) (p : Wire → V)
    (r : Wire → T) (x : T) (inj : Function.Injective (fun i=>(p i,r i))) :
    Function.Bijective (rightNeighborMap G P p r x) := by
  constructor
  · intro a b eq
    have h := congrArg Subtype.val eq
    cases a with
    | inl u => cases b with
      | inl v => exact congrArg Sum.inl (Subtype.ext (inj (Prod.ext (Sum.inl_injective h) (u.property.trans v.property.symm))))
      | inr i => simp [rightNeighborMap] at h
    | inr i => cases b with
      | inl v => simp [rightNeighborMap] at h
      | inr j => exact congrArg Sum.inr (Subtype.ext (Sum.inr_injective h))
  · rintro ⟨a,h⟩
    cases a with
    | inl u =>
      obtain ⟨i,pv,rt⟩ : ∃ i, p i = u ∧ r i = x := h
      refine ⟨Sum.inl ⟨i,rt⟩,Subtype.ext ?_⟩
      exact congrArg Sum.inl pv
    | inr t => exact ⟨Sum.inr ⟨t,h⟩,rfl⟩

/-- An exterior vertex retains one edge per incident port independent
of the chosen gadget. -/
theorem attach_degree_outside [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : SimpleGraph T) (p : Wire → V) (r : Wire → T)
    [DecidableRel (attach G P p r).Adj] (x : V)
    (inj : Function.Injective (fun i=>(p i,r i))) :
    (attach G P p r).degree (Sum.inl x) =
      G.degree x + ((univ : Finset Wire).filter (fun i => p i = x)).card := by
  classical
  rw [←SimpleGraph.card_neighborSet_eq_degree]
  rw [←Fintype.card_congr (Equiv.ofBijective _ (leftNeighbor_bij G P p r x inj))]
  rw [Fintype.card_sum,SimpleGraph.card_neighborSet_eq_degree,Fintype.card_subtype]

/-- An interior vertex receives exactly one distinct neighbor for each
port assigned to it. -/
theorem attach_degree_inside [DecidableEq T] (G : SimpleGraph V) (P : SimpleGraph T) [DecidableRel P.Adj]
    (p : Wire → V) (r : Wire → T) [DecidableRel (attach G P p r).Adj] (x : T)
    (inj : Function.Injective (fun i=>(p i,r i))) :
    (attach G P p r).degree (Sum.inr x) =
      ((univ : Finset Wire).filter (fun i => r i = x)).card + P.degree x := by
  classical
  rw [←SimpleGraph.card_neighborSet_eq_degree]
  rw [←Fintype.card_congr (Equiv.ofBijective _ (rightNeighbor_bij G P p r x inj))]
  rw [Fintype.card_sum,SimpleGraph.card_neighborSet_eq_degree,Fintype.card_subtype]

def root9 (i : Wire) : Fin 9 := (#[2,4,6,5,7,8,8] : Array (Fin 9))[i.val]?.getD 8
def root3 (i : Wire) : Fin 3 := (#[1,0,0,1,2,2,2] : Array (Fin 3))[i.val]?.getD 2

private theorem wires9_eq : oldWires=(List.finRange 7).map (fun i=>(i,root9 i)) := by decide
private theorem wires3_eq : newWires=(List.finRange 7).map (fun i=>(i,root3 i)) := by decide

def ProperWires (p : Wire→V) : Prop :=
  (∀ i j : Wire,i.val<4→j.val<4→p i=p j→i=j) ∧
    p 4≠p 5 ∧ p 4≠p 6 ∧ p 5≠p 6

omit [Fintype V] in
private theorem unique9 {p : Wire→V} (h : ProperWires p) :
    Function.Injective (fun i=>(p i,root9 i)) := by
  intro a b hh
  have hp := congrArg Prod.fst hh
  have same := congrArg Prod.snd hh
  have cs : ∀ i j : Wire,root9 i=root9 j→i=j∨(i=5∧j=6)∨(i=6∧j=5) := by decide
  rcases cs a b same with eq|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact eq
  · exact (h.2.2.2 hp).elim
  · exact (h.2.2.2 hp.symm).elim

omit [Fintype V] in
theorem unique3 {p : Wire→V} (h : ProperWires p) :
    Function.Injective (fun i=>(p i,root3 i)) := by
  intro a b hh
  have hp := congrArg Prod.fst hh
  have same := congrArg Prod.snd hh
  have cs : ∀ i j : Wire,root3 i=root3 j→i=j∨(i.val<4∧j.val<4)∨
      (i=4∧j=5)∨(i=5∧j=4)∨(i=4∧j=6)∨(i=6∧j=4)∨(i=5∧j=6)∨(i=6∧j=5) := by decide
  rcases cs a b same with eq|⟨x,y⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact eq
  · exact h.1 _ _ x y hp
  · exact (h.2.1 hp).elim
  · exact (h.2.1 hp.symm).elim
  · exact (h.2.2.1 hp).elim
  · exact (h.2.2.1 hp.symm).elim
  · exact (h.2.2.2 hp).elim
  · exact (h.2.2.2 hp.symm).elim

omit [Fintype V] [Fintype T] in
private theorem glue_eq_attach (B : SimpleGraph V) (K : SimpleGraph T)
    (p : Wire→V) (r : Wire→T) :
    glue B K p ((List.finRange 7).map (fun i=>(i,r i))) = attach B K p r := by
  have fibers (i : Wire) (x : T) :
      (i,x)∈(List.finRange 7).map (fun a=>(a,r a)) ↔ r i=x := by
    simp [Prod.mk.injEq]
  ext a b
  cases a <;> cases b <;> simp [attach,adjacency,glue,linkAdj,link,fibers]

omit [Fintype V] in
theorem original_exact (B : SimpleGraph V) (p : Wire→V) :
    ambient B p=attach B core9 p root9 := by
  unfold ambient
  rw [wires9_eq,glue_eq_attach]

omit [Fintype V] in
theorem candidate_exact (B : SimpleGraph V) (p : Wire→V) :
    candidate B p=attach B core3 p root3 := by
  unfold candidate
  rw [wires3_eq,glue_eq_attach]

theorem candidate_cubic [DecidableEq V] (B : SimpleGraph V) [DecidableRel B.Adj] (p : Wire→V)
    (proper : ProperWires p) (cu : ∀ x,(ambient B p).degree x=3) :
    ∀ x,(candidate B p).degree x=3 := by
  have same {K H : SimpleGraph (V⊕Fin 9)} [DecidableRel K.Adj] [DecidableRel H.Adj]
      (e : K=H) (x : V⊕Fin 9) : K.degree x=H.degree x := by
    subst H
    let f (F : Fintype ↑(K.neighborSet x)) := @SimpleGraph.degree (V⊕Fin 9) K x F
    exact congrArg f (Subsingleton.elim _ _)
  have same3 {K H : SimpleGraph (V⊕Fin 3)} [DecidableRel K.Adj] [DecidableRel H.Adj]
      (e : K=H) (x : V⊕Fin 3) : K.degree x=H.degree x := by
    subst H
    let f (F : Fintype ↑(K.neighborSet x)) := @SimpleGraph.degree (V⊕Fin 3) K x F
    exact congrArg f (Subsingleton.elim _ _)
  intro x
  rw [same3 (candidate_exact B p)]
  cases x with
  | inl x =>
    rw [attach_degree_outside B _ p _ _ (unique3 proper),
      ←attach_degree_outside B core9 p root9 x (unique9 proper),
      ←same (original_exact B p)]
    exact cu _
  | inr x =>
    rw [attach_degree_inside B _ p _ _ (unique3 proper)]
    exact (by decide : ∀ i : Fin 3,
      ((univ : Finset Wire).filter (fun a=>root3 a=i)).card+core3.degree i=3) x

private def orient {W : Type*} (c : W→Bool) (a b : W) : W×W := if c a then (a,b) else (b,a)

private theorem listed_boundary {W : Type*} [Fintype W] [LinearOrder W]
    (G : SimpleGraph W) (E : List (W×W))
    (adj : ∀ x y,G.Adj x y ↔ (x,y)∈E ∨ (y,x)∈E)
    (sorted : ∀ x y : W,(x,y)∈E→x<y) (nodup : E.Nodup) (c : W→Bool) :
    (boundary G c).card = E.countP (fun e=>c e.1 != c e.2) := by
  classical
  let S := E.toFinset.filter (fun e=>c e.1≠c e.2)
  let o (e : W×W) := orient c e.1 e.2
  have shape : boundary G c = S.image o := by
    ext ⟨u,v⟩
    have m : (u,v)∈boundary G c ↔ c u=true ∧ c v=false ∧ G.Adj u v := by
      simp [boundary]
    constructor
    · intro h
      obtain ⟨ho,hc,ed⟩ := m.mp h
      rcases (adj u v).mp ed with a|b
      · exact mem_image.mpr ⟨(u,v),mem_filter.mpr ⟨List.mem_toFinset.mpr a,by simp [ho,hc]⟩,
          by simp [o,orient,ho]⟩
      · exact mem_image.mpr ⟨(v,u),mem_filter.mpr ⟨List.mem_toFinset.mpr b,by simp [ho,hc]⟩,
          by simp [o,orient,hc]⟩
    · intro h
      obtain ⟨⟨u',v'⟩,hs,eq⟩ := mem_image.mp h
      obtain ⟨he,nd⟩ := mem_filter.mp hs
      have connected : G.Adj u' v' := (adj _ _).mpr (Or.inl (List.mem_toFinset.mp he))
      change c u' ≠ c v' at nd
      have mm (x y : W) : (x,y)∈boundary G c ↔ c x=true ∧ c y=false ∧ G.Adj x y := by
        simp [boundary]
      have useful : o (u',v') ∈ boundary G c := by
        cases eu : c u' <;> cases ev : c v'
        · exact (nd (eu.trans ev.symm)).elim
        · exact (mm v' u').mpr ⟨ev,eu,connected.symm⟩ |> fun hh => by simpa [o,orient,eu] using hh
        · exact (mm u' v').mpr ⟨eu,ev,connected⟩ |> fun hh => by simpa [o,orient,eu] using hh
        · exact (nd (eu.trans ev.symm)).elim
      exact eq ▸ useful
  have used (e : W×W) (h : e∈S) : e.1<e.2 :=
    sorted e.1 e.2 (List.mem_toFinset.mp (mem_filter.mp h).1)
  have inj : Set.InjOn o (↑S : Set (W×W)) := by
    intro a ha b hb eq
    have na : a.1<a.2 := used a ha
    have nb : b.1<b.2 := used b hb
    have cancel (h : a = b.swap) : False := by
      rw [h] at na
      exact (not_lt_of_ge (le_of_lt nb)) na
    have ca : o a=a ∨ o a=a.swap := by
      rcases a with ⟨x,y⟩
      cases z : c x <;> simp [o,orient,z]
    have cb : o b=b ∨ o b=b.swap := by
      rcases b with ⟨x,y⟩
      cases z : c x <;> simp [o,orient,z]
    rcases ca with p|p <;> rcases cb with q|q <;> rw [p,q] at eq
    · exact eq
    · exact (cancel eq).elim
    · exact (cancel (by simpa only [Prod.swap_swap] using congrArg Prod.swap eq)).elim
    · simpa only [Prod.swap_swap] using congrArg Prod.swap eq
  rw [shape,card_image_of_injOn inj,List.countP_eq_length_filter]
  have same : S = (E.filter (fun e=>c e.1 != c e.2)).toFinset := by
    ext z
    simp [S,and_comm]
  rw [same]
  exact List.toFinset_card_of_nodup (nodup.filter _)



private theorem mismatch_eq {I : Type*} (r : Wire→I) (c : Wire→Bool) (s : I→Bool) :
    ((univ : Finset Wire).filter (fun i=>c i≠s (r i))).card =
    ((List.finRange 7).map (fun i=>(i,r i))).countP (fun e=>c e.1 != s e.2) := by
  classical
  let Z := (List.finRange 7).filter (fun i=>c i != s (r i))
  have f : ((univ : Finset Wire).filter (fun i=>c i≠s (r i)))=Z.toFinset := by
    ext i
    simp [Z]
  rw [f,List.toFinset_card_of_nodup ((List.nodup_finRange 7).filter _)]
  rw [List.countP_map,List.countP_eq_length_filter]
  rfl

theorem ambient_boundary (B : SimpleGraph V) (p : Wire→V) (h : ProperWires p)
    (c : V→Bool) (s : Fin 9→Bool) :
    (boundary (ambient B p) (Sum.elim c s)).card =
      (boundary B c).card+cost edges9 oldWires (fun i=>c (p i)) s := by
  rw [original_exact,attach_boundary B core9 p root9 c s (unique9 h),
    listed_boundary core9 edges9 (fun _ _=>Iff.rfl) (by decide) (by decide)]
  rw [mismatch_eq root9 (fun i=>c (p i)) s,←wires9_eq]
  simp [cost,Nat.add_assoc]

theorem candidate_boundary (B : SimpleGraph V) (p : Wire→V) (h : ProperWires p)
    (c : V→Bool) (s : Fin 3→Bool) :
    (boundary (candidate B p) (Sum.elim c s)).card =
      (boundary B c).card+cost edges3 newWires (fun i=>c (p i)) s := by
  rw [candidate_exact,attach_boundary B core3 p root3 c s (unique3 h),
    listed_boundary core3 edges3 (fun _ _=>Iff.rfl) (by decide) (by decide)]
  rw [mismatch_eq root3 (fun i=>c (p i)) s,←wires3_eq]
  simp [cost,Nat.add_assoc]

#print axioms attach_boundary
#print axioms ambient_boundary
#print axioms candidate_boundary
#print axioms candidate_cubic
end
end KelmansCactus.AtomicBridge.ThetaAsymmetricFaithfulGeometry
