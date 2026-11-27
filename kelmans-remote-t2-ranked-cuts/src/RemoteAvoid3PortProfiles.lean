import RemoteT2CompletionTransfer
import RemoteT2ForcedChain
import RemoteT2AvoidThree

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteAvoid3PortProfiles
open SquareCap (FactorOn HasFactor Port cap coord SmallTrivial)
open RemoteT2CompletionTransfer (marked eraseEdge SmallerIsolatedAvoid3)
open RemoteT2ForcedChain (factor_iff_strip_leaf_chain)
open RemoteT2AvoidThree (factor_image_injOn)

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def SingleReady (G : SimpleGraph V) (q : V) : Prop :=
  FactorOn G (univ.erase q)

def PairReady (G : SimpleGraph V) (q : V) : Prop :=
  ∃ w : V,G.Adj q w ∧ FactorOn G ((univ.erase q).erase w)

theorem four_ports (k : Bool) (i : Port) :
    ∃ j t r : Port,j≠i ∧ t≠i ∧ r≠i ∧ j≠t ∧ j≠r ∧ t≠r ∧
      (∀ p : Port, coord k p=coord k i ↔ p=i∨p=j) ∧
      (∀ p : Port, coord k p= !(coord k i) ↔ p=t∨p=r) := by
  let j : Port := if k then (i.1,!i.2) else (!i.1,i.2)
  let t : Port := if k then (!i.1,i.2) else (i.1,!i.2)
  let r : Port := (!i.1,!i.2)
  refine ⟨j,t,r,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals
    rcases i with ⟨a,b⟩
    cases k <;> cases a <;> cases b
    all_goals first
      | (intro q; rcases q with ⟨x,y⟩; cases x <;> cases y <;> decide)
      | decide

omit [Fintype V] [DecidableEq V] in
private theorem cap_one_side (G : SimpleGraph V) (p : Port↪V) (k : Bool)
    (s : Bool) (u v : Port) (h : ∀ q : Port,coord k q=s ↔ q=u∨q=v) :
    ∀ z : V,(cap G p k).Adj (Sum.inr s) (Sum.inl z) ↔ z=p u∨z=p v := by
  intro z
  change (∃ q : Port,p q=z∧coord k q=s) ↔ _
  constructor
  · rintro ⟨q,qz,hs⟩
    rcases (h q).mp hs with rfl|rfl
    · exact Or.inl qz.symm
    · exact Or.inr qz.symm
  · rintro (rfl|rfl)
    · exact ⟨u,rfl,(h u).mpr (Or.inl rfl)⟩
    · exact ⟨v,rfl,(h v).mpr (Or.inr rfl)⟩

omit [Fintype V] in
private theorem project {D : SimpleGraph (V⊕Bool)} {G : SimpleGraph V}
    {U : Finset V} (dummy : V) (S : Finset (V⊕Bool))
    (supp : ∀ z : V⊕Bool,z∈S ↔ ∃ w∈U,z=Sum.inl w)
    (keep : ∀ a∈U,∀ b∈U,D.Adj (Sum.inl a) (Sum.inl b) → G.Adj a b)
    (f : FactorOn D S) : FactorOn G U := by
  classical
  let back : V⊕Bool→V := Sum.elim id (fun _=>dummy)
  have inj : Set.InjOn back (↑S : Set (V⊕Bool)) := by
    intro a ha b hb h
    obtain ⟨w,_,rfl⟩ := (supp a).mp ha
    obtain ⟨u,_,rfl⟩ := (supp b).mp hb
    exact congrArg Sum.inl h
  have mono : ∀ a∈S,∀ b∈S,D.Adj a b→G.Adj (back a) (back b) := by
    intro a ha b hb h
    obtain ⟨w,wu,rfl⟩ := (supp a).mp ha
    obtain ⟨u,uu,rfl⟩ := (supp b).mp hb
    exact keep w wu u uu h
  have cover : S.image back=U := by
    ext z
    constructor
    · intro e
      obtain ⟨u,us,h⟩ := mem_image.mp e
      obtain ⟨w,wu,rfl⟩ := (supp u).mp us
      change w=z at h
      exact h ▸ wu
    · intro zm
      exact mem_image.mpr ⟨Sum.inl z,(supp _).mpr ⟨z,zm,rfl⟩,rfl⟩
  rw [←cover]
  exact factor_image_injOn back inj mono f

/-- An order-4-mod-6 shore is single-ready at any of its four ports:
delete three cap-to-shore wires, keeping only the marked wire. The
two cap vertices and that marked port form a forced tile. Assumes
strictly smaller isolated-pattern Avoid3, not arbitrary F2. -/
theorem single_ready_of_cap_avoid3 (G : SimpleGraph V) (p : Port↪V) (k : Bool) (i : Port)
    [DecidableRel (cap G p k).Adj]
    (n : ℕ) (less : Fintype.card (V⊕Bool)<n) (order : Fintype.card V%6=4)
    (cub : ∀ v,(cap G p k).degree v=3)
    (c4 : SmallTrivial (cap G p k))
    (smaller : SmallerIsolatedAvoid3.{u} n) :
    SingleReady G (p i) := by
  classical
  obtain ⟨j,t,r,ji,ti,ri,jt,jr,tr,bport,aport⟩ := four_ports k i
  let H := cap G p k
  let s := coord k i
  let A : V⊕Bool := Sum.inr (!s)
  let B : V⊕Bool := Sum.inr s
  let Q : V⊕Bool := Sum.inl (p i)
  let J : V⊕Bool := Sum.inl (p j)
  let T : V⊕Bool := Sum.inl (p t)
  let R : V⊕Bool := Sum.inl (p r)
  have bH : ∀ w : V,H.Adj B (Sum.inl w) ↔ w=p i∨w=p j := cap_one_side G p k s i j bport
  have aH : ∀ w : V,H.Adj A (Sum.inl w) ↔ w=p t∨w=p r := cap_one_side G p k (!s) t r aport
  have ab : A≠B := by
    intro e
    have h : (!s)=s := Sum.inr.inj e
    cases hs : s <;> simp [hs] at h
  have adjAB : H.Adj A B := by
    change (⊤ : SimpleGraph Bool).Adj (!s) s
    cases s <;> decide
  have aj : H.Adj B J := (bH _).mpr (Or.inr rfl)
  have at' : H.Adj A T := (aH _).mpr (Or.inl rfl)
  have ar : H.Adj A R := (aH _).mpr (Or.inr rfl)
  have card : Fintype.card (V⊕Bool)=Fintype.card V+2 := by simp
  have vcc := SquareCap.three_connected_of_small_trivial H cub (by omega) c4
  have rem : Fintype.card (V⊕Bool)%6=0 := by omega
  let D := eraseEdge (eraseEdge (eraseEdge H B J) A T) A R
  have fs : HasFactor D := smaller (V⊕Bool) H less cub vcc c4 rem B J A T A R aj at' ar
    ab.symm Sum.noConfusion Sum.noConfusion (fun h=>jt (p.injective (Sum.inl.inj h)))
    ab.symm Sum.noConfusion Sum.noConfusion (fun h=>jr (p.injective (Sum.inl.inj h)))
    (fun h=>h.elim (fun h=>tr (p.injective (Sum.inl.inj h.2)).symm) (fun h=>Sum.noConfusion h.1))
  have da : D.Adj A B := by
    exact ⟨⟨⟨adjAB,fun h=>h.elim (fun h=>ab h.1) (fun h=>Sum.noConfusion h.1)⟩,
      fun h=>h.elim (fun h=>Sum.noConfusion h.2) (fun h=>Sum.noConfusion h.1)⟩,
      fun h=>h.elim (fun h=>Sum.noConfusion h.2) (fun h=>Sum.noConfusion h.1)⟩
  have db : D.Adj B Q := by
    exact ⟨⟨⟨(bH _).mpr (Or.inl rfl),fun h=>h.elim (fun h=>ji (p.injective (Sum.inl.inj h.2)).symm)
      (fun h=>Sum.noConfusion h.1)⟩,
      fun h=>h.elim (fun h=>ab h.1.symm) (fun h=>Sum.noConfusion h.1)⟩,
      fun h=>h.elim (fun h=>ab h.1.symm) (fun h=>Sum.noConfusion h.1)⟩
  have pole (z : Bool) : (Sum.inr z : V⊕Bool)=A∨(Sum.inr z : V⊕Bool)=B := by
    cases hs : s <;> cases z <;> simp [A,B,hs]
  have pa : ∀ z∈(univ : Finset (V⊕Bool)),D.Adj A z→z=B := by
    rintro (z|z) _ h
    · rcases (aH z).mp h.1.1.1 with rfl|rfl
      · exact (h.1.2 (Or.inl ⟨rfl,rfl⟩)).elim
      · exact (h.2 (Or.inl ⟨rfl,rfl⟩)).elim
    · exact (pole z).elim (fun e=>(D.loopless _ (e ▸ h)).elim) id
  have pb : ∀ z∈(univ : Finset (V⊕Bool)),D.Adj B z→z=A∨z=Q := by
    rintro (z|z) _ h
    · rcases (bH z).mp h.1.1.1 with rfl|rfl
      · exact Or.inr rfl
      · exact (h.1.1.2 (Or.inl ⟨rfl,rfl⟩)).elim
    · exact (pole z).elim Or.inl (fun e=>(D.loopless _ (e ▸ h)).elim)
  let S : Finset (V⊕Bool) := univ \ {A,B,Q}
  have ff : FactorOn D S := (factor_iff_strip_leaf_chain (mem_univ _) (mem_univ _)
    (mem_univ _) Sum.noConfusion da db pa pb).mp fs
  have shape (z : V⊕Bool) : z∈S ↔ ∃ w∈(univ.erase (p i) : Finset V),z=Sum.inl w := by
    cases z with
    | inl z => simp [S,A,B,Q]
    | inr z =>
      rcases pole z with eq|eq <;> simp [S,eq,Q,ab,ab.symm]
  exact project (D:=D) (G:=G) (p i) S shape (fun _ _ _ _ ed=>ed.1.1.1) ff

omit [Fintype V] in
private theorem factor_remove_tile {D : SimpleGraph (V⊕Bool)} {S U : Finset (V⊕Bool)}
    {P : Finset (Finset (V⊕Bool))} (tiles : ∀ A∈P,SquareCap.IsTile D A)
    (apart : ∀ A∈P,∀ B∈P,A≠B→ Disjoint A B)
    (cv : P.biUnion id=S) (m : U∈P) : FactorOn D (S\U) := by
  classical
  refine ⟨P.erase U,fun _ a=>tiles _ (mem_erase.mp a).2,
    fun _ a _ b ne=>apart _ (mem_erase.mp a).2 _ (mem_erase.mp b).2 ne,?_⟩
  ext z
  constructor
  · intro q
    obtain ⟨A,a,h⟩ := mem_biUnion.mp q
    obtain ⟨ne,ap⟩ := mem_erase.mp a
    exact mem_sdiff.mpr ⟨cv ▸ mem_biUnion.mpr ⟨A,ap,h⟩,
      fun x=>disjoint_left.mp (apart _ ap _ m ne) h x⟩
  · intro q
    obtain ⟨zS,nu⟩ := mem_sdiff.mp q
    obtain ⟨A,a,ha⟩ := mem_biUnion.mp (cv.symm ▸ zS)
    exact mem_biUnion.mpr ⟨A,mem_erase.mpr ⟨fun eq=>nu (eq ▸ ha),a⟩,ha⟩

/-- Exact extraction for the remaining residue: in the cap, delete
the pole opposite the marked port and forbid the other wire at the
marked port's own pole. This makes the latter a leaf. Its tile consumes
the marked port and a genuine neighbor of that port inside the shore. -/
theorem pair_ready_of_cap_root_avoid (G : SimpleGraph V) (p : Port↪V) (k : Bool) (i j : Port)
    (_mate : j≠i) (bport : ∀ q : Port, coord k q=coord k i ↔ q=i∨q=j)
    (f : FactorOn (eraseEdge (cap G p k) (Sum.inr (coord k i)) (Sum.inl (p j)))
      (univ.erase (Sum.inr (!(coord k i))))) :
    PairReady G (p i) := by
  classical
  let s := coord k i
  let A : V⊕Bool := Sum.inr (!s)
  let B : V⊕Bool := Sum.inr s
  let Q : V⊕Bool := Sum.inl (p i)
  let J : V⊕Bool := Sum.inl (p j)
  let D := eraseEdge (cap G p k) B J
  let S : Finset (V⊕Bool) := univ.erase A
  have ab : A≠B := by
    intro e
    have h : (!s)=s := Sum.inr.inj e
    cases hs : s <;> simp [hs] at h
  have pole (z : Bool) : (Sum.inr z : V⊕Bool)=A∨(Sum.inr z : V⊕Bool)=B := by
    cases hs : s <;> cases z <;> simp [A,B,hs]
  have mt : B∈S := by simp [S,ab.symm]
  have bH := cap_one_side G p k s i j bport
  have leaves : ∀ z∈S,D.Adj B z→z=Q := by
    rintro (z|z) hz ed
    · rcases (bH z).mp ed.1 with rfl|rfl
      · rfl
      · exact (ed.2 (Or.inl ⟨rfl,rfl⟩)).elim
    · rcases pole z with eq|eq
      · simp [S,eq] at hz
      · exact (D.loopless _ (eq ▸ ed)).elim
  change FactorOn D S at f
  obtain ⟨P,tiles,apart,cover⟩ := f
  have Ts : ∀ T∈P,T⊆S := fun _ m _ h=>cover ▸ mem_biUnion.mpr ⟨_,m,h⟩
  obtain ⟨T,tm,bm⟩ := mem_biUnion.mp (cover.symm ▸ mt)
  obtain ⟨nT,c,cm,cent⟩ := tiles T tm
  have cb : c≠B := by
    intro e
    subst c
    have pair : T⊆{B,Q} := by
      intro z zt
      by_cases eq : z=B
      · simp [eq]
      · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (leaves _ (Ts T tm zt) (cent _ zt eq))))
    have le := (card_le_card pair).trans card_le_two
    omega
  have cq : c=Q := leaves c (Ts T tm cm) (cent B bm cb.symm).symm
  subst c
  have haveThird : ∃ z∈T,z≠Q∧z≠B := by
    by_contra no
    have pair : T⊆{Q,B} := by
      intro z zt
      rw [mem_insert,mem_singleton]
      by_cases hz : z=Q
      · exact Or.inl hz
      · apply Or.inr
        by_contra ne
        exact no ⟨z,zt,hz,ne⟩
    have le := (card_le_card pair).trans card_le_two
    omega
  obtain ⟨z,zt,zq,zb⟩ := haveThird
  have outside : ∃ v : V,z=Sum.inl v := by
    cases z with
    | inl z => exact ⟨z,rfl⟩
    | inr z =>
      rcases pole z with h|h
      · exact False.elim ((mem_erase.mp (Ts T tm zt)).1 h)
      · exact False.elim (zb h)
  obtain ⟨w,rfl⟩ := outside
  have adj : G.Adj (p i) w := (cent (Sum.inl w) zt zq).1
  have we : w≠p i := fun h=>zq (congrArg Sum.inl h)
  have exactT : T={B,Q,Sum.inl w} := by
    symm
    apply eq_of_subset_of_card_le
    · intro u hu
      simp only [mem_insert,mem_singleton] at hu
      rcases hu with rfl|rfl|rfl <;> assumption
    · simp [Q,B,we.symm,nT]
  have rest := factor_remove_tile tiles apart cover tm
  rw [exactT] at rest
  have shape (z : V⊕Bool) : z∈S\{B,Q,Sum.inl w} ↔
      ∃ v∈((univ.erase (p i)).erase w : Finset V),z=Sum.inl v := by
    cases z with
    | inl z => simp [S,A,B,Q,and_comm]
    | inr z => rcases pole z with h|h <;> simp [S,h,A,B,Q,ab,ab.symm]
  exact ⟨w,adj,project (D:=D) (G:=G) (p i) _ shape (fun _ _ _ _ ed=>ed.1) rest⟩

#print axioms single_ready_of_cap_avoid3
#print axioms pair_ready_of_cap_root_avoid
end KelmansCactus.AtomicBridge.RemoteAvoid3PortProfiles
