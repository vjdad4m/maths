import PentagonCap
import PentagonTransfer

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaModes
open SquareCap (FactorOn HasFactor SmallTrivial ThreeConnected three_connected_of_small_trivial)
open PentagonCap (pathCap path3 pathRoot)
open PentagonProfile (Port)
open PentagonTransfer (stubGraph stub)
noncomputable section

universe u

/-- Exact centered-neighbor version of the published cyclic z5 input. -/
def CyclicZ5Promise : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    (∀ x,G.degree x=3) → ThreeConnected G → SmallTrivial G →
    6 ∣ Fintype.card W →
    ∀ {r a : W}, G.Adj r a → ∃ w,a≠w ∧ G.Adj r a ∧ G.Adj r w ∧
      FactorOn G (univ \ {r,a,w})

private theorem pullback {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    {G : SimpleGraph X} {H : SimpleGraph Y} {S : Finset X} (f : X↪Y)
    (keep : ∀ a∈S,∀ b∈S,H.Adj (f a) (f b) → G.Adj a b)
    (h : FactorOn H (S.map f)) : FactorOn G S := by
  classical
  obtain ⟨P,tp,sep,cover⟩ := h
  let pre (t : Finset Y) := S.filter (fun v=>f v∈t)
  have pm {t : Finset Y} {v : X} : v∈pre t ↔ v∈S ∧ f v∈t := by simp [pre]
  have sub {t : Finset Y} (ht : t∈P) : t ⊆ S.map f := fun _ tV =>
    cover ▸ mem_biUnion.mpr ⟨t,ht,tV⟩
  have eq {t : Finset Y} (ht : t∈P) : (pre t).map f = t := by
    ext y
    constructor
    · rintro hy
      obtain ⟨x,hx,rfl⟩ := mem_map.mp hy
      exact (pm.mp hx).2
    · intro hy
      obtain ⟨x,xs,rfl⟩ := mem_map.mp (sub ht hy)
      exact mem_map.mpr ⟨x,pm.mpr ⟨xs,hy⟩,rfl⟩
  refine ⟨P.image pre,?_,?_,?_⟩
  · intro A ha
    obtain ⟨t,ht,rfl⟩ := mem_image.mp ha
    obtain ⟨n,c,hc,star⟩ := tp t ht
    obtain ⟨x,xs,rfl⟩ := mem_map.mp (sub ht hc)
    have cN : (pre t).card=3 := by rw [←card_map f,eq ht,n]
    refine ⟨cN,x,pm.mpr ⟨xs,hc⟩,?_⟩
    intro w wt wx
    obtain ⟨ws,wt'⟩ := pm.mp wt
    exact keep x xs w ws (star (f w) wt' (fun e=>wx (f.injective e)))
  · intro A ha B hb ne
    obtain ⟨t,ht,rfl⟩ := mem_image.mp ha
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hb
    have left : t≠u := fun e=>ne (congrArg pre e)
    exact disjoint_left.mpr (fun _ xt xu=>disjoint_left.mp (sep t ht u hu left)
      (pm.mp xt).2 (pm.mp xu).2)
  · ext v
    constructor
    · intro h
      obtain ⟨x,hx,hy⟩ := mem_biUnion.mp h
      obtain ⟨t,_,rfl⟩ := mem_image.mp hx
      exact (pm.mp hy).1
    · intro h
      have vm : f v ∈ P.biUnion id := cover.symm ▸ mem_map.mpr ⟨v,h,rfl⟩
      obtain ⟨t,ht,hv⟩ := mem_biUnion.mp vm
      exact mem_biUnion.mpr ⟨pre t,mem_image.mpr ⟨t,ht,rfl⟩,pm.mpr ⟨h,hv⟩⟩

variable {V : Type u} [Fintype V] [DecidableEq V]

private def pushStub : (V⊕Unit)↪(V⊕Fin 3) where
  toFun := Sum.elim Sum.inl (fun _=>Sum.inr 2)
  inj' := by
    intro x y e
    cases x with
    | inl u => cases y with
      | inl v => exact congrArg Sum.inl (Sum.inl_injective e)
      | inr v => exact Sum.noConfusion (show Sum.inl u = Sum.inr (2:Fin 3) from e)
    | inr u => cases y with
      | inl v => exact Sum.noConfusion (show Sum.inr (2:Fin 3) = Sum.inl v from e)
      | inr v => cases u; cases v; rfl

private theorem pathPorts0 : ∀ i : Port,pathRoot i=1 ↔ i=0 := by decide
private theorem pathPorts2 : ∀ i : Port,pathRoot i=2 ↔ i=1∨i=4 := by decide
private theorem pathCenter : ∀ i : Fin 3,path3.Adj 1 i → i=0∨i=2 := by decide
private theorem allThree : ∀ i : Fin 3, i=0∨i=1∨i=2 := by decide

private theorem retain_only_stub (p : Port↪V) :
    ((univ : Finset (V⊕Unit)).erase (Sum.inl (p 0))).map pushStub =
      (univ : Finset (V⊕Fin 3)) \ {Sum.inr 1,Sum.inr 0,Sum.inl (p 0)} := by
  ext v
  cases v with
  | inl u => simp [pushStub,mem_map]
  | inr i =>
    rcases allThree i with rfl|rfl|rfl <;> simp [pushStub,mem_map]

private theorem retain_outside :
    (univ : Finset V).map ⟨Sum.inl,Sum.inl_injective⟩ =
      (univ : Finset (V⊕Fin 3)) \ {Sum.inr 1,Sum.inr 0,Sum.inr 2} := by
  ext v
  cases v with
  | inl w => simp [mem_map]
  | inr i =>
    rcases allThree i with rfl|rfl|rfl <;> simp [mem_map]

omit [Fintype V] [DecidableEq V] in
private theorem stub_preserved {G : SimpleGraph V} {p : Port↪V}
    (x y : V⊕Unit) :
    (pathCap G p).Adj (pushStub x) (pushStub y) → (stubGraph G (p 1) (p 4)).Adj x y := by
  intro e
  cases x with
  | inl x => cases y with
    | inl y => exact e
    | inr y =>
      obtain ⟨i,xi,loc⟩ : ∃ i,p i=x ∧ pathRoot i=2 := e
      rcases (pathPorts2 i).mp loc with rfl|rfl
      · exact Or.inl xi.symm
      · exact Or.inr xi.symm
  | inr x => cases y with
    | inl y =>
      obtain ⟨i,xi,loc⟩ : ∃ i,p i=y ∧ pathRoot i=2 := e
      rcases (pathPorts2 i).mp loc with rfl|rfl
      · exact Or.inl xi.symm
      · exact Or.inr xi.symm
    | inr y => exact path3.loopless 2 e

/-- Prescribing the discarded leaf at the cap midpoint leaves exactly
the two modes required by the theta transfer theorem. -/
theorem theta_modes_of_cyclic_z5 (z5 : CyclicZ5Promise.{u})
    {G : SimpleGraph V} {p : Port↪V} [DecidableRel (pathCap G p).Adj]
    (cub : ∀ x,(pathCap G p).degree x=3)
    (small : SmallTrivial (pathCap G p))
    (order : Fintype.card (V⊕Fin 7)%6=4) :
    HasFactor G ∨ FactorOn (stubGraph G (p 1) (p 4))
      (univ.erase (Sum.inl (p 0))) := by
  classical
  let H := pathCap G p
  have f5 : 5≤Fintype.card V := by
    have u := Fintype.card_le_of_injective p p.injective
    simpa using u
  have nc : Fintype.card (V⊕Fin 3)=Fintype.card V+3 := by simp
  have conn := three_connected_of_small_trivial H cub (by omega) small
  have dvd : 6 ∣ Fintype.card (V⊕Fin 3) := by
    rw [Fintype.card_sum,Fintype.card_fin] at order
    omega
  have edge : H.Adj (Sum.inr 1) (Sum.inr 0) := by
    change path3.Adj (1:Fin 3) 0
    decide
  obtain ⟨w,notFirst,_,toW,parts⟩ := z5 (V⊕Fin 3) H cub conn small dvd edge
  cases w with
  | inl v =>
    have eq : v=p 0 := by
      obtain ⟨i,pn,ip⟩ : ∃ i,p i=v ∧ pathRoot i=1 := toW
      exact ((pathPorts0 i).mp ip ▸ pn).symm
    subst v
    right
    rw [←retain_only_stub p] at parts
    exact pullback pushStub (fun x _ y _ e=>stub_preserved x y e) parts
  | inr i =>
    have h : path3.Adj 1 i := toW
    rcases pathCenter i h with rfl|rfl
    · exact (notFirst rfl).elim
    · left
      rw [←retain_outside] at parts
      exact pullback ⟨Sum.inl,Sum.inl_injective⟩ (fun _ _ _ _ a => a) parts

#print axioms theta_modes_of_cyclic_z5

end
end KelmansCactus.AtomicBridge.ThetaModes
