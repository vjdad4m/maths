import PentagonCap
import SquareCapFactor

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.EarDecode
open SquareCap (FactorOn IsTile omitEdge)
open PentagonCap (pathCap pathRoot path3)
open PentagonProfile (Port)
noncomputable section

universe u
private theorem factor_erase_one {T : Type*} [DecidableEq T] {F : Finset T}
    {G : SimpleGraph T} (f : FactorOn G F) {x : T} (xF : x ∈ F) :
    ∃ S, S ⊆ F ∧ x ∈ S ∧ IsTile G S ∧ FactorOn G (F \ S) := by
  obtain ⟨P,p,d,u⟩ := f
  have m : x ∈ P.biUnion id := u ▸ xF
  obtain ⟨s,hs,xs⟩ := mem_biUnion.mp m
  have sub : s ⊆ F := fun a h => u ▸ mem_biUnion.mpr ⟨s,hs,h⟩
  refine ⟨s,sub,xs,p s hs,P.erase s,?_,?_,?_⟩
  · intro t ht
    exact p t (mem_erase.mp ht).2
  · intro a ha b hb
    exact d a (mem_erase.mp ha).2 b (mem_erase.mp hb).2
  · ext v
    constructor
    · intro hv
      obtain ⟨t,ht,vt⟩ := mem_biUnion.mp hv
      refine mem_sdiff.mpr ⟨u ▸ mem_biUnion.mpr ⟨t,(mem_erase.mp ht).2,vt⟩,?_⟩
      exact fun vs => disjoint_left.mp (d t (mem_erase.mp ht).2 s hs (mem_erase.mp ht).1) vt vs
    · intro hv
      have vP : v ∈ P.biUnion id := u ▸ (mem_sdiff.mp hv).1
      obtain ⟨t,ht,vt⟩ := mem_biUnion.mp vP
      have nq : t ≠ s := fun e => (mem_sdiff.mp hv).2 (e ▸ vt)
      exact mem_biUnion.mpr ⟨t,mem_erase.mpr ⟨nq,ht⟩,vt⟩


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


private theorem forced_leaf_tile {W : Type*} [DecidableEq W]
    {G : SimpleGraph W} {S T : Finset W} {b c : W}
    (within : T ⊆ S) (tile : IsTile G T) (inside : b ∈ T)
    (forced : ∀ v ∈ S,G.Adj b v → v=c) :
    ∃ w, w∈T ∧ w≠b ∧ w≠c ∧ G.Adj c w ∧ T = {b,c,w} := by
  obtain ⟨tc,o,oin,star⟩ := tile
  have other : o ≠ b := by
    intro eb
    subst o
    have sub : T ⊆ {b,c} := by
      intro v hv
      by_cases hvb : v=b
      · simp [hvb]
      · simp [forced v (within hv) (star v hv hvb)]
    have tiny := card_le_card sub
    have atMost : ({b,c}:Finset W).card ≤ 2 := (card_insert_le b {c}).trans (by simp)
    omega
  have oc := forced o (within oin) (star b inside other.symm).symm
  subst o
  have bn : ({b,c}:Finset W).card ≤ 2 := (card_insert_le b {c}).trans (by simp)
  obtain ⟨w,ww,wo⟩ := exists_mem_not_mem_of_card_lt_card (by omega :
    ({b,c}:Finset W).card<T.card)
  have ⟨wb,wc⟩ : w ≠ b ∧ w ≠ c := by simpa using wo
  have sub : ({b,c,w}:Finset W) ⊆ T := by
    intro v hv
    simp only [mem_insert,mem_singleton] at hv
    rcases hv with rfl|rfl|rfl <;> assumption
  have equal := (eq_of_subset_of_card_le sub (by
    rw [tc]
    simp [card_insert_of_not_mem,other.symm,wb.symm,wc.symm])).symm
  exact ⟨w,ww,wb,wc,star w ww wc,equal⟩

variable {V : Type u} [Fintype V] [DecidableEq V]

private abbrev mid : V ⊕ Fin 3 := Sum.inr 1
private abbrev kept : V ⊕ Fin 3 := Sum.inr 2
private abbrev discarded : V ⊕ Fin 3 := Sum.inr 0

def restrictedCap (G : SimpleGraph V) (p : Port ↪ V) :=
  omitEdge (pathCap G p) mid (Sum.inl (p 0))

private theorem pathPorts0 : ∀ i : Port,pathRoot i=1 ↔ i=0 := by decide
private theorem pathPorts2 : ∀ i : Port,pathRoot i=2 ↔ i=1∨i=4 := by decide
private theorem middleNeighbors : ∀ i : Fin 3,path3.Adj 1 i → i=0∨i=2 := by decide
private theorem keptNeighbors : ∀ i : Fin 3,path3.Adj 2 i → i=1 := by decide
private theorem allThree : ∀ i : Fin 3, i=0∨i=1∨i=2 := by decide

/-- The exact one-contact decoupling needed after an ear is absorbed:
delete the discarded cap leaf and omit the midpoint's wire. Then the
midpoint is forced to use the kept leaf and one of its two ports.
Deleting this forced tile leaves a factor on the old exterior
minus that port. No assumption about the rest of the factor is made. -/
theorem decode_restricted_cap {G : SimpleGraph V} {p : Port ↪ V}
    (f : FactorOn (restrictedCap G p) (univ.erase discarded)) :
    ∃ x, (x=p 1 ∨ x=p 4) ∧ FactorOn G (univ.erase x) := by
  have adjOnly (v : V⊕Fin 3) (vS : v∈univ.erase discarded)
      (ed : (restrictedCap G p).Adj mid v) : v=kept := by
    cases v with
    | inl w =>
      obtain ⟨i,iw,ip⟩ : ∃ i,p i=w ∧ pathRoot i=1 := ed.1
      have eq : w=p 0 := by
        obtain rfl := (pathPorts0 i).mp ip
        exact iw.symm
      exact (ed.2 (Or.inl ⟨rfl,congrArg Sum.inl eq⟩)).elim
    | inr i =>
      have dat : path3.Adj 1 i := ed.1
      rcases middleNeighbors i dat with rfl|rfl
      · exact ((mem_erase.mp vS).1 rfl).elim
      · rfl
  have rootMem : (mid : V⊕Fin 3)∈univ.erase discarded := by simp
  obtain ⟨T,inS,inT,tile,rem⟩ := factor_erase_one f rootMem
  obtain ⟨w,_,wn,_,edge,teq⟩ := forced_leaf_tile inS tile inT adjOnly
  cases w with
  | inr i =>
    have ne := wn
    have e : i=1 := keptNeighbors i edge.1
    subst i
    exact (ne rfl).elim
  | inl x =>
    obtain ⟨i,eq,ip⟩ : ∃ i,p i=x ∧ pathRoot i=2 := edge.1
    have possible : x=p 1∨x=p 4 := by
      rcases (pathPorts2 i).mp ip with rfl|rfl
      · exact Or.inl eq.symm
      · exact Or.inr eq.symm
    let e : V ↪ V⊕Fin 3 := ⟨Sum.inl,Sum.inl_injective⟩
    have support : ((univ : Finset V).erase x).map e =
        (univ.erase discarded) \ T := by
      rw [teq]
      ext z
      cases z with
      | inl v => simp [e,mem_map]
      | inr j => rcases allThree j with rfl|rfl|rfl <;> simp [e,mem_map]
    rw [←support] at rem
    exact ⟨x,possible,pullback (G:=G) (H:=restrictedCap G p) e (fun _ _ _ _ ed => ed.1) rem⟩

#print axioms decode_restricted_cap


end
end KelmansCactus.AtomicBridge.EarDecode
