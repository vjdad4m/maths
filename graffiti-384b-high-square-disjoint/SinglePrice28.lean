import HighBasics28

namespace Graffiti384b.HighSquare28
open SimpleGraph Finset HighEar Thin28
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

theorem endpoint_limit {e p q s : V} (en : H.neighborFinset e={p,q}) (pq : H.Adj p q)
    (single : additional H e p q={s}) :
    let W := ({e,p,q}:Finset V)ᶜ
    nbr H p W+2=H.degree p ∧ trianglesAt H p≤2+(nbr H p W).choose 2 := by
  classical
  let W := ({e,p,q}:Finset V)ᶜ
  have ep := (H.mem_neighborFinset ..).mp (en ▸ mem_insert_self ..)
  have eq' := (H.mem_neighborFinset ..).mp (en ▸ mem_insert_of_mem (mem_singleton_self _))
  have l := (exact_count H en ep eq' pq).2
  change trianglesAt H p=1+(additional H e p q).card+(pairs H (exterior H e p q)).card at l
  have ex : exterior H e p q=W.filter (H.Adj p) := by
    ext z
    simp only [exterior,W,mem_sdiff,mem_compl,mem_insert,mem_singleton,H.mem_neighborFinset,mem_filter]
    constructor
    · rintro ⟨pz,off⟩
      exact ⟨fun h => h.elim (fun he => off (Or.inl he)) (fun h => h.elim pz.ne.symm (fun hq => off (Or.inr hq))),pz⟩
    · rintro ⟨off,pz⟩
      exact ⟨pz,fun h => off (h.imp_right Or.inr)⟩
  have cap := card_filter_le ((exterior H e p q).powersetCard 2) (fun E => ∀ x∈E,∀ y∈E,x≠y → H.Adj x y)
  change (pairs H (exterior H e p q)).card≤_ at cap
  rw [card_powersetCard,ex] at cap
  have count := exact_count H en ep eq' pq
  have dg := count.1
  change (exterior H e p q).card+2=H.degree p at dg
  rw [ex] at dg
  refine ⟨dg,?_⟩
  rw [single,card_singleton,ex] at l
  change trianglesAt H p≤2+((W.filter (H.Adj p)).card).choose 2
  omega

theorem single_charge {W P : Finset V} {e v : V} (ws : W.card=25) (vm : v∈W)
    (dis : Disjoint P W) (ps : P.card=2) (free : H.CliqueFree 5)
    (deg : nbr H v W+nbr H v P=H.degree v) (hi : nbr H v P=2 → 5≤H.degree v)
    (i : Fin 27) (lb : i.val+2≤trianglesAt H v) :
    3*hit H W P 8 v+hit H W {e} 10 v+205000*nbr H v P≤residualPrice i+
      (if H.degree v=3 then 726750 else 0)+(if nbr H v P=2 then 292516 else 0) := by
  have small := pool_degree H vm
  have csmall : nbr H v P≤2 := (card_filter_le ..).trans ps.le
  have cap := (local_cap H free v).imp_left lb.trans
  have tbl := single_rows i ⟨nbr H v W,by omega⟩ ⟨nbr H v P,by omega⟩ (by rw [deg]; exact cap)
    (by rw [deg]; exact hi)
  dsimp only at tbl
  rw [deg] at tbl
  have f := bill_bound H dis vm 8
  rw [ws] at f
  have g := plain H (P:={e}) (b:=10) vm
  rw [ws] at g
  exact (Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 3 f) g) _).trans tbl

end Graffiti384b.HighSquare28
#print axioms Graffiti384b.HighSquare28.endpoint_limit
#print axioms Graffiti384b.HighSquare28.single_charge
