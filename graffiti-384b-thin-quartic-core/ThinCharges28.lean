import ThinTable28
import ThinTrial28

namespace Graffiti384b.Thin28
open Finset SimpleGraph HighEar
open private Repair.full_nbr from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

theorem exterior_charge {W P : Finset V} {e v : V} (size : W.card=25)
    (vm : v∈W) (dis : Disjoint P W) (one : nbr H v P≤1)
    (deg : nbr H v W+nbr H v P=H.degree v) (free : H.CliqueFree 5)
    (i : Fin 27) (rank : i.val+2≤trianglesAt H v) :
    3*hit H W P 8 v+hit H W {e} 10 v+205000*nbr H v P≤price i := by
  classical
  have room : nbr H v W≤24 := by
    have sub : W.filter (H.Adj v)⊆W.erase v := by
      intro z zm; exact mem_erase.mpr ⟨(mem_filter.mp zm).2.ne.symm,(mem_filter.mp zm).1⟩
    have h := card_le_card sub
    rwa [card_erase_of_mem vm,size] at h
  let d := H.degree v
  have ds : d<26 := by dsimp [d]; omega
  have cap : i.val+2≤RankTable.cap d 3 ∨ 10≤d := by
    by_cases big : 10≤d
    · exact Or.inr big
    have h := RankTuran.local_turan H 3 (by decide) free v
    have tab := RankTable.cap_table ⟨d,by omega⟩ ⟨3,by decide⟩ (by decide)
    change (turanGraph d 3).edgeFinset.card=RankTable.cap d 3 at tab
    exact Or.inl (rank.trans (h.trans_eq tab))
  have tab := exterior_rows i ⟨d,ds⟩ cap
  dsimp only at tab
  have ear := plain H (P:={e}) (b:=10) vm
  rw [size] at ear
  change nbr H v W+nbr H v P=d at deg
  by_cases z : nbr H v P=0
  · have pv := plain H (P:=P) (b:=8) vm
    have de : nbr H v W=d := by omega
    rw [size,de] at pv
    rw [de] at ear
    rw [z,Nat.mul_zero,Nat.add_zero]
    exact (Nat.add_le_add (Nat.mul_le_mul_left 3 pv) ear).trans tab.1
  · obtain ⟨w,wm⟩ := card_pos.mp (show 0<(P.filter (H.Adj v)).card from Nat.pos_of_ne_zero z)
    obtain ⟨wp,vw⟩ := mem_filter.mp wm
    have pv := credited H (b:=8) wp (show w∉W from disjoint_left.mp dis wp) vw
    have c : nbr H v P=1 := by omega
    have df : nbr H v W=d-1 := by omega
    have dif : 25-1-nbr H v W=25-d := by omega
    rw [size,if_pos vm,dif] at pv
    rw [df] at ear
    rw [c,Nat.mul_one]
    exact (Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 3 pv) ear) 205000).trans
      (tab.2 (by omega))

/-- With no second common neighbor, all endpoint triangles except the ear
triangle lie entirely on its private exterior neighbors. -/
theorem thin_endpoint {e p q : V} (en : H.neighborFinset e={p,q}) (pq : H.Adj p q)
    (thin : additional H e p q=∅) :
    let W := ({e,p,q}:Finset V)ᶜ
    trianglesAt H p≤1+(nbr H p W).choose 2 := by
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
  rw [thin,card_empty,Nat.add_zero,ex] at l
  change trianglesAt H p≤1+((W.filter (H.Adj p)).card).choose 2
  omega

end Graffiti384b.Thin28
#print axioms Graffiti384b.Thin28.exterior_charge
#print axioms Graffiti384b.Thin28.thin_endpoint
