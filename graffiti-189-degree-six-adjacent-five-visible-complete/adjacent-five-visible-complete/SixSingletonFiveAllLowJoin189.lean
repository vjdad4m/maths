import SixSingletonFiveAllLowModel189
import SixSingletonFiveAllLowCore189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair PortCertificates PortCertificates.AllLow
open private all_low_port_model from SixSingletonFiveAllLowModel189
open private dark_core_five from SixSingletonFiveThreeBase189
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

private theorem label_cover {L R S : Finset V} {T z w h : V} (F : ProfileThree G L R S T)
    (W : D\S={z,w,h}) (zm : z∈D\S) (wm : w∈D\S) (hm : h∈D\S) :
    univ.image (allLowLabel z w h)=univ\S := by
  ext u
  rw [mem_image,mem_sdiff]
  simp only [mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i
    · exact fun m=>(by decide : (5:V)∉D) (F.core_sub m)
    · exact fun m=>(by decide : (6:V)∉D) (F.core_sub m)
    · exact fun m=>(by decide : (7:V)∉D) (F.core_sub m)
    · exact (mem_sdiff.mp zm).2
    · exact (mem_sdiff.mp wm).2
    · exact (mem_sdiff.mp hm).2
    · exact fun m=>(by decide : a∉D) (F.core_sub m)
    · exact fun m=>(by decide : b∉D) (F.core_sub m)
    · exact fun m=>(by decide : s∉D) (F.core_sub m)
    · exact fun m=>(by decide : x∉D) (F.core_sub m)
    · exact fun m=>(by decide : y∉D) (F.core_sub m)
  intro n
  by_cases m : u∈D
  · have f : u∈D\S := mem_sdiff.mpr ⟨m,n⟩
    rw [W,mem_insert,mem_insert,mem_singleton] at f
    rcases f with q|q|q
    · exact ⟨3,q.symm⟩
    · exact ⟨4,q.symm⟩
    exact ⟨5,q.symm⟩
  have fixed : ∀ u : V,u∉D → u=5 ∨ u=6 ∨ u=7 ∨ u=a ∨ u=b ∨ u=s ∨ u=x ∨ u=y := by decide
  rcases fixed u m with q|q|q|q|q|q|q|q
  · exact ⟨0,q.symm⟩
  · exact ⟨1,q.symm⟩
  · exact ⟨2,q.symm⟩
  · exact ⟨6,q.symm⟩
  · exact ⟨7,q.symm⟩
  · exact ⟨8,q.symm⟩
  · exact ⟨9,q.symm⟩
  exact ⟨10,q.symm⟩

private theorem label_edges {L R S : Finset V} {T z w h : V} (F : ProfileThree G L R S T)
    (ab : G.Adj a b) : ∀ i j,(i,j)∈fixed → G.Adj (allLowLabel z w h i) (allLowLabel z w h j) := by
  intro i j e
  simp only [fixed,List.mem_cons,List.not_mem_nil,or_false] at e
  rcases e with e|e|e|e|e|e|e|e|e|e|e
  · rcases Prod.mk.inj e with ⟨rfl,rfl⟩; exact ab
  · rcases Prod.mk.inj e with ⟨rfl,rfl⟩; exact F.sa.symm
  · rcases Prod.mk.inj e with ⟨rfl,rfl⟩; exact F.sb.symm
  · rcases Prod.mk.inj e with ⟨rfl,rfl⟩; exact F.ax
  · rcases Prod.mk.inj e with ⟨rfl,rfl⟩; exact F.by'
  · rcases Prod.mk.inj e with ⟨rfl,rfl⟩; exact (F.commonA 5 (by decide)).symm
  · rcases Prod.mk.inj e with ⟨rfl,rfl⟩; exact (F.commonB 5 (by decide)).symm
  · rcases Prod.mk.inj e with ⟨rfl,rfl⟩; exact (F.commonA 6 (by decide)).symm
  · rcases Prod.mk.inj e with ⟨rfl,rfl⟩; exact (F.commonB 6 (by decide)).symm
  · rcases Prod.mk.inj e with ⟨rfl,rfl⟩; exact (F.commonA 7 (by decide)).symm
  · rcases Prod.mk.inj e with ⟨rfl,rfl⟩; exact (F.commonB 7 (by decide)).symm

/-- The last five-visible case: every balance is low and one is tiny.
The five-vertex dark core is Hamilton-connected, and every balance
attaches to it. The certified eleven-position tail covers the rest. -/
theorem traceable_all_balances_low_one_tiny {L R S : Finset V} {T z : V}
    (F : ProfileThree G L R S T) (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ u,(EvenFrom G u).card≤7)
    (zm : z∈D\S) (tiny : (inside G D z).card≤2)
    (low : ∀ u∈D\S,(inside G D u).card≤3) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ u,u∈p.support := by
  classical
  let W := D\S
  have w3 : W.card=3 := F.balance
  have r2 : (W.erase z).card=2 := by rw [card_erase_of_mem zm,w3]
  obtain ⟨w,h,wh,shape⟩ := card_eq_two.mp r2
  have ew : w∈W.erase z := by simp [shape]
  have eh : h∈W.erase z := by simp [shape]
  have wm := (mem_erase.mp ew).2
  have hm := (mem_erase.mp eh).2
  have zw := (mem_erase.mp ew).1.symm
  have zh := (mem_erase.mp eh).1.symm
  have exactW : W={z,w,h} := by rw [←shape,insert_erase zm]
  let f := allLowLabel z w h
  have cover : univ.image f=univ\S := label_cover F exactW zm wm hm
  have n : (univ.image f).card=(univ : Finset (Fin 11)).card := by
    rw [cover,card_sdiff (subset_univ _),card_univ,card_univ,dark_core_five F]
    decide
  have fInj : Function.Injective f := fun _ _ e=>Finset.card_image_iff.mp n (mem_univ _) (mem_univ _) e
  have M : PortModel (bitGraph G f) :=
    all_low_port_model F hc even zm wm hm zw zh wh exactW tiny (low w wm) (low h hm)
  obtain ⟨j,tag,t,tail⟩ := port_walk f fInj (label_edges (z:=z) (w:=w) (h:=h) F ab) M
  rw [cover] at tail
  have jW : f j∈D\S := by
    rcases tag with rfl|rfl|rfl
    · exact zm
    · exact wm
    exact hm
  obtain ⟨i,iS,edge⟩ := all_low_every_balance_hits_core F low jW
  obtain ⟨l,lS,li⟩ := exists_ne_of_one_lt_card (s:=S) (by rw [dark_core_five F]; decide) i
  have p := all_low_core_route F low zm tiny l lS i iS li
  have ds : Disjoint S ((univ:Finset V)\S) := disjoint_left.mpr (fun _ q n=>(mem_sdiff.mp n).2 q)
  obtain ⟨k,kp,ks⟩ := p.join tail ds edge
  refine ⟨l,t,k,kp,fun u=>(ks u).mpr ?_⟩
  by_cases h : u∈S
  · exact mem_union_left _ h
  exact mem_union_right _ (mem_sdiff.mpr ⟨mem_univ _,h⟩)

#print axioms traceable_all_balances_low_one_tiny
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
