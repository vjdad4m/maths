import TenSeeds28
namespace Graffiti384b.Types28
open Finset SimpleGraph Thin28 EarMix LowSample
open private CliqueChoice.degree_neighbor from CliqueChoice384b
open private LowSample.anchor_samples LowSample.two_degree from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def contacts (e : V) := (high G).filter (G.Adj e)
def eligible (E k : Finset V) := E.filter (fun v => contacts G v⊆k)

private theorem trial {E k : Finset V} (low : E⊆twos G) (ind : ∀x∈E,∀y∈E,¬G.Adj x y)
    (inj : Set.InjOn (trianglesAt G) (high G:Set V)) (ks : k⊆high G) :
    gamma G+(high G).card+(eligible G E k).card+(active G (high G)ᶜ k).card≤
    Fintype.card V+k.card+(misses G (high G)ᶜ k).card := by
  classical
  let H := high G
  let U := eligible G E k
  let P := Hᶜ\U
  have uh : U⊆Hᶜ := fun _ um => mem_compl.mpr (mem_sdiff.mp (low (mem_filter.mp um).1)).2
  have left : P∪k⊆Hᶜ∪k := union_subset_union sdiff_subset Subset.rfl
  have retain {v : V} (vm : v∈U) : G.neighborFinset v⊆P∪k := by
    intro y ym
    have vy := (G.mem_neighborFinset ..).mp ym
    by_cases yh : y∈H
    · exact mem_union_right _ ((mem_filter.mp vm).2 (mem_filter.mpr ⟨yh,vy⟩))
    · exact mem_union_left _ (mem_sdiff.mpr ⟨mem_compl.mpr yh,fun yu =>
        ind v (mem_filter.mp vm).1 y (mem_filter.mp yu).1 vy⟩)
  have neigh {v : V} (out : v∉P∪k) (vu : v∉U) :
      ((Hᶜ∪k).filter (G.Adj v))⊆(P∪k).filter (G.Adj v) := by
    intro y ym; obtain ⟨ym,vy⟩ := mem_filter.mp ym
    apply mem_filter.mpr ⟨?_,vy⟩
    rcases mem_union.mp ym with yout|yk
    · exact mem_union_left _ (mem_sdiff.mpr ⟨yout,fun yu =>
        out (retain yu ((G.mem_neighborFinset ..).mpr vy.symm))⟩)
    · exact mem_union_right _ yk
  have smaller : misses G P k ⊆ misses G Hᶜ k := by
    intro v vm; obtain ⟨off,ins⟩ := mem_filter.mp vm
    have out := mem_compl.mp off
    have vu : v∉U := by
      intro u
      have ct := card_le_card (show G.neighborFinset v⊆(P∪k).filter (G.Adj v) from
        fun w wm => mem_filter.mpr ⟨retain u wm,(G.mem_neighborFinset ..).mp wm⟩)
      rw [card_neighborFinset_eq_degree,LowSample.two_degree G (low (mem_filter.mp u).1)] at ct
      exact (not_lt_of_ge ct) ins
    have outside : v∉Hᶜ∪k := fun h => (mem_union.mp h).elim
      (fun vh => out (mem_union_left _ (mem_sdiff.mpr ⟨vh,vu⟩))) (fun vk => out (mem_union_right _ vk))
    exact mem_filter.mpr ⟨mem_compl.mpr outside,(card_le_card (neigh out vu)).trans_lt ins⟩
  have keep : active G Hᶜ k ⊆ active G P k := by
    intro v vm
    obtain ⟨vk,sat,good⟩ := mem_filter.mp vm
    refine mem_filter.mpr ⟨vk,sat,good.trans (card_le_card ?_)⟩
    intro y ym; obtain ⟨ym,vy⟩ := mem_filter.mp ym
    have highV := (mem_filter.mp (ks vk)).2
    have highY := CliqueChoice.degree_neighbor G (CliqueChoice.saturated_clique G sat) vy
    have yh : y∈H := mem_filter.mpr ⟨mem_univ _,highV.trans highY⟩
    exact mem_filter.mpr ⟨mem_union_right _ ((mem_union.mp ym).resolve_left (fun h => mem_compl.mp h yh)),vy⟩
  have win := EarMix.clean G H P k ks inj
  have size : P.card+U.card=Hᶜ.card := card_sdiff_add_card_eq_card uh
  have part := card_compl H
  have order := card_le_univ H
  have a := card_le_card keep; have b := card_le_card smaller
  change gamma G+H.card+U.card+(active G Hᶜ k).card≤Fintype.card V+k.card+(misses G Hᶜ k).card
  omega

theorem ear_mass (hs : (high G).card=26) {E : Finset V} (low : E⊆twos G)
    (ind : ∀x∈E,∀y∈E,¬G.Adj x y) (inj : Set.InjOn (trianglesAt G) (high G:Set V))
    (fail : Fintype.card V-14<gamma G) :
    15935205+(∑v∈high G,gain G (high G) (high G)ᶜ 10 v)+
       (∑e∈E,(26-(contacts G e).card).choose (10-(contacts G e).card)) ≤
      ∑v∈high G,hit G (high G) (high G)ᶜ 10 v := by
  classical
  let H := high G
  let K := H.powersetCard 10
  have per (k : Finset V) (km : k∈K) : 3+(active G Hᶜ k).card+(eligible G E k).card≤(misses G Hᶜ k).card := by
    obtain ⟨kh,kc⟩ := mem_powersetCard.mp km
    have win := trial G low ind inj kh
    change H.card=26 at hs
    change gamma G+H.card+(eligible G E k).card+(active G Hᶜ k).card≤Fintype.card V+k.card+(misses G Hᶜ k).card at win
    omega
  have flip (T : Finset V) (F : Finset V→Finset V) (sub : ∀k∈K,F k⊆T) :
      (∑k∈K,(F k).card)=∑v∈T,(K.filter (fun k => v∈F k)).card := by
    calc _=∑k∈K,∑v∈T,if v∈F k then 1 else 0 := by
           apply sum_congr rfl; intro k km
           simp [sum_boole,filter_mem_eq_inter,inter_eq_right.mpr (sub k km)]
         _=_ := by rw [sum_comm]; simp [sum_boole]
  have af := flip H (active G Hᶜ) (fun k km => (filter_subset ..).trans (mem_powersetCard.mp km).1)
  have bf := flip H (misses G Hᶜ) (fun k _ v vm => Classical.byContradiction (fun out =>
    mem_compl.mp (mem_filter.mp vm).1 (mem_union_left k (mem_compl.mpr out))))
  have ef := flip E (eligible G E) (fun _ _ => filter_subset ..)
  have ec (e : V) (em : e∈E) : (26-(contacts G e).card).choose (10-(contacts G e).card)≤
      (K.filter (fun k => e∈eligible G E k)).card := by
    have n := card_le_card (show contacts G e⊆G.neighborFinset e from fun _ m => (G.mem_neighborFinset ..).mpr (mem_filter.mp m).2)
    rw [card_neighborFinset_eq_degree,LowSample.two_degree G (low em)] at n
    simpa [K,H,hs,eligible,em] using LowSample.anchor_samples H (contacts G e) 10 (filter_subset ..) (by omega)
  have total := sum_le_sum per
  rw [sum_add_distrib,sum_add_distrib,af,bf,ef,sum_const,nsmul_eq_mul,Nat.cast_id] at total
  have size : K.card=5311735 := by rw [show K=H.powersetCard 10 from rfl,card_powersetCard,show H.card=26 from hs]; decide
  rw [size] at total
  have earns := sum_le_sum ec
  change 5311735*3+(∑v∈H,gain G H Hᶜ 10 v)+_≤∑v∈H,hit G H Hᶜ 10 v at total
  change 15935205+(∑v∈H,gain G H Hᶜ 10 v)+_≤∑v∈H,hit G H Hᶜ 10 v
  omega
end Graffiti384b.Types28
#print axioms Graffiti384b.Types28.ear_mass
