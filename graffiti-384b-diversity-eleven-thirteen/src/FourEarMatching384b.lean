import LargeLowerProfile384b
import ShorePairs

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph ShorePairs
open scoped BigOperators
open private Repair.omit_set from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Four ordinary ears with disjoint pairs of high anchors yield six omissions.
At most three distinct anchors can obstruct a two-pair swap; each can obstruct
at most one of the six pair choices. -/
theorem exact_of_four_matched_ears (t : (types G).card=11) {O : Finset V}
    (four : O.card=4) (lo : Disjoint O (high G)) (deg : ∀ e∈O,G.degree e=2)
    (hh : ∀ e∈O,G.neighborFinset e ⊆ high G)
    (dN : (O : Set V).PairwiseDisjoint (fun e : V => (G.neighborFinset e : Finset V)))
    (scores : Set.InjOn (trianglesAt G) (high G : Set V))
    (min : ∀ x∈high G,2≤trianglesAt G x) :
    gamma G≤bound G := by
  classical
  let N : V → Finset V := fun e => G.neighborFinset e
  let C := O.powersetCard 2
  let A := fun F : Finset V => F.biUnion N
  have agree {e f x : V} (eO : e∈O) (fO : f∈O) (ex : x∈N e) (fx : x∈N f) :
      e=f := by
    by_contra ne
    exact Finset.disjoint_left.mp (dN eO fO ne) ex fx
  have cover {F : Finset V} (FC : F∈C) : A F ⊆ high G := by
    intro x xA
    obtain ⟨e,eF,ex⟩ := mem_biUnion.mp xA
    exact hh e ((mem_powersetCard.mp FC).1 eF) ex
  have cardA {F : Finset V} (FC : F∈C) : (A F).card=4 := by
    have FF := mem_powersetCard.mp FC
    have dj : (F : Set V).PairwiseDisjoint N := fun e em f fm ne =>
      dN (FF.1 em) (FF.1 fm) ne
    change (F.biUnion N).card=4
    rw [card_biUnion dj]
    calc
      (∑ x ∈ F,(N x).card)=∑ _ ∈ F,2 := sum_congr rfl (fun x xm=>by
        rw [show (N x).card=G.degree x by exact card_neighborFinset_eq_degree ..,
          deg x (FF.1 xm)])
      _=4 := by simp [FF.2]
  have uniqueLow {e x : V} (em : e∈O) (ex : x∈N e) {y : V}
      (yo : y∈O) (xy : G.Adj x y) : y=e :=
    agree yo em ((G.mem_neighborFinset ..).mpr xy.symm) ex
  let free := fun (F : Finset V) (x : V) => ∃ w∉O∪A F,G.Adj x w
  have blockers : ∃ F∈C,∀ x∈A F,free F x := by
    apply Classical.byContradiction
    intro hnone
    have bad (F : C) : ∃ x∈A F.val,¬free F.val x := by
      apply Classical.byContradiction
      intro hn
      exact hnone ⟨F.val,F.property,fun x xm=>Classical.byContradiction
        (fun n=>hn ⟨x,xm,n⟩)⟩
    let b := fun (F : C) => Classical.choose (bad F)
    have bf (F : C) : b F∈A F.val ∧ ¬free F.val (b F) :=
      Classical.choose_spec (bad F)
    have where_block {F : Finset V} {x : V} (n : ¬free F x) {w : V}
        (xw : G.Adj x w) : w∈O∪A F := by
      exact Classical.byContradiction (fun hno => n ⟨w,hno,xw⟩)
    have bs (F : C) : trianglesAt G (b F) ≤ 4 := by
      let x := b F
      obtain ⟨e,eF,ex⟩ := mem_biUnion.mp (bf F).1
      have eO := (mem_powersetCard.mp F.property).1 eF
      have xe : G.Adj x e := ((G.mem_neighborFinset ..).mp ex).symm
      let R := (N x).erase e
      have rsub : R ⊆ (A F.val).erase x := by
        intro w wm
        obtain ⟨we,wn⟩ := mem_erase.mp wm
        have xw := (G.mem_neighborFinset ..).mp wn
        have m : w∈O∪A F.val := where_block (bf F).2 xw
        exact mem_erase.mpr ⟨xw.ne.symm,(mem_union.mp m).resolve_left
          (fun wo=>we (uniqueLow eO ex wo xw))⟩
      have rc : R.card≤3 := by
        have g := card_le_card rsub
        rw [card_erase_of_mem (bf F).1,cardA F.property] at g
        exact g
      have er : nbr G e R≤1 := by
        have inc : R.filter (G.Adj e) ⊆ (N e).erase x := by
          intro y ym
          obtain ⟨yr,ey⟩ := mem_filter.mp ym
          have xy := (G.mem_neighborFinset ..).mp (mem_of_mem_erase yr)
          exact mem_erase.mpr ⟨xy.ne.symm,(G.mem_neighborFinset ..).mpr ey⟩
        have h := card_le_card inc
        rw [card_erase_of_mem ex,show (N e).card=G.degree e from card_neighborFinset_eq_degree ..,
          deg e eO] at h
        exact h
      have p : (pairs G R).card≤3 := by
        have sub : (pairs G R).card≤(R.powersetCard 2).card :=
          card_le_card (filter_subset _ _)
        rw [card_powersetCard] at sub
        apply sub.trans
        have r := Nat.choose_le_choose 2 rc
        exact r.trans (by decide)
      have ne : e∉R := not_mem_erase e (N x) 
      have old : insert e R=N x := insert_erase ((G.mem_neighborFinset ..).mpr xe)
      change (pairs G (N x)).card≤4
      rw [←old,pairs_insert G ne]
      omega
    have bi : Function.Injective b := by
      intro F J eq
      let x := b F
      have xJ : x∈A J.val := by simpa only [x,eq] using (bf J).1
      have nxJ : ¬free J.val x := by simpa only [x,eq] using (bf J).2
      obtain ⟨e,eF,ex⟩ := mem_biUnion.mp (bf F).1
      obtain ⟨f,fJ,fx⟩ := mem_biUnion.mp xJ
      have eO := (mem_powersetCard.mp F.property).1 eF
      have fO := (mem_powersetCard.mp J.property).1 fJ
      have ef := agree eO fO ex fx
      have eJ : e∈J.val := ef ▸ fJ
      obtain ⟨w,xw,wO,we⟩ : ∃ w,G.Adj x w ∧ w∉O ∧ w∉N e := by
        apply Classical.byContradiction
        intro hn
        have sub : N x ⊆ insert e ((N e).erase x) := by
          intro y ym
          have xy := (G.mem_neighborFinset ..).mp ym
          by_cases yo : y∈O
          · exact mem_insert.mpr (Or.inl (uniqueLow eO ex yo xy))
          · exact mem_insert.mpr (Or.inr (mem_erase.mpr ⟨xy.ne.symm,Classical.byContradiction (fun hy=>hn ⟨y,xy,yo,hy⟩)⟩))
        have c := card_le_card sub
        have p := card_insert_le e ((N e).erase x)
        rw [card_erase_of_mem ex,show (N e).card=G.degree e from card_neighborFinset_eq_degree ..,
          deg e eO] at p
        rw [show (N x).card=G.degree x from card_neighborFinset_eq_degree ..] at c
        have d : 3≤G.degree x := (mem_filter.mp (cover F.property (bf F).1)).2
        omega
      have wF : w∈A F.val :=
        (mem_union.mp (where_block (bf F).2 xw)).resolve_left wO
      have wJ : w∈A J.val :=
        (mem_union.mp (where_block nxJ xw)).resolve_left wO
      obtain ⟨g,gF,gw⟩ := mem_biUnion.mp wF
      obtain ⟨h,hJ,hw⟩ := mem_biUnion.mp wJ
      have gh := agree ((mem_powersetCard.mp F.property).1 gF)
        ((mem_powersetCard.mp J.property).1 hJ) gw hw
      have eg : e≠g := fun h=>we (h ▸ gw)
      have gJ : g∈J.val := gh ▸ hJ
      have tok {S : Finset V} (m : S∈C) (es : e∈S) (gs : g∈S) :
          S={e,g} := by
        symm
        apply eq_of_subset_of_card_le (insert_subset es (singleton_subset_iff.mpr gs))
        rw [(mem_powersetCard.mp m).2,card_pair eg]
      exact Subtype.ext ((tok F.property eF gF).trans (tok J.property eJ gJ).symm)
    let K := (high G).filter (fun x=>trianglesAt G x≤4)
    let S := K.image (trianglesAt G)
    have Cn : Fintype.card C=6 := by rw [Fintype.card_coe]; simp [C,four]; decide
    let inj : C → K := fun F=>⟨b F,mem_filter.mpr ⟨cover F.property (bf F).1,bs F⟩⟩
    have cardLE : Fintype.card C≤Fintype.card K :=
      Fintype.card_le_of_injective inj (fun _ _ h=>bi (congrArg Subtype.val h))
    rw [Cn,Fintype.card_coe] at cardLE
    have same : S.card=K.card := card_image_of_injOn (fun x xm y ym h=>
      scores (mem_filter.mp xm).1 (mem_filter.mp ym).1 h)
    have sup : S ⊆ ({2,3,4} : Finset Nat) := by
      intro j jm
      obtain ⟨x,xm,rfl⟩ := mem_image.mp jm
      have a := (mem_filter.mp xm).2
      have b := min x (mem_filter.mp xm).1
      have z : trianglesAt G x=2 ∨ trianglesAt G x=3 ∨ trianglesAt G x=4 := by omega
      simpa using z
    have cap := card_le_card sup
    rw [same,show ({2,3,4} : Finset Nat).card=3 by decide] at cap
    omega
  obtain ⟨F,FC,done⟩ := blockers
  let X := A F
  let T := (O\F)∪X
  have FF := mem_powersetCard.mp FC
  have xcard := cardA FC
  have xhi := cover FC
  have dis : Disjoint (O\F) X := lo.mono sdiff_subset xhi
  have tc : T.card=6 := by
    rw [show T=(O\F)∪X by rfl,card_union_of_disjoint dis,
      card_sdiff FF.1,four,FF.2,xcard]
  have dom : ∀ u∈T,2≤nbr G u Tᶜ := by
    intro u um
    rcases mem_union.mp um with uold|ux
    · obtain ⟨uo,uf⟩ := mem_sdiff.mp uold
      have n : N u ⊆ Tᶜ.filter (G.Adj u) := by
        intro w wm
        apply mem_filter.mpr
        refine ⟨mem_compl.mpr ?_,(G.mem_neighborFinset ..).mp wm⟩
        intro wt
        rcases mem_union.mp wt with wo|wx
        · exact Finset.disjoint_left.mp lo (mem_sdiff.mp wo).1 (hh u uo wm)
        · obtain ⟨e,eF,ew⟩ := mem_biUnion.mp wx
          exact uf ((agree uo (FF.1 eF) wm ew) ▸ eF)
      have h := card_le_card n
      rw [show (N u).card=G.degree u from card_neighborFinset_eq_degree ..,deg u uo] at h
      exact h
    · obtain ⟨e,eF,eu⟩ := mem_biUnion.mp ux
      obtain ⟨w,wo,uw⟩ := done u ux
      have et : e∈Tᶜ := mem_compl.mpr (fun et=> (mem_union.mp et).elim
        (fun h=>(mem_sdiff.mp h).2 eF) (fun h=>Finset.disjoint_left.mp lo (FF.1 eF) (xhi h)))
      have wt : w∈Tᶜ := mem_compl.mpr (fun h=>wo
        ((mem_union.mp h).elim (fun h=>mem_union_left _ (mem_sdiff.mp h).1)
          (fun h=>mem_union_right _ h)))
      have ew : e≠w := fun eq=>wo (mem_union_left _ (eq ▸ FF.1 eF))
      have sub : ({e,w} : Finset V) ⊆ Tᶜ.filter (G.Adj u) := insert_subset
        (mem_filter.mpr ⟨et,((G.mem_neighborFinset ..).mp eu).symm⟩)
        (singleton_subset_iff.mpr (mem_filter.mpr ⟨wt,uw⟩))
      simpa [nbr,card_pair ew] using card_le_card sub
  have h := Repair.omit_set G T dom
  unfold bound
  rw [t]
  omega

#print axioms exact_of_four_matched_ears
end Graffiti384b.DiversityEleven
