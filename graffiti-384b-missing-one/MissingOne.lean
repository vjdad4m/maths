import CubicSide
import MatchingSide
import ShoreDonors
import EightExchange
namespace Graffiti384b.OddStars.MissingOne
open Finset SimpleGraph LeafCritical ShorePairs PositivePalette
open private LeafCritical.max_compl LeafCritical.balance_max LeafCritical.max_covers from LeafCritical
open private ShoreRanks.active_hit from ShoreRanks
open private ShoreCounts.in_high from ShoreCounts
open private Graffiti384b.cut Graffiti384b.nbr_partition from Proof384b
open private Repair.nbr_mono Repair.omit_set from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- At a half-size between four and six, the same-shore cubic restrictions
give either a contradiction or an extra omission on the high set. -/
private theorem large_side (bad : bound G<gamma G) (one : 1∉types G)
    {S : Finset V} (mx : Maximum (patch G ∅) S) {u v : V} (uv : u≠v)
    (us : u∈S) (vs : v∈S) (su : trianglesAt G u=2) (sv : trianglesAt G v=3)
    (apart : ¬(patch G ∅).Adj u v)
    (classify : ∀w,(patch G ∅).degree w=3 ↔ w=u ∨ w=v)
    (crit : critical (patch G ∅) S={u,v})
    (band : 4≤(high (patch G ∅)∩S).card ∧ (high (patch G ∅)∩S).card≤6) : False := by
  classical
  let J := patch G ∅
  let H := high J
  let A := H∩S
  let B := H∩Sᶜ
  let C : Finset V := {u,v}
  let U := A\C
  have du : J.degree u=3 := (classify _).mpr (Or.inl rfl)
  have dv : J.degree v=3 := (classify _).mpr (Or.inr rfl)
  have ua : u∈A := mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,us⟩
  have va : v∈A := mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,vs⟩
  have cc : C.card=2 := card_pair uv
  have ca : C⊆A := insert_subset ua (singleton_subset_iff.mpr va)
  have dis : Disjoint A B := disjoint_left.mpr (fun _ am bm => mem_compl.mp (mem_inter.mp bm).2 (mem_inter.mp am).2)
  have union : A∪B=H := by ext w; simp [A,B]; tauto
  have sz := (PaletteCorollaries.upper_iff_no_one G bad).mpr one
  have bal := LeafCritical.balance_max G bad sz mx
  have bal' := LeafCritical.balance_max G bad sz (LeafCritical.max_compl _ mx)
  change 2*A.card=H.card at bal
  change 2*B.card=H.card at bal'
  have nbh (w : V) : J.neighborFinset w⊆A∪B := by
    rw [union]; exact fun y ym => ShoreCounts.in_high G bad sz ((J.mem_neighborFinset ..).mp ym)
  have restrict (w : V) (R : Finset V) : nbr J w (H∩R)=nbr J w R := by
    unfold nbr; congr 1
    ext y; simp only [mem_filter,mem_inter]
    exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨ShoreCounts.in_high G bad sz h.2,h.1⟩,h.2⟩⟩
  have crossA {w : V} (wm : w∈S) : crossed J S w=B.filter (J.Adj w) := by
    ext y; simp only [crossed,B,mem_filter,mem_inter,mem_compl,mem_neighborFinset]
    constructor
    · intro h; exact ⟨⟨ShoreCounts.in_high G bad sz h.1,fun ys => h.2 (iff_of_true wm ys)⟩,h.1⟩
    · intro h; exact ⟨h.2,fun e => h.1.2 (e.mp wm)⟩
  have crossB {w : V} (wm : w∉S) : crossed J S w=A.filter (J.Adj w) := by
    ext y; simp only [crossed,A,mem_filter,mem_inter,mem_neighborFinset]
    constructor
    · intro h
      have ys : y∈S := by apply Classical.byContradiction; intro yo; exact h.2 (iff_of_false wm yo)
      exact ⟨⟨ShoreCounts.in_high G bad sz h.1,ys⟩,h.1⟩
    · intro h; exact ⟨h.2,fun e => wm (e.mpr h.1.2)⟩
  have idC : critical J S=C := crit
  have two (w : V) (wc : w∈C) : nbr J w B=2 := by
    have c : w∈critical J S := idC ▸ wc
    have val := (mem_filter.mp c).2
    rwa [crossA (mem_inter.mp (ca wc)).2] at val
  have cover {x : V} (act : x∈active J S) : ∃w∈C,x∈crossed J S w := by
    obtain ⟨w,wm,e⟩ := ShoreRanks.active_hit G bad sz mx act
    exact ⟨w,idC ▸ wm,e⟩
  have thin (x : V) (xa : x∈A) : nbr J x A≤1 := by
    rw [show nbr J x A=nbr J x S from restrict ..]
    apply Nat.le_of_not_gt; intro many
    obtain ⟨w,wc,e⟩ := cover (mem_filter.mpr ⟨(mem_inter.mp xa).1,by simpa [(mem_inter.mp xa).2] using many⟩)
    rw [crossA (mem_inter.mp (ca wc)).2] at e
    exact disjoint_left.mp dis xa (mem_filter.mp e).1
  have cubicMate {w : V} (wc : w∈C) (d : J.degree w=3) : nbr J w A=1 := by
    have part := Graffiti384b.nbr_partition J w S
    have co := two w wc
    rw [show nbr J w B=nbr J w Sᶜ from restrict ..] at co
    rw [show nbr J w A=nbr J w S from restrict ..]; omega
  have um := cubicMate (show u∈C from mem_insert_self ..) du
  have vm := cubicMate (show v∈C from mem_insert_of_mem (mem_singleton_self _)) dv
  have bigB (w : V) (wb : w∈B) : 3≤nbr J w A := by
    have ws := mem_compl.mp (mem_inter.mp wb).2
    have low := LeafCritical.max_covers J (LeafCritical.max_compl J mx) w (mem_inter.mp wb).1 (mem_inter.mp wb).2
    rw [compl_compl,←restrict w S] at low
    change 2≤nbr J w A at low
    apply Nat.le_of_not_gt
    intro n
    have eq : (crossed J S w).card=2 := by rw [crossB ws]; change nbr J w A=2; omega
    have cr : w∈critical J S := mem_filter.mpr ⟨(mem_inter.mp wb).1,eq⟩
    exact disjoint_left.mp dis (ca (idC ▸ cr)) wb
  let Z := crossed J S u∪crossed J S v
  let O := B\Z
  have cZ : Z.card≤4 := by
    have lo := card_union_le (crossed J S u) (crossed J S v)
    change (crossed J S u∪crossed J S v).card≤4
    rw [crossA us,crossA vs] at lo ⊢
    have a := two u (mem_insert_self ..)
    have b := two v (mem_insert_of_mem (mem_singleton_self _))
    change (B.filter (J.Adj u)).card=2 at a
    change (B.filter (J.Adj v)).card=2 at b
    omega
  have mass := card_sdiff_add_card_inter B Z
  have loss := card_le_card (inter_subset_right (s₁:=B) (s₂:=Z))
  change O.card+(B∩Z).card=B.card at mass
  change 4≤A.card ∧ A.card≤6 at band
  have unhit {b : V} (bm : b∈O) {c : V} (cm : c∈C) : ¬J.Adj b c := by
    intro e
    have hit : b∈crossed J S c := by rw [crossA (mem_inter.mp (ca cm)).2]; exact mem_filter.mpr ⟨(mem_sdiff.mp bm).1,e.symm⟩
    have m : c=u ∨ c=v := by simpa only [C,mem_insert,mem_singleton] using cm
    exact (mem_sdiff.mp bm).2 (m.elim (fun eq => mem_union_left _ (eq ▸ hit)) (fun eq => mem_union_right _ (eq ▸ hit)))
  have outside {b : V} (bm : b∈O) : J.neighborFinset b∩A⊆U := fun x xm =>
    mem_sdiff.mpr ⟨(mem_inter.mp xm).2,fun c => unhit bm c ((J.mem_neighborFinset ..).mp (mem_inter.mp xm).1)⟩
  have other {b : V} (bm : b∈O) : nbr J b B≤1 := by
    have wb := (mem_sdiff.mp bm).1
    have ws := mem_compl.mp (mem_inter.mp wb).2
    rw [show nbr J b B=nbr J b Sᶜ from restrict ..]
    apply Nat.le_of_not_gt; intro many
    obtain ⟨c,cm,hit⟩ := cover (mem_filter.mpr ⟨(mem_inter.mp wb).1,by simpa [ws] using many⟩)
    exact unhit bm cm (((J.mem_neighborFinset ..).mp (mem_filter.mp hit).1).symm)
  have four {b : V} (bm : b∈O) : 4≤trianglesAt G b := by
    have wb := (mem_sdiff.mp bm).1
    have deg : 3≤J.degree b := (mem_filter.mp (mem_inter.mp wb).1).2
    have d := skeleton_degree_bound G b
    change J.degree b≤_ at d
    apply Nat.le_of_not_gt
    intro lo
    rcases (show trianglesAt G b=2 ∨ trianglesAt G b=3 by omega) with eq|eq
    · exact disjoint_left.mp dis ((distinct_rich G bad (by omega) (eq.trans su.symm)).symm ▸ ua) wb
    · exact disjoint_left.mp dis ((distinct_rich G bad (by omega) (eq.trans sv.symm)).symm ▸ va) wb
  have finish {D : Finset V} (sub : D⊆A∪B) (count : D.card+1=A.card)
      (dom : ∀x∈(A∪B)\D,2≤nbr J x D) : False := by
    have saving := Repair.omit_set G ((A∪B)\D) (fun x xm => (dom x xm).trans
      (card_le_card (fun y ym =>
        let h := mem_filter.mp ym
        mem_filter.mpr ⟨mem_compl.mpr (fun z => (mem_sdiff.mp z).2 h.1),h.2.1⟩)))
    rw [card_sdiff sub,union] at saving
    change H.card+1=(types G).card at sz
    unfold bound at bad
    omega
  have smallOff (a5 : A.card≤5) {b : V} (bm : b∈O) : False := by
    obtain ⟨p,pu,t,tu,pt,_,_,inc⟩ := MatchingSide.mates J uv ua va apart thin um vm
    have uc : U.card≤3 := by dsimp [U]; rw [card_sdiff ca,cc]; omega
    have pc : {p,t}⊆U := insert_subset pu (singleton_subset_iff.mpr tu)
    have cap := card_le_card inc
    change (pairs J U).card≤((U\{p,t}).powersetCard 2).card at cap
    rw [card_powersetCard,card_sdiff pc,card_pair pt] at cap
    have few := Nat.choose_le_choose 2 (show U.card-2≤1 by omega)
    have h := MatchingSide.link_cap J (nbh b) dis (outside bm) (other bm)
    have r := card_le_card (outside bm)
    change (J.neighborFinset b∩A).card≤U.card at r
    change trianglesAt J b≤(pairs J U).card+(J.neighborFinset b∩A).card at h
    have z : Nat.choose 1 2=0 := by decide
    rw [show trianglesAt J b=trianglesAt G b from patch_scores ..] at h
    have d := four bm
    omega
  by_cases a4 : A.card=4
  · have hit (b : V) (bm : b∈B) : J.Adj u b ∨ J.Adj v b := by
      apply Classical.byContradiction
      intro no
      push_neg at no
      have off : b∉Z := by
        intro zm
        rcases mem_union.mp zm with h|h
        · exact no.1 ((J.mem_neighborFinset ..).mp (mem_filter.mp h).1)
        · exact no.2 ((J.mem_neighborFinset ..).mp (mem_filter.mp h).1)
      exact smallOff (by omega) (mem_sdiff.mpr ⟨bm,off⟩)
    have degree (b : V) (bm : b∈B) : 4≤J.degree b := by
      have lo : 3≤J.degree b := (mem_filter.mp (mem_inter.mp bm).1).2
      have no : J.degree b≠3 := fun e => disjoint_left.mp dis
        (((classify _).mp e).elim (fun h => h ▸ ua) (fun h => h ▸ va)) bm
      omega
    obtain ⟨D,sub,c,d⟩ := EightExchange.three J A B a4 (by omega) dis ua va apart
      ((patch_scores G ∅ u).trans su) um (two _ (mem_insert_self ..))
      (two _ (mem_insert_of_mem (mem_singleton_self _))) nbh hit bigB degree
    exact finish sub (by omega) d
  by_cases five : A.card=5
  · obtain ⟨b,bm⟩ := card_pos.mp (show 0<O.card by omega)
    exact smallOff (by omega) bm
  have six : A.card=6 := by omega
  obtain ⟨b,bm,ge⟩ : ∃b∈O,5≤trianglesAt G b := by
    apply Classical.byContradiction
    intro no
    push_neg at no
    have atMost := card_le_one.mpr (fun p pm q qm =>
      distinct_rich G bad (show 2≤trianglesAt G p by have := four pm; omega)
        (by have := four pm; have := four qm; have := no p pm; have := no q qm; omega))
    change O.card≤1 at atMost
    omega
  have geo := MatchingSide.six_contact J six dis uv ua va apart thin um vm (nbh b) (outside bm) (other bm)
    (show 5≤trianglesAt J b from (patch_scores G ∅ b).symm ▸ ge)
  obtain ⟨D,sub,count,dom⟩ := ShoreDonors.exchange J A B C six (by omega) dis ca cc two bigB geo.1 geo.2.1
    (mem_sdiff.mp bm).1 geo.2.2 (fun _ cm => unhit bm cm)
  exact finish sub (by omega) dom

/-- The Graffiti.pc 384b inequality for every connected graph of order
greater than two in which the triangle count one is absent. -/
theorem exact (conn : G.Connected) (ord : 2<Fintype.card V) (one : 1∉types G) : gamma G≤bound G := by
  apply Nat.le_of_not_gt
  intro bad
  classical
  let J := patch G ∅
  let H := high J
  have cap := UpperThirteen.diversity_cap G conn ord bad one
  obtain ⟨_,u,v,uv,su,sv,sep,char,crit⟩ := PaletteCorollaries.missing_one_failure G conn ord bad one
  obtain ⟨i,j,is,js,_,together⟩ := CubicSide.same_shore G conn ord bad one
  have iu := distinct_rich G bad (show 2≤trianglesAt G i by omega) (is.trans su.symm)
  have jv := distinct_rich G bad (show 2≤trianglesAt G j by omega) (js.trans sv.symm)
  subst i; subst j
  obtain ⟨S,_,val⟩ := exists_max_image (univ:Finset (Finset V)) (fun R => Graffiti384b.cut J R Rᶜ) univ_nonempty
  have mx : Maximum J S := fun R => val R (mem_univ _)
  obtain ⟨A,ma,ua⟩ : ∃A : Finset V,Maximum J A ∧ u∈A := by
    by_cases us : u∈S
    · exact ⟨S,mx,us⟩
    · exact ⟨Sᶜ,LeafCritical.max_compl J mx,mem_compl.mpr us⟩
  have sz := (PaletteCorollaries.upper_iff_no_one G bad).mpr one
  have bal := LeafCritical.balance_max G bad sz ma
  have big := CubicSide.beyond_six G bad one su sv sep char ma
  change 2*(H∩A).card=H.card at bal
  change H.card+1=(types G).card at sz
  change 6<H.card at big
  exact large_side G bad one ma uv ua ((together A ma).mp ua) su sv sep char (crit A ma) (by change 4≤(H∩A).card ∧ (H∩A).card≤6; omega)
end Graffiti384b.OddStars.MissingOne
#print axioms Graffiti384b.OddStars.MissingOne.exact
