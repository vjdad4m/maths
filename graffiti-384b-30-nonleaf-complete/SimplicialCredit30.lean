import HighBasics28
import CleanTrial
namespace Graffiti384b.EarMix
open Finset SimpleGraph Thin28
open private CliqueChoice.degree_neighbor from CliqueChoice384b
open private Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def active (P k : Finset V) := k.filter (fun v => trianglesAt G v=(G.degree v).choose 2 ∧ 2≤nbr G v (P∪k))
def gain (W P : Finset V) (b : ℕ) (v : V) := ((W.powersetCard b).filter (fun k => v∈active G P k)).card

theorem clean (W P k : Finset V) (sub : k⊆W) (inj : Set.InjOn (trianglesAt G) (W:Set V)) :
    gamma G+(active G P k).card≤P.card+k.card+(misses G P k).card := by
  classical
  let A := active G P k
  let R := P∪k
  let s := R\A
  have ar : A⊆k := filter_subset .. 
  have no {x y : V} (xm : x∈A) (ym : y∈A) : ¬G.Adj x y := by
    intro xy
    have sx := (mem_filter.mp xm).2.1
    have sy := (mem_filter.mp ym).2.1
    have eq := Nat.le_antisymm (CliqueChoice.degree_neighbor G (CliqueChoice.saturated_clique G sx) xy)
      (CliqueChoice.degree_neighbor G (CliqueChoice.saturated_clique G sy) xy.symm)
    exact xy.ne (inj (sub (ar xm)) (sub (ar ym)) (sx.trans ((congrArg (fun d : ℕ => d.choose 2) eq).trans sy.symm)))
  have rescue {p z : V} (pm : p∈A) (zs : z∉s) (near : z=p ∨ G.Adj p z) : 2≤nbr G z s := by
    apply (mem_filter.mp pm).2.2.trans (card_le_card ?_)
    intro y ym
    obtain ⟨yr,py⟩ := mem_filter.mp ym
    have ys : y∈s := mem_sdiff.mpr ⟨yr,fun ya => no pm ya py⟩
    apply mem_filter.mpr ⟨ys,?_⟩
    rcases near with rfl|pw
    · exact py
    · exact CliqueChoice.saturated_clique G (mem_filter.mp pm).2.1 _ _ pw py (fun eq => zs (eq ▸ ys))
  let D := s∪misses G P k
  have dom : TwoDominates G D := by
    intro z zo
    have zs : z∉s := fun m => zo (mem_union_left _ m)
    apply LE.le.trans ?_ (Repair.nbr_mono G z (show s⊆D from subset_union_left))
    by_cases za : z∈A
    · exact rescue za zs (Or.inl rfl)
    by_cases nb : ∃p∈A,G.Adj p z
    · obtain ⟨p,pm,pz⟩ := nb
      exact rescue pm zs (Or.inr pz)
    have zr : z∉R := fun m => zs (mem_sdiff.mpr ⟨m,za⟩)
    have enough : 2≤nbr G z R := Nat.le_of_not_gt (fun low => zo (mem_union_right _
      (mem_filter.mpr ⟨mem_compl.mpr zr,low⟩)))
    apply enough.trans (card_le_card ?_)
    intro y ym
    obtain ⟨yr,zy⟩ := mem_filter.mp ym
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨yr,fun ya => nb ⟨y,ya,zy.symm⟩⟩,zy⟩
  have ub : gamma G≤D.card := Nat.sInf_le ⟨D,dom,rfl⟩
  have ds := card_union_le s (misses G P k)
  have size : s.card+A.card=R.card := card_sdiff_add_card_eq_card (ar.trans subset_union_right)
  have rs := card_union_le P k
  change gamma G≤(s∪misses G P k).card at ub
  change s.card+A.card=(P∪k).card at size
  change gamma G+A.card≤_; omega

theorem mass (W P : Finset V) (b : ℕ) (inj : Set.InjOn (trianglesAt G) (W:Set V))
    (large : P.card+b+3≤gamma G) :
    3*W.card.choose b+(∑v,gain G W P b v)≤∑v,hit G W P b v := by
  classical
  have per (k : Finset V) (km : k∈W.powersetCard b) :
      3+(active G P k).card≤(misses G P k).card := by
    obtain ⟨ks,kc⟩ := mem_powersetCard.mp km
    have win := clean G W P k ks inj; omega
  have all := sum_le_sum per
  have flip (F : Finset V → Finset V) : (∑ k∈W.powersetCard b,(F k).card)=
      ∑v,((W.powersetCard b).filter (fun k => v∈F k)).card := by
    calc _ = ∑ k∈W.powersetCard b,∑v,if v∈F k then 1 else 0 := by simp
         _ = _ := by rw [sum_comm]; simp [sum_boole]
  simpa only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,card_powersetCard,
    flip (active G P),flip (misses G P),gain,hit,Nat.mul_comm 3] using all

theorem active_fiber {W P : Finset V} {w : V} (wm : w∈W) (wp : w∉P)
    (sat : trianglesAt G w=(G.degree w).choose 2) (k : ℕ) :
    (W.card-1).choose k≤gain G W P (k+1) w+hit G W P k w := by
  classical
  let K := (W.erase w).powersetCard k
  let ok := fun s : Finset V => 2≤nbr G w (P∪s)
  have total := filter_card_add_filter_neg_card_eq_card (s:=K) ok
  have ks : K.card=(W.card-1).choose k := by dsimp [K]; rw [card_powersetCard,card_erase_of_mem wm]
  have off {s : Finset V} (sm : s∈K) : w∉s := fun m => (mem_erase.mp ((mem_powersetCard.mp sm).1 m)).1 rfl
  have fail : K.filter (fun s => ¬ok s)⊆(W.powersetCard k).filter (fun s => w∈misses G P s) := by
    intro s sm; obtain ⟨sk,no⟩ := mem_filter.mp sm
    obtain ⟨se,sc⟩ := mem_powersetCard.mp sk
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨se.trans (erase_subset ..),sc⟩,
      mem_filter.mpr ⟨mem_compl.mpr (fun h => (mem_union.mp h).elim wp (off sk)),Nat.lt_of_not_ge no⟩⟩
  let J := K.filter ok
  have insertInj : Set.InjOn (insert w) (J:Set (Finset V)) := by
    intro s sm t tm eq
    simpa [erase_insert (off (mem_filter.mp sm).1),erase_insert (off (mem_filter.mp tm).1)] using congrArg (fun S : Finset V => S.erase w) eq
  have inc : J.image (insert w)⊆(W.powersetCard (k+1)).filter (fun s => w∈active G P s) := by
    intro t tm; obtain ⟨s,sm,rfl⟩ := mem_image.mp tm
    obtain ⟨sk,yes⟩ := mem_filter.mp sm
    obtain ⟨se,sc⟩ := mem_powersetCard.mp sk
    rw [mem_filter,mem_powersetCard]
    exact ⟨⟨insert_subset wm (se.trans (erase_subset ..)),by rw [card_insert_of_not_mem (off sk),sc]⟩,
      mem_filter.mpr ⟨mem_insert_self ..,sat,yes.trans (Repair.nbr_mono G w (union_subset_union Subset.rfl (subset_insert ..)))⟩⟩
  have count := card_le_card inc
  rw [card_image_of_injOn insertInj] at count
  have missing := card_le_card fail
  change J.card+_=K.card at total
  change _≤((W.powersetCard (k+1)).filter (fun s => w∈active G P s)).card+
    ((W.powersetCard k).filter (fun s => w∈misses G P s)).card
  omega

end Graffiti384b.EarMix
#print axioms Graffiti384b.EarMix.clean
#print axioms Graffiti384b.EarMix.mass
#print axioms Graffiti384b.EarMix.active_fiber
