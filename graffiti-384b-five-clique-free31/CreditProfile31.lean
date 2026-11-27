import CreditRanks31
namespace Graffiti384b.EarCredit
open SimpleGraph Finset
open private Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def cubics := univ.filter (fun z => G.degree z=3 ∧ trianglesAt G z=3)
def pins (e : V) := insert e (cubics G)

structure Ledger (e : V) (r : V→ℕ) : Prop where
  few : (cubics G).card≤1
  injective : Set.InjOn r (((pins G e)ᶜ:Finset V):Set V)
  valid : ∀ v∈(pins G e)ᶜ,r v<m (cubics G).card
  tests : ∀ v∈(pins G e)ᶜ,
    (mark (cubics G).card (r v)≤RankTable.cap (min (G.degree v) 10) 3 ∨ min (G.degree v) 10=10) ∧
    (3≤mark (cubics G).card (r v) → 4≤min (G.degree v) 10)
  total : (∑ v∈(pins G e)ᶜ,credit G (cubics G).card (pins G e) r v)≤gap (cubics G).card

theorem nonadjacent {e s : V} (de : G.degree e=2) (ds : s∈cubics G) : ¬G.Adj s e := by
  intro edge; obtain ⟨d,score⟩ := (mem_filter.mp ds).2
  have cl := CliqueChoice.saturated_clique G (v:=s) (by rw [score,d]; decide)
  have sub : insert s ((G.neighborFinset s).erase e)⊆G.neighborFinset e := by
    apply insert_subset ((G.mem_neighborFinset ..).mpr edge.symm)
    intro w wm; obtain ⟨ne,wn⟩ := mem_erase.mp wm
    exact (G.mem_neighborFinset ..).mpr (cl e w edge ((G.mem_neighborFinset ..).mp wn) ne.symm)
  have off : s∉(G.neighborFinset s).erase e := fun h => G.not_mem_neighborFinset_self _ (mem_erase.mp h).2
  have c := card_le_card sub
  rw [card_insert_of_not_mem off,card_erase_of_mem ((G.mem_neighborFinset ..).mpr edge),
    card_neighborFinset_eq_degree,card_neighborFinset_eq_degree,de,d] at c
  omega

theorem ledger {e : V} (n : Fintype.card V=30) (de : G.degree e=2) (one : trianglesAt G e=1)
    (pos : ∀ v,0<trianglesAt G v) (fi : Function.Injective (trianglesAt G))
    (free : G.CliqueFree 5) (hi : 15≤gamma G) : ∃ r,Ledger G e r := by
  classical
  let L := cubics G
  let P := pins G e
  have notin : e∉L := fun h => by have d := (mem_filter.mp h).2.1; omega
  have same {a b : V} (am : a∈L) (bm : b∈L) : a=b :=
    fi ((mem_filter.mp am).2.2.trans (mem_filter.mp bm).2.2.symm)
  have few : L.card≤1 := card_le_one.mpr (fun _ am _ bm => same am bm)
  have ws : Pᶜ.card=m L.card := by
    change (insert e L)ᶜ.card=m L.card
    rw [card_compl,card_insert_of_not_mem notin,n]; unfold m; omega
  have scores (v : V) (vm : v∈Pᶜ) : 2≤trianglesAt G v ∧ (L.card=1 → trianglesAt G v≠3) := by
    have ve : v≠e := fun h => mem_compl.mp vm (h ▸ mem_insert_self ..)
    have ne : trianglesAt G v≠1 := fun h => ve (fi (h.trans one.symm))
    have := pos v
    refine ⟨by omega,?_⟩
    intro h eq; obtain ⟨w,mw⟩ := card_pos.mp (show 0<L.card by omega)
    have vw := fi (eq.trans (mem_filter.mp mw).2.2.symm)
    exact mem_compl.mp vm (mem_insert_of_mem (vw ▸ mw))
  have small (v : V) (vm : v∈Pᶜ) (big : 3≤trianglesAt G v) : 4≤G.degree v := by
    by_contra! low
    have cap := Repair.triangles_le_choose G v
    have d : G.degree v=3 := by
      by_contra! ne
      have b := cap.trans (Nat.choose_le_choose 2 (show G.degree v≤2 by omega))
      change trianglesAt G v≤1 at b; omega
    rw [d] at cap; change trianglesAt G v≤3 at cap
    exact mem_compl.mp vm (mem_insert_of_mem (mem_filter.mpr ⟨mem_univ _,d,by omega⟩))
  have sc (z : V) (zm : z∈P) : CliqueChoice.cliqueAt G z := by
    apply CliqueChoice.saturated_clique
    rcases mem_insert.mp zm with rfl|l
    · rw [one,de]; decide
    · obtain ⟨d,ds⟩ := (mem_filter.mp l).2; rw [d,ds]; decide
  have ind (z : V) (zm : z∈P) : G.neighborFinset z⊆Pᶜ := by
    intro v vn; apply mem_compl.mpr; intro vm; have edge := (G.mem_neighborFinset ..).mp vn
    rcases mem_insert.mp zm with rfl|zl <;> rcases mem_insert.mp vm with rfl|vl
    · exact edge.ne rfl
    · exact nonadjacent G de vl edge.symm
    · exact nonadjacent G de zl edge
    · exact edge.ne (same zl vl)
  have bonus : (∑ z∈P,CliqueSample.bonus (m L.card) (draws L.card) (G.degree z))=
      CliqueSample.bonus (m L.card) (draws L.card) 2+L.card*CliqueSample.bonus (m L.card) (draws L.card) 3 := by
    change (∑ z∈insert e L,_) = _
    rw [sum_insert notin,de]
    have eq := sum_congr (s₁:=L) (s₂:=L) rfl (fun z zm => congrArg (CliqueSample.bonus (m L.card) (draws L.card)) (mem_filter.mp zm).2.1)
    rw [eq,sum_const,nsmul_eq_mul,Nat.cast_id]
  obtain ⟨r,ri,rv,rt,up⟩ := account G few ws n hi free fi scores small sc ind bonus
  exact ⟨r,⟨few,ri,rv,rt,up⟩⟩

end Graffiti384b.EarCredit
#print axioms Graffiti384b.EarCredit.nonadjacent
#print axioms Graffiti384b.EarCredit.ledger
