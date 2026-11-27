import AdjacentBound
import LowOmissions
namespace Graffiti384b.Adjacent15
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- At the third ear, each missed contact among the low vertex and the outer
support of either endpoint costs an additional unit in the bound fourteen. -/
theorem third_ear_contacts (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    {u v f a b z l : V} (uv : G.Adj u v) (du : G.degree u=2) (dv : G.degree v=2)
    (uf : u≠f) (vf : v≠f) (ear : G.neighborFinset f={a,b}) (ab : a≠b)
    (vz : G.Adj v z) (zu : z≠u) (dl : G.degree l≤1) (bad : bound G<gamma G) :
    let A : Finset V := {a,b}
    let W := (insert f A)ᶜ
    (W.filter (fun i => 0<nbr G i A)).card+
      (({z,l}:Finset V).filter (fun i => nbr G i A=0)).card≤14 := by
  classical
  let A : Finset V := {a,b}
  let W := (insert f A)ᶜ
  let M := ({z,l}:Finset V).filter (fun i => nbr G i A=0)
  change (W.filter (fun i => 0<nbr G i A)).card+M.card≤14
  have df : G.degree f=2 := by rw [←card_neighborFinset_eq_degree,ear,card_pair ab]
  have fa (i : V) (ia : i∈A) : G.Adj f i := (G.mem_neighborFinset ..).mp (ear ▸ ia)
  have anchors (i : V) (ia : i∈A) : 3≤G.degree i := by
    by_contra! low
    exact (not_lt_of_ge (two_steps G uf.symm df du (fa i ia) (by omega) uv dv.le vf)) bad
  have out {i : V} (ne : i≠f) (na : i∉A) : i∈W := mem_compl.mpr (fun h => (mem_insert.mp h).elim ne na)
  have uw := out uf (fun h => by have := anchors u h; omega)
  have vw := out vf (fun h => by have := anchors v h; omega)
  have hz : 3≤G.degree z := by
    by_contra! low
    exact (not_lt_of_ge (two_steps G uv.ne du dv uv dv.le vz (by omega) zu)) bad
  have zw := out (show z≠f by intro eq; subst z; omega) (fun za =>
      (not_lt_of_ge (shared_anchor G uv vz (fa z za) uf vf du dv df)) bad)
  have lw := out (show l≠f by intro eq; subst l; omega) (fun h => by have := anchors l h; omega)
  have peers {i j : V} (ij : G.Adj i j) (di : G.degree i=2) (dj : G.degree j=2)
      (nf : i≠f) (mf : j≠f) : ¬0<nbr G j A := by
    intro h; obtain ⟨k,km⟩ := card_pos.mp h
    obtain ⟨ka,jk⟩ := mem_filter.mp km
    exact (not_lt_of_ge (shared_anchor G ij jk (fa k ka) nf mf di dj df)) bad
  have im {i : V} (h : i∈M) : i=z ∨ i=l := by simpa using (mem_filter.mp h).1
  have sep : Disjoint ({u,v}:Finset V) M := disjoint_left.mpr (by
    intro i pair m
    rcases mem_insert.mp pair with rfl|p
    · rcases im m with eq|eq <;> subst_vars <;> omega
    · rw [mem_singleton.mp p] at m
      rcases im m with eq|eq <;> subst_vars <;> omega)
  let B := ({u,v}:Finset V)∪M
  have bs : B.card=2+M.card := by dsimp [B]; rw [card_union_of_disjoint sep,card_pair uv.ne]
  have bw : B⊆W := union_subset (insert_subset uw (singleton_subset_iff.mpr vw)) (by
    intro i m; rcases im m with rfl|rfl <;> assumption)
  have missed (i : V) (m : i∈B) : ¬0<nbr G i A := by
    rcases mem_union.mp m with p|p
    · rcases mem_insert.mp p with rfl|k
      · exact peers uv.symm dv du vf uf
      · rw [mem_singleton.mp k]; exact peers uv du dv uf vf
    · have h : nbr G i A=0 := (mem_filter.mp p).2; omega
  have omitted (i : V) (m : i∈B) : i=z ∨ G.degree i≤2 := by
    rcases mem_union.mp m with p|p
    · rcases mem_insert.mp p with rfl|k
      · exact Or.inr du.le
      · rw [mem_singleton.mp k]; exact Or.inr dv.le
    · rcases im p with h|rfl
      · exact Or.inl h
      · exact Or.inr (by omega)
  have sub : {u,z}⊆G.neighborFinset v := insert_subset ((G.mem_neighborFinset ..).mpr uv.symm)
    (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr vz))
  have vn := (eq_of_subset_of_card_le sub (by rw [card_pair zu.symm,card_neighborFinset_eq_degree,dv])).symm
  by_contra! excess
  have th := (all_ears G n q t uv du dv bad ear ab).1
  apply supported G n q t ear ab th W rfl B bw omitted missed _ uw vw zw uv zu.symm du dv vn bad
  change 17≤(W.filter (fun i => 0<nbr G i A)).card+B.card
  omega

end Graffiti384b.Adjacent15
#print axioms Graffiti384b.Adjacent15.third_ear_contacts
