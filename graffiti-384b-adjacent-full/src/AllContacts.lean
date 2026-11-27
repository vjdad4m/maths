import ThreeEars
namespace Graffiti384b.Adjacent12
open Finset SimpleGraph
open private LowSample.two_degree from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Number of distinct exterior vertices contacting at least one neighbor of an ear. -/
def contacts (e : V) := ((insert e (G.neighborFinset e))ᶜ.filter
    (fun i => 0<nbr G i (G.neighborFinset e))).card

private theorem other_neighbor {u v : V} (uv : G.Adj u v) (dv : G.degree v=2) :
    ∃ z,G.Adj v z ∧ z≠u ∧ G.neighborFinset v={u,z} := by
  obtain ⟨z,zm,zu⟩ := exists_mem_ne (s:=G.neighborFinset v) (by rw [card_neighborFinset_eq_degree,dv]; decide) u
  have vz := (G.mem_neighborFinset ..).mp zm
  have sub : {u,z}⊆G.neighborFinset v := insert_subset ((G.mem_neighborFinset ..).mpr uv.symm) (singleton_subset_iff.mpr zm)
  exact ⟨z,vz,zu,(eq_of_subset_of_card_le sub (by rw [card_pair zu.symm,card_neighborFinset_eq_degree,dv])).symm⟩

/-- In an adjacent-pair failure, the remaining ear has at most eleven
contacts. Each endpoint has at most twelve, and at most one endpoint can attain twelve. -/
theorem all_caps (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    {u v : V} (uv : G.Adj u v) (du : G.degree u=2) (dv : G.degree v=2) (bad : bound G<gamma G) :
    contacts G u≤12 ∧ contacts G v≤12 ∧ (contacts G u≤11 ∨ contacts G v≤11) ∧
    ∀ f,G.degree f=2 → f≠u → f≠v → contacts G f≤11 := by
  classical
  obtain ⟨_,ts⟩ := Cover31.residual G t q bad
  have rest := le_card_sdiff ({u,v}:Finset V) (LowSample.twos G)
  rw [ts,card_pair uv.ne] at rest
  obtain ⟨f,fm⟩ := card_pos.mp (show 0<((LowSample.twos G)\{u,v}).card by omega)
  obtain ⟨ft,fo⟩ := mem_sdiff.mp fm
  have df := LowSample.two_degree G ft
  have fu : f≠u := fun eq => fo (mem_insert.mpr (Or.inl eq))
  have fv : f≠v := fun eq => fo (mem_insert_of_mem (mem_singleton.mpr eq))
  have size : (nonleaves G)ᶜ.card=1 := by rw [card_compl,n,q]
  obtain ⟨l,lm⟩ := card_pos.mp (show 0<(nonleaves G)ᶜ.card by omega)
  have dl : G.degree l≤1 := by
    by_contra! large; exact mem_compl.mp lm (mem_filter.mpr ⟨mem_univ _,by omega⟩)
  have profile {i j k : V} (ij : G.Adj i j) (di : G.degree i=2) (dj : G.degree j=2)
      (dk : G.degree k=2) (ki : k≠i) (kj : k≠j) {z : V} (jz : G.Adj j z) (zi : z≠i)
      (jn : G.neighborFinset j={i,z}) : contacts G k≤11 ∧ contacts G j+
      (if G.Adj i z then 1 else 0)+(if G.Adj z l then 0 else 1)≤12 := by
    obtain ⟨a,b,ab,ear⟩ := card_eq_two.mp ((card_neighborFinset_eq_degree ..).trans dk)
    have cap := contact_profile G n q t ij di dj ki.symm kj.symm ear ab jz zi dl bad
    dsimp only at cap
    have th := (Adjacent15.all_ears G n q t ij di dj bad ear ab).1
    have zw : z∈(insert k ({a,b}:Finset V))ᶜ := by
      apply mem_compl.mpr; intro m
      rcases mem_insert.mp m with eq|za
      · subst z
        exact (not_lt_of_ge (Adjacent15.two_steps G ki.symm di dk ij dj.le jz.symm dj.le ij.ne.symm)) bad
      · have kz : G.Adj k z := (G.mem_neighborFinset ..).mp (ear ▸ za)
        exact (not_lt_of_ge (Adjacent15.shared_anchor G ij jz kz ki.symm kj.symm di dj dk)) bad
    have one := (PortRepair29.thin_degrees G ear th z zw).1
    unfold contacts; rw [ear,jn]
    exact ⟨by omega,by omega⟩
  obtain ⟨z,vz,zu,vn⟩ := other_neighbor G uv dv
  obtain ⟨w,uw,wv,un⟩ := other_neighbor G uv.symm du
  have cv := (profile uv du dv df fu fv vz zu vn).2
  have cu := (profile uv.symm dv du df fv fu uw wv un).2
  refine ⟨by omega,by omega,?_,fun k dk ku kv => (profile uv du dv dk ku kv vz zu vn).1⟩
  by_contra! both
  have zl : G.Adj z l := by by_contra h; rw [if_neg h] at cv; omega
  have wl : G.Adj w l := by by_contra h; rw [if_neg h] at cu; omega
  have zw : z≠w := by
    intro eq; subst w; rw [if_pos uw] at cv; omega
  have sub : {z,w}⊆G.neighborFinset l := insert_subset ((G.mem_neighborFinset ..).mpr zl.symm)
    (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr wl.symm))
  have ct := card_le_card sub
  rw [card_pair zw,card_neighborFinset_eq_degree] at ct; omega

end Graffiti384b.Adjacent12
#print axioms Graffiti384b.Adjacent12.all_caps
