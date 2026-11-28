import StarNumbers

namespace CographTree
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
local notation "n" => Fintype.card V
local notation "a" => CubicBridges1160.annihilation G
local notation "r" => Graffiti324.residue G
local notation "e" => edgeCoverNumber G
local notation "o" => AutoGraphForge370.outerNumber G

/-- The seven invariants all count the leaves of the star. -/
theorem cograph_tree_profile (hn : 2 ≤ n) (ht : G.IsTree) (hc : CographRadius.Cograph G) :
    a = n-1 ∧ r = n-1 ∧ e = n-1 ∧ G.indepNum = n-1 ∧ G.maxDegree = n-1 ∧
      G.edgeFinset.card = n-1 ∧ o = some (n-1) := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega : 1 < n)
  obtain ⟨c,h⟩ := star_of_tree_cograph G ht hc
  exact ⟨star_annihilation G h ht hn,star_residue G h hn,star_edge_cover G h ht hn,
    indep G h hn,max_degree G h,edge_size G ht,outer G h ht hn⟩

theorem row1173 (hn : 2 ≤ n) (ht : G.IsTree) (hc : CographRadius.Cograph G) :
    a = e := by
  obtain ⟨ha,hr,he,hi,hd,hs,ho⟩ := cograph_tree_profile G hn ht hc
  omega

theorem row1178 (hn : 2 ≤ n) (ht : G.IsTree) (hc : CographRadius.Cograph G) :
    G.indepNum = r := by
  obtain ⟨ha,hr,he,hi,hd,hs,ho⟩ := cograph_tree_profile G hn ht hc
  omega

theorem row1181 (hn : 2 ≤ n) (ht : G.IsTree) (hc : CographRadius.Cograph G) :
    a = G.indepNum := by
  obtain ⟨ha,hr,he,hi,hd,hs,ho⟩ := cograph_tree_profile G hn ht hc
  omega

theorem row1212 (hn : 2 ≤ n) (ht : G.IsTree) (hc : CographRadius.Cograph G) :
    a = r := by
  obtain ⟨ha,hr,he,hi,hd,hs,ho⟩ := cograph_tree_profile G hn ht hc
  omega

theorem row1215 (hn : 2 ≤ n) (ht : G.IsTree) (hc : CographRadius.Cograph G) :
    e = r := by
  obtain ⟨ha,hr,he,hi,hd,hs,ho⟩ := cograph_tree_profile G hn ht hc
  omega

theorem row1227 (hn : 2 ≤ n) (ht : G.IsTree) (hc : CographRadius.Cograph G) :
    a = G.edgeFinset.card := by
  obtain ⟨ha,hr,he,hi,hd,hs,ho⟩ := cograph_tree_profile G hn ht hc
  omega

theorem row1229 (hn : 2 ≤ n) (ht : G.IsTree) (hc : CographRadius.Cograph G) :
    r = G.edgeFinset.card := by
  obtain ⟨ha,hr,he,hi,hd,hs,ho⟩ := cograph_tree_profile G hn ht hc
  omega

theorem row1257 (hn : 2 ≤ n) (ht : G.IsTree) (hc : CographRadius.Cograph G) :
    a = G.maxDegree := by
  obtain ⟨ha,hr,he,hi,hd,hs,ho⟩ := cograph_tree_profile G hn ht hc
  omega

theorem row1272 (hn : 2 ≤ n) (ht : G.IsTree) (hc : CographRadius.Cograph G) :
    G.maxDegree = r := by
  obtain ⟨ha,hr,he,hi,hd,hs,ho⟩ := cograph_tree_profile G hn ht hc
  omega

theorem row1314 (hn : 2 ≤ n) (ht : G.IsTree) (hc : CographRadius.Cograph G) :
    a + 1 = n := by
  obtain ⟨ha,hr,he,hi,hd,hs,ho⟩ := cograph_tree_profile G hn ht hc
  omega

theorem row1316 (hn : 2 ≤ n) (ht : G.IsTree) (hc : CographRadius.Cograph G) :
    r + 1 = n := by
  obtain ⟨ha,hr,he,hi,hd,hs,ho⟩ := cograph_tree_profile G hn ht hc
  omega

theorem row1415 (hn : 2 ≤ n) (ht : G.IsTree) (hc : CographRadius.Cograph G) :
    (n : ℤ) + (-1) = (r : ℤ) := by
  obtain ⟨ha,hr,he,hi,hd,hs,ho⟩ := cograph_tree_profile G hn ht hc
  omega

theorem row1416 (hn : 2 ≤ n) (ht : G.IsTree) (hc : CographRadius.Cograph G) :
    (n : ℤ) + (-1) = (a : ℤ) := by
  obtain ⟨ha,hr,he,hi,hd,hs,ho⟩ := cograph_tree_profile G hn ht hc
  omega

theorem row1638 (hn : 2 ≤ n) (ht : G.IsTree) (hc : CographRadius.Cograph G) {k : ℕ} (hk : o = some k) :
    k ≤ r := by
  obtain ⟨ha,hr,he,hi,hd,hs,ho⟩ := cograph_tree_profile G hn ht hc
  have hK := Option.some.inj (hk.symm.trans ho)
  omega

theorem row1640 (hn : 2 ≤ n) (ht : G.IsTree) (hc : CographRadius.Cograph G) {k : ℕ} (hk : o = some k) :
    k ≤ a := by
  obtain ⟨ha,hr,he,hi,hd,hs,ho⟩ := cograph_tree_profile G hn ht hc
  have hK := Option.some.inj (hk.symm.trans ho)
  omega

theorem row1643 (hn : 2 ≤ n) (ht : G.IsTree) (hc : CographRadius.Cograph G) {k : ℕ} (hk : o = some k) :
    G.maxDegree ≤ k := by
  obtain ⟨ha,hr,he,hi,hd,hs,ho⟩ := cograph_tree_profile G hn ht hc
  have hK := Option.some.inj (hk.symm.trans ho)
  omega

theorem row1644 (hn : 2 ≤ n) (ht : G.IsTree) (hc : CographRadius.Cograph G) {k : ℕ} (hk : o = some k) :
    k ≤ G.maxDegree := by
  obtain ⟨ha,hr,he,hi,hd,hs,ho⟩ := cograph_tree_profile G hn ht hc
  have hK := Option.some.inj (hk.symm.trans ho)
  omega

#print axioms cograph_tree_profile
#print axioms row1173
#print axioms row1178
#print axioms row1181
#print axioms row1212
#print axioms row1215
#print axioms row1227
#print axioms row1229
#print axioms row1257
#print axioms row1272
#print axioms row1314
#print axioms row1316
#print axioms row1415
#print axioms row1416
#print axioms row1638
#print axioms row1640
#print axioms row1643
#print axioms row1644
end CographTree
