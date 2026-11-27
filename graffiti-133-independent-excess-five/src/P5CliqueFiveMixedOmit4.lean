import P5CliqueMixedPairKernel133

namespace Graffiti133P5CliqueArms.MixedPairCertificate
open SimpleGraph Graffiti133 Graffiti133Camby
set_option maxRecDepth 140000
set_option maxHeartbeats 20000000

def fivePairOmitModel4 : Model 17 := ⟨[(4,5),(4,6),(4,7),(4,8),(5,6),(5,7),(5,8),(6,7),(6,8),(6,15),(6,16),(7,8),(7,13),(7,14),(8,11),(8,12),(9,12),(9,13),(9,14),(9,16),(10,11),(10,12),(10,14),(10,15),(10,16),(11,13),(11,14),(11,16),(12,13),(12,15),(12,16)], ![32880,10640,17056,70976,1539,6149,24585,98310,10,20,24,34,40,66,68,129,136]⟩
def fivePairOmitRows4 : List (Row 17) := [⟨0,201327635,Sum.inr ![4,1,11,5,2,14,6,3,16]⟩,
⟨536870912,0,Sum.inl ![0,5,12,15]⟩,
⟨268435456,0,Sum.inl ![3,6,13,12]⟩,
⟨134217728,0,Sum.inl ![1,7,16,11]⟩,
⟨67108864,0,Sum.inl ![2,5,11,14]⟩,
⟨1090519040,0,Sum.inl ![3,10,16,12]⟩,
⟨50331648,135271558,Sum.inr ![2,7,16,10,4,0,6,13,11]⟩,
⟨8388608,0,Sum.inl ![0,4,10,15]⟩,
⟨4194304,0,Sum.inl ![3,6,14,10]⟩,
⟨1075838976,0,Sum.inl ![3,10,12,16]⟩,
⟨18874368,0,Sum.inl ![3,12,10,16]⟩,
⟨1048576,0,Sum.inl ![1,4,10,11]⟩,
⟨524288,0,Sum.inl ![2,7,16,9]⟩,
⟨1074003968,599216,Sum.inr ![1,7,16,12,5,0,6,14,9]⟩,
⟨131072,0,Sum.inl ![1,4,9,13]⟩,
⟨65536,0,Sum.inl ![2,5,12,9]⟩,
⟨1073774592,0,Sum.inl ![3,8,12,16]⟩,
⟨268468224,0,Sum.inl ![1,8,12,13]⟩,
⟨2129920,0,Sum.inl ![3,8,12,10]⟩,
⟨16384,134744076,Sum.inr ![0,4,9,2,7,16,3,8,11]⟩,
⟨33570816,0,Sum.inl ![1,8,11,13]⟩,
⟨49152,0,Sum.inl ![5,11,8,12]⟩,
⟨67117056,0,Sum.inl ![1,7,14,11]⟩,
⟨270336,0,Sum.inl ![2,7,14,9]⟩,
⟨33558528,0,Sum.inl ![1,7,13,11]⟩,
⟨12288,0,Sum.inl ![6,13,7,14]⟩,
⟨2048,0,Sum.inl ![3,8,7,16]⟩,
⟨0,12593164,Sum.inr ![8,3,10,4,0,15,7,2,14]⟩,
⟨1073742848,0,Sum.inl ![3,6,16,12]⟩,
⟨33554432,147803,Sum.inr ![4,9,2,5,11,13,6,3,8]⟩,
⟨16778240,0,Sum.inl ![3,6,16,10]⟩,
⟨2098176,1094713363,Sum.inr ![1,4,10,12,5,2,14,6,16]⟩,
⟨262144,73911,Sum.inr ![5,12,3,6,14,9,4,1,7]⟩,
⟨33792,1073742171,Sum.inr ![4,1,8,12,5,2,14,6,16]⟩,
⟨9216,0,Sum.inl ![6,14,7,16]⟩,
⟨5120,0,Sum.inl ![6,13,7,16]⟩,
⟨512,536936467,Sum.inr ![1,4,9,2,5,12,3,6,15]⟩,
⟨8704,0,Sum.inl ![6,14,7,15]⟩,
⟨4608,0,Sum.inl ![6,13,7,15]⟩,
⟨1536,0,Sum.inl ![6,15,7,16]⟩,
⟨256,0,Sum.inl ![1,8,6,13]⟩,
⟨128,0,Sum.inl ![0,6,7,15]⟩,
⟨64,0,Sum.inl ![1,8,5,11]⟩,
⟨32,0,Sum.inl ![0,5,7,15]⟩,
⟨16,0,Sum.inl ![2,5,6,14]⟩,
⟨8,0,Sum.inl ![3,8,4,10]⟩,
⟨4,0,Sum.inl ![0,4,7,15]⟩,
⟨2,0,Sum.inl ![1,4,6,13]⟩,
⟨1,0,Sum.inl ![1,4,5,11]⟩]
def fivePairOmitTree4 : Tree := .fork 10 (.fork 13 (.fork 1 (.fork 4 (.fork 0 (.fork 2 (.fork 3 (.fork 7 (.fork 14 (.fork 16 (.fork 30 (.fork 12 (.fork 27 (.fork 5 (.fork 6 (.fork 8 (.fork 11 (.fork 15 (.fork 17 (.fork 20 (.fork 22 (.fork 23 (.leaf 27) (.leaf 7)) (.leaf 8)) (.leaf 11)) (.leaf 14)) (.fork 17 (.fork 20 (.fork 21 (.fork 22 (.fork 23 (.leaf 27) (.leaf 7)) (.leaf 8)) (.leaf 18)) (.leaf 11)) (.leaf 14))) (.leaf 26)) (.leaf 40)) (.leaf 42)) (.leaf 43)) (.leaf 3)) (.fork 5 (.fork 6 (.fork 8 (.fork 9 (.fork 11 (.fork 15 (.fork 17 (.fork 22 (.fork 23 (.leaf 27) (.leaf 7)) (.leaf 8)) (.leaf 14)) (.fork 17 (.fork 21 (.fork 22 (.fork 23 (.leaf 27) (.leaf 7)) (.leaf 8)) (.leaf 18)) (.leaf 14))) (.leaf 26)) (.leaf 38)) (.leaf 40)) (.leaf 42)) (.leaf 43))) (.fork 5 (.fork 12 (.fork 15 (.fork 24 (.fork 6 (.fork 8 (.fork 11 (.fork 17 (.fork 18 (.fork 22 (.fork 23 (.leaf 27) (.leaf 7)) (.leaf 8)) (.leaf 32)) (.leaf 14)) (.leaf 26)) (.leaf 40)) (.leaf 42)) (.leaf 5)) (.leaf 16)) (.fork 15 (.fork 6 (.fork 8 (.fork 9 (.fork 11 (.fork 17 (.fork 18 (.fork 21 (.fork 22 (.fork 23 (.leaf 27) (.leaf 7)) (.leaf 8)) (.leaf 9)) (.leaf 32)) (.leaf 14)) (.leaf 26)) (.leaf 38)) (.leaf 40)) (.leaf 42)) (.leaf 16))) (.leaf 43))) (.leaf 15)) (.fork 15 (.fork 16 (.fork 27 (.fork 5 (.fork 11 (.fork 12 (.fork 19 (.leaf 19) (.leaf 12)) (.fork 19 (.leaf 19) (.leaf 12))) (.leaf 26)) (.leaf 43)) (.leaf 3)) (.leaf 15)) (.leaf 21))) (.leaf 41)) (.leaf 45)) (.leaf 46)) (.leaf 48)) (.leaf 44)) (.leaf 47)) (.fork 1 (.fork 0 (.fork 4 (.fork 12 (.fork 14 (.fork 15 (.fork 24 (.fork 26 (.fork 3 (.fork 6 (.fork 8 (.fork 9 (.fork 17 (.fork 27 (.leaf 0) (.leaf 3)) (.leaf 14)) (.leaf 37)) (.leaf 40)) (.leaf 42)) (.leaf 45)) (.leaf 4)) (.fork 26 (.fork 27 (.leaf 0) (.leaf 3)) (.leaf 4))) (.fork 21 (.fork 26 (.fork 27 (.leaf 0) (.leaf 3)) (.leaf 4)) (.leaf 18))) (.fork 15 (.fork 27 (.fork 2 (.fork 24 (.fork 26 (.leaf 0) (.leaf 4)) (.fork 26 (.leaf 0) (.leaf 4))) (.leaf 46)) (.leaf 3)) (.leaf 21))) (.leaf 25)) (.leaf 44)) (.leaf 48)) (.leaf 47))) (.fork 13 (.fork 0 (.fork 1 (.fork 4 (.fork 30 (.fork 3 (.fork 2 (.fork 14 (.fork 6 (.fork 8 (.fork 9 (.fork 15 (.fork 22 (.fork 24 (.fork 5 (.fork 7 (.fork 11 (.fork 12 (.fork 16 (.fork 17 (.fork 23 (.leaf 27) (.leaf 7)) (.leaf 14)) (.leaf 15)) (.leaf 35)) (.leaf 26)) (.leaf 41)) (.leaf 43)) (.leaf 30)) (.leaf 8)) (.leaf 33)) (.leaf 39)) (.leaf 40)) (.leaf 42)) (.fork 15 (.fork 9 (.fork 11 (.fork 22 (.fork 24 (.fork 5 (.fork 7 (.fork 12 (.fork 16 (.fork 19 (.fork 23 (.leaf 27) (.leaf 7)) (.leaf 12)) (.leaf 15)) (.leaf 35)) (.leaf 41)) (.leaf 43)) (.leaf 30)) (.leaf 8)) (.leaf 26)) (.leaf 39)) (.leaf 21))) (.leaf 46)) (.leaf 45)) (.leaf 28)) (.leaf 44)) (.leaf 47)) (.leaf 48)) (.leaf 34))

theorem five_pair_omit_4_forbidden {V : Type*} {G : SimpleGraph V}
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (m : Nat) (e : Fin 17→V) (eI : Function.Injective e)
    (fit : ∀ x y,G.Adj (e x) (e y)↔edge fivePairOmitModel4 m x y=true) : False := by
  apply actual_model_forbidden (by decide) h4 h9 fivePairOmitModel4 fivePairOmitRows4 fivePairOmitTree4 _ _ m e eI fit
  · decide
  · decide

#print axioms five_pair_omit_4_forbidden
end Graffiti133P5CliqueArms.MixedPairCertificate
