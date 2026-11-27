import P5CliqueMixedPairKernel133

namespace Graffiti133P5CliqueArms.MixedPairCertificate
open SimpleGraph Graffiti133 Graffiti133Camby
set_option maxRecDepth 140000
set_option maxHeartbeats 20000000

def fivePairOmitModel2 : Model 17 := ⟨[(4,5),(4,6),(4,7),(4,8),(5,6),(5,7),(5,8),(5,15),(5,16),(6,7),(6,8),(6,13),(6,14),(7,8),(8,11),(8,12),(9,12),(9,14),(9,15),(9,16),(10,11),(10,12),(10,13),(10,14),(10,16),(11,14),(12,13),(12,14),(13,15),(13,16),(14,15)], ![41072,2448,66208,21824,1539,6149,9,24582,98314,20,24,34,40,129,136,257,260]⟩
def fivePairOmitRows2 : List (Row 17) := [⟨0,604020748,Sum.inr ![4,0,13,7,2,16,8,3,12]⟩,
⟨1073741824,0,Sum.inl ![3,8,15,14]⟩,
⟨536870912,0,Sum.inl ![2,7,13,16]⟩,
⟨67108864,0,Sum.inl ![0,5,12,13]⟩,
⟨33554432,0,Sum.inl ![1,7,14,11]⟩,
⟨16777216,0,Sum.inl ![3,8,16,10]⟩,
⟨142606336,0,Sum.inl ![3,10,14,12]⟩,
⟨4194304,0,Sum.inl ![0,4,10,13]⟩,
⟨270532608,71336137,Sum.inr ![2,5,12,10,4,1,8,15,13]⟩,
⟨136314880,0,Sum.inl ![3,10,12,14]⟩,
⟨10485760,0,Sum.inl ![3,12,10,14]⟩,
⟨1048576,0,Sum.inl ![1,4,10,11]⟩,
⟨134742016,237920,Sum.inr ![0,5,12,14,7,1,8,16,9]⟩,
⟨262144,0,Sum.inl ![0,4,9,15]⟩,
⟨131072,0,Sum.inl ![2,7,14,9]⟩,
⟨65536,0,Sum.inl ![2,5,12,9]⟩,
⟨0,17826067,Sum.inr ![6,3,10,4,1,11,5,2,16]⟩,
⟨268435456,273934,Sum.inr ![4,9,2,7,13,15,8,3,6]⟩,
⟨134250496,0,Sum.inl ![3,8,12,14]⟩,
⟨8421376,153100300,Sum.inr ![0,4,10,14,7,2,16,8,12]⟩,
⟨2129920,0,Sum.inl ![3,8,12,10]⟩,
⟨524288,139629,Sum.inr ![5,0,4,9,16,8,3,14,7]⟩,
⟨16384,33693708,Sum.inr ![0,4,9,2,7,14,3,8,11]⟩,
⟨49152,0,Sum.inl ![5,11,8,12]⟩,
⟨8192,0,Sum.inl ![2,7,8,16]⟩,
⟨1073745920,0,Sum.inl ![0,6,14,15]⟩,
⟨134221824,0,Sum.inl ![3,6,14,12]⟩,
⟨8392704,0,Sum.inl ![3,6,14,10]⟩,
⟨36864,134227470,Sum.inr ![4,0,6,14,7,2,16,8,12]⟩,
⟨2048,67174419,Sum.inr ![1,4,9,2,5,12,3,6,13]⟩,
⟨268437504,0,Sum.inl ![0,6,13,15]⟩,
⟨6144,0,Sum.inl ![6,13,7,14]⟩,
⟨1024,0,Sum.inl ![0,6,8,15]⟩,
⟨512,0,Sum.inl ![0,6,7,13]⟩,
⟨536871168,0,Sum.inl ![0,5,16,13]⟩,
⟨524544,0,Sum.inl ![2,5,16,9]⟩,
⟨33024,0,Sum.inl ![5,12,8,16]⟩,
⟨16640,0,Sum.inl ![5,11,8,16]⟩,
⟨268435584,0,Sum.inl ![0,5,15,13]⟩,
⟨32896,0,Sum.inl ![5,12,8,15]⟩,
⟨16512,0,Sum.inl ![5,11,8,15]⟩,
⟨384,0,Sum.inl ![5,15,8,16]⟩,
⟨64,0,Sum.inl ![0,5,8,15]⟩,
⟨32,0,Sum.inl ![0,5,7,13]⟩,
⟨16,0,Sum.inl ![3,6,5,12]⟩,
⟨8,0,Sum.inl ![0,4,8,15]⟩,
⟨4,0,Sum.inl ![0,4,7,13]⟩,
⟨2,0,Sum.inl ![3,6,4,10]⟩,
⟨1,0,Sum.inl ![1,4,5,11]⟩]
def fivePairOmitTree2 : Tree := .fork 15 (.fork 8 (.fork 3 (.fork 13 (.fork 0 (.fork 2 (.fork 1 (.fork 6 (.fork 11 (.fork 17 (.fork 27 (.fork 7 (.fork 26 (.fork 4 (.fork 5 (.fork 9 (.fork 10 (.fork 12 (.fork 18 (.fork 20 (.fork 21 (.fork 24 (.leaf 16) (.leaf 5)) (.fork 22 (.fork 24 (.leaf 16) (.leaf 5)) (.leaf 7))) (.leaf 11)) (.leaf 13)) (.fork 18 (.fork 20 (.fork 21 (.fork 24 (.leaf 16) (.leaf 5)) (.fork 22 (.fork 23 (.fork 24 (.leaf 16) (.leaf 5)) (.leaf 10)) (.leaf 7))) (.leaf 11)) (.leaf 13))) (.leaf 32)) (.leaf 33)) (.leaf 43)) (.leaf 44)) (.leaf 3)) (.fork 4 (.fork 5 (.fork 9 (.fork 10 (.fork 12 (.fork 14 (.fork 18 (.fork 20 (.fork 24 (.leaf 16) (.leaf 5)) (.leaf 11)) (.leaf 13)) (.leaf 40)) (.fork 14 (.fork 18 (.fork 20 (.fork 23 (.fork 24 (.leaf 16) (.leaf 5)) (.leaf 27)) (.leaf 11)) (.leaf 13)) (.leaf 40))) (.leaf 32)) (.leaf 33)) (.leaf 43)) (.leaf 44))) (.fork 5 (.fork 7 (.fork 12 (.fork 21 (.fork 4 (.fork 9 (.fork 10 (.fork 16 (.fork 18 (.fork 19 (.fork 20 (.fork 24 (.leaf 16) (.leaf 5)) (.leaf 11)) (.leaf 12)) (.leaf 13)) (.leaf 15)) (.leaf 32)) (.leaf 33)) (.leaf 44)) (.leaf 9)) (.leaf 26)) (.fork 12 (.fork 4 (.fork 9 (.fork 10 (.fork 14 (.fork 16 (.fork 18 (.fork 19 (.fork 20 (.fork 21 (.fork 24 (.leaf 16) (.leaf 5)) (.leaf 9)) (.leaf 11)) (.leaf 12)) (.leaf 13)) (.leaf 15)) (.leaf 40)) (.leaf 32)) (.leaf 33)) (.leaf 44)) (.leaf 26))) (.leaf 43))) (.leaf 14)) (.fork 12 (.fork 17 (.fork 26 (.fork 4 (.fork 5 (.fork 7 (.fork 16 (.leaf 29) (.leaf 15)) (.fork 16 (.leaf 29) (.leaf 15))) (.leaf 43)) (.leaf 44)) (.leaf 3)) (.leaf 14)) (.leaf 31))) (.leaf 42)) (.leaf 47)) (.leaf 46)) (.leaf 48)) (.leaf 24)) (.leaf 45)) (.fork 3 (.fork 2 (.fork 7 (.fork 11 (.fork 13 (.fork 12 (.fork 21 (.fork 29 (.fork 1 (.fork 9 (.fork 10 (.fork 14 (.fork 18 (.fork 26 (.leaf 0) (.leaf 3)) (.leaf 13)) (.leaf 37)) (.leaf 32)) (.leaf 33)) (.leaf 47)) (.leaf 2)) (.fork 26 (.fork 29 (.leaf 0) (.leaf 2)) (.leaf 3))) (.fork 21 (.fork 29 (.fork 1 (.fork 9 (.fork 10 (.fork 14 (.fork 18 (.fork 23 (.fork 26 (.leaf 0) (.leaf 3)) (.leaf 27)) (.leaf 13)) (.leaf 37)) (.leaf 32)) (.leaf 33)) (.leaf 47)) (.leaf 2)) (.fork 23 (.fork 26 (.fork 29 (.leaf 0) (.leaf 2)) (.leaf 3)) (.leaf 10)))) (.leaf 24)) (.fork 12 (.fork 26 (.fork 0 (.fork 13 (.fork 21 (.fork 29 (.leaf 0) (.leaf 2)) (.fork 29 (.leaf 0) (.leaf 2))) (.leaf 24)) (.leaf 48)) (.leaf 3)) (.leaf 31))) (.leaf 41)) (.leaf 46)) (.leaf 45))) (.fork 8 (.fork 2 (.fork 3 (.fork 13 (.fork 27 (.fork 1 (.fork 0 (.fork 11 (.fork 7 (.fork 9 (.fork 10 (.fork 12 (.fork 17 (.fork 21 (.fork 24 (.fork 4 (.fork 5 (.fork 6 (.fork 14 (.fork 18 (.fork 20 (.leaf 16) (.leaf 11)) (.leaf 13)) (.leaf 23)) (.leaf 42)) (.leaf 43)) (.leaf 44)) (.leaf 5)) (.leaf 20)) (.leaf 14)) (.leaf 28)) (.leaf 32)) (.leaf 33)) (.leaf 39)) (.fork 12 (.fork 4 (.fork 7 (.fork 17 (.fork 21 (.fork 24 (.fork 5 (.fork 6 (.fork 14 (.fork 16 (.fork 20 (.leaf 16) (.leaf 11)) (.leaf 15)) (.leaf 23)) (.leaf 42)) (.leaf 43)) (.leaf 5)) (.leaf 20)) (.leaf 14)) (.leaf 39)) (.leaf 44)) (.leaf 31))) (.leaf 48)) (.leaf 47)) (.leaf 18)) (.leaf 24)) (.leaf 45)) (.leaf 46)) (.leaf 36))

theorem five_pair_omit_2_forbidden {V : Type*} {G : SimpleGraph V}
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (m : Nat) (e : Fin 17→V) (eI : Function.Injective e)
    (fit : ∀ x y,G.Adj (e x) (e y)↔edge fivePairOmitModel2 m x y=true) : False := by
  apply actual_model_forbidden (by decide) h4 h9 fivePairOmitModel2 fivePairOmitRows2 fivePairOmitTree2 _ _ m e eI fit
  · decide
  · decide

#print axioms five_pair_omit_2_forbidden
end Graffiti133P5CliqueArms.MixedPairCertificate
