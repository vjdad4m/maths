import SixSingletonQ2Cert189
import SixSingletonQ2RootChunk00189
import SixSingletonQ2RootChunk01189
import SixSingletonQ2RootChunk02189
import SixSingletonQ2RootChunk03189
import SixSingletonQ2RootChunk04189
import SixSingletonQ2RootChunk05189
import SixSingletonQ2RootChunk06189
import SixSingletonQ2RootChunk07189
import SixSingletonQ2RootChunk08189
import SixSingletonQ2RootChunk09189
import SixSingletonQ2RootChunk10189
import SixSingletonQ2RootChunk11189
import SixSingletonQ2RootChunk12189
import SixSingletonQ2RootChunk13189
import SixSingletonQ2RootChunk14189
import SixSingletonQ2RootChunk15189
import SixSingletonQ2RootChunk16189
import SixSingletonQ2RootChunk17189
import SixSingletonQ2RootChunk18189
import SixSingletonQ2RootChunk19189
import SixSingletonQ2RootChunk20189
import SixSingletonQ2RootChunk21189
import SixSingletonQ2RootChunk22189
import SixSingletonQ2RootChunk23189
import SixSingletonQ2RootChunk24189
import SixSingletonQ2RootChunk25189
import SixSingletonQ2RootChunk26189
import SixSingletonQ2RootChunk27189
import SixSingletonQ2RootChunk28189
import SixSingletonQ2RootChunk29189
import SixSingletonQ2RootChunk30189
import SixSingletonQ2RootChunk31189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.Q2
open Sat SimpleGraph Graffiti189Ore PortCertificates
set_option maxRecDepth 32768
set_option maxHeartbeats 60000000

theorem traceable_of_data {G : SimpleGraph Vertex} [DecidableRel G.Adj] (M : Data G) : Traceable G := by
  by_contra no
  have p : (value G).satisfies_fmla (Fmla.and (Fmla.and (Fmla.and (Fmla.and (Fmla.and (chunk00) (chunk01)) (Fmla.and (chunk02) (chunk03))) (Fmla.and (Fmla.and (chunk04) (chunk05)) (Fmla.and (chunk06) (chunk07)))) (Fmla.and (Fmla.and (Fmla.and (chunk08) (chunk09)) (Fmla.and (chunk10) (chunk11))) (Fmla.and (Fmla.and (chunk12) (chunk13)) (Fmla.and (chunk14) (chunk15))))) (Fmla.and (Fmla.and (Fmla.and (Fmla.and (chunk16) (chunk17)) (Fmla.and (chunk18) (chunk19))) (Fmla.and (Fmla.and (chunk20) (chunk21)) (Fmla.and (chunk22) (chunk23)))) (Fmla.and (Fmla.and (Fmla.and (chunk24) (chunk25)) (Fmla.and (chunk26) (chunk27))) (Fmla.and (Fmla.and (chunk28) (chunk29)) (Fmla.and (chunk30) (chunk31)))))) :=
    AllLow.fmla_and _ _ _ (AllLow.fmla_and _ _ _ (AllLow.fmla_and _ _ _ (AllLow.fmla_and _ _ _ (AllLow.fmla_and _ _ _ (satisfies_chunk00 M) (satisfies_chunk01 M)) (AllLow.fmla_and _ _ _ (satisfies_chunk02 M) (satisfies_chunk03 M))) (AllLow.fmla_and _ _ _ (AllLow.fmla_and _ _ _ (satisfies_chunk04 M) (satisfies_chunk05 M)) (AllLow.fmla_and _ _ _ (satisfies_chunk06 M) (satisfies_chunk07 M)))) (AllLow.fmla_and _ _ _ (AllLow.fmla_and _ _ _ (AllLow.fmla_and _ _ _ (satisfies_chunk08 M) (satisfies_chunk09 M)) (AllLow.fmla_and _ _ _ (satisfies_chunk10 M) (satisfies_chunk11 M))) (AllLow.fmla_and _ _ _ (AllLow.fmla_and _ _ _ (satisfies_chunk12 M) (satisfies_chunk13 M)) (AllLow.fmla_and _ _ _ (satisfies_chunk14 M) (satisfies_chunk15 M))))) (AllLow.fmla_and _ _ _ (AllLow.fmla_and _ _ _ (AllLow.fmla_and _ _ _ (AllLow.fmla_and _ _ _ (satisfies_chunk16 M) (satisfies_chunk17 M)) (AllLow.fmla_and _ _ _ (satisfies_chunk18 M) (satisfies_chunk19 M))) (AllLow.fmla_and _ _ _ (AllLow.fmla_and _ _ _ (satisfies_chunk20 M) (satisfies_chunk21 M)) (AllLow.fmla_and _ _ _ (satisfies_chunk22 M) (satisfies_chunk23 M)))) (AllLow.fmla_and _ _ _ (AllLow.fmla_and _ _ _ (AllLow.fmla_and _ _ _ (satisfies_chunk24 M) (satisfies_chunk25 M)) (AllLow.fmla_and _ _ _ (satisfies_chunk26 M) (satisfies_chunk27 M))) (AllLow.fmla_and _ _ _ (AllLow.fmla_and _ _ _ (satisfies_chunk28 M) (satisfies_chunk29 M)) (AllLow.fmla_and _ _ _ (satisfies_chunk30 M) (satisfies_chunk31 M no)))))
  exact exclusion (value G) p

#print axioms traceable_of_data
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.Q2
