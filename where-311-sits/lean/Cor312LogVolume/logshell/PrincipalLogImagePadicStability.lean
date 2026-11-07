import Cor312LogVolume.logshell.ClosedAddSubgroupPadicModule
import Cor312LogVolume.logshell.LocalLogShellCompactness

noncomputable section
set_option autoImplicit false

namespace CitedLV.PrincipalLogImagePadicStability

open Src.IUT3.Remark122 Src.IUT3.Proposition39iv
open CitedLV.LocalLogShellCompactness
open CitedLV.ClosedAddSubgroupPadicModule

variable (p : ℕ) [Fact p.Prime]
variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K]
  [CompleteSpace K] [IsUltrametricDist K] [ProperSpace K]

theorem logImage_padicInt_smul_mem {z : K}
    (hz : z ∈ logUnit '' (principalUnits : Set K)) (a : ℤ_[p]) :
    (a : ℚ_[p]) • z ∈ logUnit '' (principalUnits : Set K) :=
  padicInt_smul_mem (E := K) p (logImageAddSubgroup (K := K) p)
    (logImage_compact (K := K) p).isClosed hz a

theorem logImage_inv_natCast_mul_mem (n : ℕ) (hn : ¬p ∣ n) {z : K}
    (hz : z ∈ logUnit '' (principalUnits : Set K)) :
    (n : K)⁻¹ * z ∈ logUnit '' (principalUnits : Set K) :=
  inv_natCast_mul_mem p (logImageAddSubgroup p) (logImage_compact p).isClosed n hn hz

theorem logImage_natCast_mul_mem_iff (n : ℕ) (hn : ¬p ∣ n) (z : K) :
    (n : K) * z ∈ logUnit '' (principalUnits : Set K) ↔
      z ∈ logUnit '' (principalUnits : Set K) :=
  natCast_mul_mem_iff p (logImageAddSubgroup p) (logImage_compact p).isClosed n hn z

theorem logShell_padicInt_smul_mem {z : K}
    (hz : z ∈ logShell (K := K) p) (a : ℤ_[p]) :
    (a : ℚ_[p]) • z ∈ logShell (K := K) p :=
  padicInt_smul_mem (E := K) p (logShellAddSubgroup (K := K) p)
    (logShell_compact (K := K) p).isClosed hz a

theorem logShell_inv_natCast_mul_mem (n : ℕ) (hn : ¬p ∣ n) {z : K}
    (hz : z ∈ logShell (K := K) p) : (n : K)⁻¹ * z ∈ logShell (K := K) p :=
  inv_natCast_mul_mem p (logShellAddSubgroup p) (logShell_compact p).isClosed n hn hz

end CitedLV.PrincipalLogImagePadicStability
