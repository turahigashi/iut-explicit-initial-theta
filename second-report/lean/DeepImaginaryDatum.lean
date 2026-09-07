/-!
Exact arithmetic for L=Q(i), pi=10+3i, a=pi^100, ell=31.
Uses the unchanged IMQ.GI integer model in ImaginaryQuadraticDatum.lean.
Concatenate that file first (the full audit supplies the dependency).

The 31-power sieve itself is external. We kernel-check its EXACT bound.
The full norm is NOT seventh-power-free: v2=7, a counterexample below.
The height bounds are directed-rounding certificates in height_audit.py;
this file checks the integer consequences, not transcendental logarithms.
The geometric/number-field interpretation is source-based in datum-proof.md.
There is no assertion of an actual blur or of membership outside Exc_d.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace IMQDeep
open IMQ.GI
abbrev GI := IMQ.GI
def ell : Nat := 31
def NN : Nat := 100
def pi : GI := ⟨10, 3⟩
def a : GI := pw pi NN
def oma : GI := sub one a
def ab : GI := conj a
def am1 : GI := sub a one
def B : Nat := 552904079182587925544083239345463235688361412279973706362632978753327883959485143836167203756966788138316011412609681125016475037186637862888570854434659209800182963205386889166725176972197328279578000000

theorem ell_prime : IMQ.isPrimeB ell = true := by decide
theorem ell_ge_five : 5 ≤ ell := by decide
theorem norm_a : nrm a = 109^100 := by decide
theorem norm_oma : nrm oma = (B : Int) := by decide
theorem smooth : a ≠ ⟨0,0⟩ ∧ a ≠ one := by decide
/-- Cleared-denominator Legendre orbit tests, implying nonrational j in the
quadratic interpretation. They are not a library theorem about number fields. -/
theorem orbit_exclusion :
    ab ≠ a ∧ mul ab a ≠ one ∧ ab ≠ oma ∧
    mul ab oma ≠ one ∧ mul ab am1 ≠ a ∧ mul ab a ≠ am1 := by decide

def t : GI := add (sub (mul a a) a) one
def jNum : GI := mul ⟨256,0⟩ (mul (mul t t) t)
def jDen : GI := mul (mul a a) (mul oma oma)
theorem j_den_nonzero : jDen ≠ ⟨0,0⟩ := by decide
theorem j_nonreal : (mul jNum (conj jDen)).im ≠ 0 := by decide

theorem split_roots : (33*33+1)%109 = 0 ∧ (76*76+1)%109 = 0 := by decide
theorem residues_pi : (10+3*33)%109 = 0 ∧ (10+3*76)%109 = 20 := by decide
theorem conjugate_place_good : 20^100%109 = 81 := by decide
theorem thirty_one_good : B%31 = 2 ∧ (109^100)%31 ≠ 0 := by decide
theorem seven_power_counterexample : B%128 = 0 ∧ B%256 ≠ 0 := by decide
/-- Verified BEFORE the exhaustive external sieve of 265766 primes. -/
theorem sieve_root31 : (3735455:Nat)^31 ≤ B ∧ B < (3735456:Nat)^31 := by decide
/-- Exact seventh root too; no search is claimed at this enormous bound. -/
theorem sieve_root7 : (127671166876556913248840051207:Nat)^7 ≤ B ∧ B < (127671166876556913248840051208:Nat)^7 := by decide
/-- The old sieve's fixed 10^8 cap cannot bound a seventh-power search here. -/
theorem old_seven_cap_insufficient : (100000000:Nat)^7 < B := by decide

theorem order_at_pi : 2*NN = 200 := by decide
theorem order_prime_to_ell : 200%ell ≠ 0 := by decide
theorem degree_prime_to_ell : Nat.gcd 23040 ell = 1 := by decide
/-- Once the external norm sieve has given 1<=v<31, all possible ideal orders
2v are prime to 31. Ramification from F/L is separately prime to 31. -/
theorem remaining_orders :
    (List.range 31).all (fun v => v == 0 || (2*v)%31 != 0) = true := by decide
theorem torsion_order : 15*ell = 465 := by decide
theorem torsion_gcd : Nat.gcd 465 200 = 5 := by decide
theorem field_ramification : 15 / Nat.gcd 15 200 = 3 := by decide
theorem full_ramification : 465 / Nat.gcd 465 200 = 93 := by decide
theorem small_ramification : 93 ≤ 109-2 := by decide
theorem entrance_positive : 6*ell < 2*NN := by decide
theorem margin_numerator : (NN : Int)-3*(ell:Int) = 7 := by decide

/-! A genuine good Frobenius over Q(i), at i=4 in F17. -/
def residueA : Nat := 22^100%17
def quadraticSymbol (x : Nat) : Int :=
  if x%17 == 0 then 0 else if (x%17)^8%17 == 1 then 1 else -1
def rhs (x : Nat) : Nat := (x*((x+16)%17)*((x+17-residueA)%17))%17
def trace17 : Int := -((List.range 17).map (fun x => quadraticSymbol (rhs x))).sum
theorem frobenius_place : (4*4+1)%17 = 0 ∧ residueA = 13 := by decide
theorem frobenius_trace : trace17 = 2 := by decide
theorem frobenius_discriminant : ((2:Int)^2-4*17)%31 = 29 := by decide
theorem irreducible_discriminant :
    (List.range 31).all (fun x => x*x%31 != 29) = true := by decide

/-! Complete candidate set. Given 933 < Hq < 934, the integral square cutoff
below is equivalent to Hq <= ell^2. C1's upper bound exceeds 10*delta here. -/
def candidate (l : Nat) : Bool :=
  IMQ.isPrimeB l && 5 ≤ l && 934 ≤ l*l && 6*l < 200
theorem candidates_exact : (List.range 34).filter candidate = [31] := by decide
theorem larger_candidates_fail (l : Nat) (h : 34 ≤ l) : ¬6*l < 200 := by omega
/-- Necessary-region obstruction only: if ell>=31 and e=15ell, neither base
prime in the two families has the required small ramification. -/
theorem coprime_branch_empty (l : Nat) (hl : 31 ≤ l) :
    ¬(15*l ≤ 107) ∧ ¬(15*l ≤ 209) := by
  have lower : 465 ≤ 15*l := Nat.mul_le_mul_left 15 hl
  exact ⟨fun h => (by decide : ¬(465 ≤ 107)) (Nat.le_trans lower h),
         fun h => (by decide : ¬(465 ≤ 209)) (Nat.le_trans lower h)⟩
theorem actual_fraction_margin :
    IMQEntrance.SameValue
      (IMQEntrance.margin 1 (IMQEntrance.depth 31 200 (by decide)))
      ⟨7,31,by decide⟩ := by decide
theorem actual_fraction_entrance :
    IMQEntrance.Positive
      (IMQEntrance.margin 1 (IMQEntrance.depth 31 200 (by decide))) := by decide
/-- Replacing Hq by full Weil height would falsely discard this witness.
This is a counterfactual integer filter, not the condition in IUT IV. -/
theorem full_weil_proxy_empty :
    (List.range 34).filter (fun l => IMQ.isPrimeB l &&
      5 ≤ l && 1408 ≤ l*l && 6*l < 200) = [] := by decide
end IMQDeep
