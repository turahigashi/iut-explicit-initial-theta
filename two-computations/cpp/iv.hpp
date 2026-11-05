// iv.hpp -- IUT IV, Theorem 1.10, proof: the upper bound U(D) for -|log Theta| (Steps (iv)-(vii)), Step (viii) and
// the form of the theorem. This is IV's estimate of the output of the algorithm, not part of the algorithm.
#pragma once
#include "multiradial.hpp"

namespace iutm {

struct IVEstimate {
    double iv_primes = 0;   // the primes with theta values (Proposition 1.4 (iii), averaged)
    double iv_closed = 0;   // the same in closed form
    double U_rest = 0;      // 2, 3, 5 and l: Step (ii) and (R4)
    double arch = 0;        // the archimedean part
    double U = 0;           // U(D) = iv_primes + U_rest + arch
    double a = 0;           // |log qq|
    double wall = 0;        // (k - 1) a
    double C = 0;           // U(D) + k a
    double viii = 0;        // Step (viii)
    double thm_lhs = 0, thm_rhs = 0;   // Theorem 1.10: (1/6) log q <= rhs
    bool enumerated = true;
    std::vector<std::string> notes;
};

IVEstimate iv_estimate(const AlgorithmInput& coric, const Representation& rep, const QPilot& qp);

}  // namespace iutm
