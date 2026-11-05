// multiradial.hpp -- the part of the multiradial algorithm (IUT III, Theorem 3.11) that this mockup implements.
//
// Input: the etale-like data of the dagger theater and the global data (common.hpp). Output: what the algorithm
// says about the Theta-pilot in one reading, IUT IV's: the log-volume of the hull of the union of the possible
// images, procession-normalized. The steps that are implemented here:
//   (A) the local invariants p, d, f, e from the abstract group G_{K_v}^ab;
//   (B) the log-shell radius and the different from (p, e) (IUT IV, Propositions 1.1 and 1.2);
//   (C) cyclotomic rigidity at level N: the coordinates of Delta_Theta from the commutator in the theta group;
//   (D) the theta values from their Kummer classes, with a check of the j^2-structure;
//   (E) the procession: labels j = 1, ..., l* and the tuples of places of the tensor packets;
//   (F) the possible images and their hull, (Ind1) = average over the labels, (Ind2) = units, (Ind3) = container;
//   (G) the archimedean container.
// What is not implemented is in oracle.hpp.
#pragma once
#include "common.hpp"
#include <functional>

namespace iutm {

struct LocalInvariants {        // (A)-(B), from G_{K_v}^ab alone
    bool known = false;
    std::string p;
    double logp = 0;
    long long small = -1;       // p if it fits in 18 digits, else -1
    int d = 0, f = 0;
    long long e = 0;
    double rho = 0;             // outer radius of the log-shell (1/2p) log(O_v^x), in units of log p
    double dif = 0;             // order of the different (tame): (e - 1)/e
};

struct PrimeImages {            // the possible images of the Theta-pilot at the places above one prime
    std::string p;
    double logp = 0;
    long long small = -1;
    std::vector<int> places;    // indices into AlgorithmInput::places
    double hull = 0;            // log-volume of the hull, averaged over the tuples and the labels
    double hull_closed = 0;     // the same in closed form
    bool by_linearity = false;  // the long tuples were averaged by linearity
};

struct Representation {         // the output (one reading: IUT IV's)
    int ell = 0, ell_star = 0;
    double k = 0;               // the average of j^2 over the labels j = 1, ..., l*
    std::vector<LocalInvariants> local;
    std::vector<double> theta_ord;   // ord_p(qq) at the bad places, recovered from the theta values (0 elsewhere)
    std::vector<u64> rigidity;       // the coordinate unit of Delta_Theta recovered at the bad places (0 elsewhere)
    bool gaussian_ok = true;         // the theta classes satisfy kappa(theta_j) = j^2 kappa(theta_1)
    std::vector<PrimeImages> primes;
    double arch = 0;                 // the archimedean container pi^(j+1) B_I, averaged over the labels
    double minus_log_theta = 0;      // -|log Theta|
    std::vector<std::string> notes;
};

struct QPilot {                 // the ddagger theater's q-pilot, read in the same coric frame
    std::vector<double> ord;    // ord_p(qq) at the bad places
    double minus_log_q = 0;     // -|log qq|
};

class MultiradialAlgorithm {
public:
    // use_rigidity = false skips step (C) and reads the theta classes as if Delta_Theta had the coordinates of mu_N
    explicit MultiradialAlgorithm(bool use_rigidity = true) : use_rigidity_(use_rigidity) {}
    Representation run(const AlgorithmInput& in) const;
    QPilot q_pilot(const QPilotInput& q, const AlgorithmInput& coric, const Representation& rep) const;

private:
    bool use_rigidity_;
};

// shared with the IV estimate
double log_shell_radius(long long p, long long e);
std::vector<std::vector<int>> places_by_prime(const AlgorithmInput& in);   // the bad primes, with all their places
void for_each_tuple(int m, int j, const std::function<void(const std::vector<int>&)>& f);   // all m^(j+1) tuples
constexpr double TUPLE_LIMIT = 1 << 22;

}  // namespace iutm
