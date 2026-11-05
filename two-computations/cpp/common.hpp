// common.hpp -- everything that crosses from a Hodge theater to the multiradial algorithm.
//
// The algorithm (multiradial.cpp) includes this header and multiradial.hpp only. It never sees the class
// HodgeTheater, so it cannot read a local field, a q-parameter or a valuation: what it gets is listed here.
// The values in these structures are produced by oracle.cpp, by reverse computation from the theater's ring
// structure (the ORACLE notes below say from what): this mockup does not have the profinite groups that IUT
// starts from.
#pragma once
#include <cstdint>
#include <memory>
#include <string>
#include <vector>

namespace iutm {

using u64 = std::uint64_t;
using i64 = std::int64_t;

// The finite level of the Kummer classes: N = 2^61 - 1, a prime. The algorithm checks that it is prime to p(q_v - 1)
// at every place it uses. Then H^1(G_v, mu_N) = K_v^x / (K_v^x)^N is cyclic of order N and carries only the
// valuation mod N: the units of K_v are N-divisible.
constexpr u64 LEVEL = 2305843009213693951ULL;

// x mod N for x < 2^64, and a b mod N for a, b < N, in 64-bit arithmetic (2^61 = 1 mod N)
inline u64 reduce61(u64 x)
{
    x = (x >> 61) + (x & LEVEL);
    return x >= LEVEL ? x - LEVEL : x;
}
inline u64 mulmod(u64 a, u64 b)
{
    const u64 M31 = (1ULL << 31) - 1, M30 = (1ULL << 30) - 1;
    const u64 au = a >> 31, ad = a & M31, bu = b >> 31, bd = b & M31;
    const u64 mid = ad * bu + au * bd;
    return reduce61(2 * au * bu + (mid >> 30) + ((mid & M30) << 31) + ad * bd);
}

// ORACLE [gab]. The isomorphism type of G_{K_v}^ab as an abstract profinite group: G^ab = Zhat x Z_p^d x (torsion).
// In IUT it is read off the abstract group G_v. Here it is computed from the field by local class field theory
// (G^ab = the profinite completion of K_v^x): the prime p, d = [K_v : Q_p] and the order p^f - 1 of the torsion
// prime to p.
struct AbelianizationType {
    bool known = false;                // false above 2, 3, 5 and l: not computed, as in IUT IV
    std::string extra_prime;           // the prime with an extra Z_p-part, in decimal
    int extra_rank = 0;                // d, the rank of that extra part
    std::string prime_to_p_torsion;    // the order of the torsion prime to p, in decimal
};

// A Kummer class at level N: an element of H^1(G_v, Lambda) = Z/N, written in the coordinates of the cyclotome
// Lambda in which it was handed over.
struct KummerClass { u64 value = 0; };

// An element of the theta group at level N, in the coordinates of the theater that hands it over:
// c in the central cyclotome Delta_Theta, a in the cyclotome mu_N of the Z-covering, b in Z = Gal(Y/X).
struct ThetaGroupElement { u64 c = 0, a = 0; i64 b = 0; };

// ORACLE [theta-group]. The theta group at level N as a black box: the algorithm may multiply, invert and ask for the two
// generators, nothing else. It models the theta quotient of the tempered fundamental group of the Tate curve
// ([EtTh] Section 2; lana-agents/iut, Iut/EtaleTheta/Heisenberg.lean), whose commutator pairing identifies the two
// cyclotomes. Here the box is built from the theater's own choice of coordinates on Delta_Theta.
class ThetaGroupBox {
public:
    virtual ~ThetaGroupBox() = default;
    virtual ThetaGroupElement mul(const ThetaGroupElement& x, const ThetaGroupElement& y) const = 0;
    virtual ThetaGroupElement inv(const ThetaGroupElement& x) const = 0;
    virtual ThetaGroupElement generator_t() const = 0;   // the generator of the Z-part
    virtual ThetaGroupElement generator_a() const = 0;   // a generator of the mu_N-part
};

struct EtalePlace {                    // one place of the dagger theater, with everything the algorithm may read
    std::string name;
    AbelianizationType gab;            // ORACLE [gab]
    bool bad = false;                  // in V^bad: part of the initial Theta-datum
    std::vector<KummerClass> theta;    // ORACLE [kummer]: Kummer classes of the theta values qq^(j^2), j = 1, ..., l*,
                                       //            in the coordinates of Delta_Theta (bad places only)
    std::shared_ptr<const ThetaGroupBox> theta_group;   // ORACLE [theta-group] (bad places only)
};

struct GlobalData {                    // ORACLE [global]: in IUT from the copies of F_mod (the global Frobenioids)
    int ell = 0;                       // the prime l of the initial Theta-datum
    std::vector<std::string> prime_label;   // places with the same label lie above the same prime
    std::vector<double> weight;        // [F_v : Q_p] / [F : Q]
    double log_disc_F = 0;             // log d^F of F = F_mod (= F_tpd for the Legendre form)
    double log_cond_F = 0;             // log f^F over V^bad
};

struct AlgorithmInput {                // the dagger theater's etale-like data and the global data
    GlobalData global;
    std::vector<EtalePlace> places;
};

struct QPilotInput {                   // the ddagger theater's q-pilot
    std::vector<KummerClass> q;        // ORACLE [kummer]: Kummer classes of qq in mu_N (0 if the place is not bad)
};

}  // namespace iutm
