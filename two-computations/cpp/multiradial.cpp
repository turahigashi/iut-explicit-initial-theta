// multiradial.cpp -- the implemented part of the multiradial algorithm.
//
// This file includes common.hpp and multiradial.hpp only: it cannot name a theater, a field, a q-parameter or a
// valuation. Everything it computes comes from the etale-like data and the global data it is given.
#include "multiradial.hpp"
#include "decimal.hpp"
#include <cmath>
#include <stdexcept>

namespace iutm {

namespace {

u64 powmod(u64 a, u64 e)
{
    u64 r = 1;
    for (; e; e >>= 1, a = mulmod(a, a))
        if (e & 1) r = mulmod(r, a);
    return r;
}
u64 invmod(u64 a) { return powmod(a, LEVEL - 2); }   // N is prime

// (A) G^ab = Zhat x Z_p^d x (torsion): p is the prime with an extra Z_p-part, d is its rank, f is the exponent with
// p^f - 1 = the order of the torsion prime to p (local class field theory), and e = d / f.
// (B) the outer radius of the log-shell and the order of the different, from (p, e).
LocalInvariants local_invariants(const AbelianizationType& g)
{
    LocalInvariants L;
    if (!g.known) return L;
    L.known = true;
    L.p = g.extra_prime;
    L.logp = dec::log(L.p);
    L.small = dec::small(L.p);
    L.d = g.extra_rank;
    for (int f = 1; f <= L.d && !L.f; f++)
        if (dec::sub1(dec::pow(L.p, f)) == g.prime_to_p_torsion) L.f = f;
    if (!L.f || L.d % L.f) throw std::runtime_error("not the abelianized Galois group of a p-adic field: " + L.p);
    L.e = L.d / L.f;
    if (dec::mod_level(L.p) == 0 || dec::mod_level(g.prime_to_p_torsion) == 0)   // N must be prime to p (q_v - 1)
        throw std::runtime_error("the level N is not prime to p (q_v - 1) at " + L.p);
    if (L.small > 0 && L.e % L.small == 0) throw std::runtime_error("wild ramification is not handled");
    L.rho = L.small > 0 ? log_shell_radius(L.small, L.e) : 1 - 1.0 / L.e;   // p > e + 1: m = 1
    L.dif = (L.e - 1.0) / L.e;
    return L;
}

// (C) cyclotomic rigidity at level N. In the theta group the commutator pairing a |-> [t, a] identifies the
// cyclotome mu_N of the Z-covering with the central cyclotome Delta_Theta ([EtTh] Prop. 2.12; lana-agents/iut,
// Iut/EtaleTheta/Heisenberg.lean, cyclotomicRigidity_aut). The c-coordinate of [t, a_1] is the coordinate of the
// image of the generator a_1: the unit by which the theater's coordinates on Delta_Theta differ from those of mu_N.
u64 rigidity_unit(const ThetaGroupBox& G)
{
    const ThetaGroupElement t = G.generator_t(), a = G.generator_a();
    const ThetaGroupElement c = G.mul(G.mul(t, a), G.mul(G.inv(t), G.inv(a)));
    if (c.a != 0 || c.b != 0 || c.c == 0) throw std::runtime_error("the commutator is not a nonzero central element");
    return c.c;
}

}  // namespace

// rho = 1 + [p = 2] - m/e,  m = min over s >= 0 of p^s - s e   (the same loop as iut.c)
double log_shell_radius(long long p, long long e)
{
    double m = 1, ps = p;
    for (int s = 1; ps <= (double)(s * e + e) || ps - s * e < m; s++, ps *= p)
        if (ps - s * e < m) m = ps - s * e;
    return 1 + (p == 2) - m / e;
}

std::vector<std::vector<int>> places_by_prime(const AlgorithmInput& in)
{
    const int n = (int)in.places.size();
    std::vector<std::vector<int>> groups;
    std::vector<bool> done(n, false);
    for (int i0 = 0; i0 < n; i0++) {
        if (done[i0] || !in.places[i0].bad) continue;
        std::vector<int> idx;
        for (int i = 0; i < n; i++)
            if (in.global.prime_label[i] == in.global.prime_label[i0]) { idx.push_back(i); done[i] = true; }
        groups.push_back(idx);
    }
    return groups;
}

void for_each_tuple(int m, int j, const std::function<void(const std::vector<int>&)>& f)
{
    std::vector<int> t(j + 1, 0);
    for (;;) {
        f(t);
        int i = 0;                                   // the next tuple, t_0 fastest
        while (i <= j && ++t[i] == m) t[i++] = 0;
        if (i > j) break;
    }
}

Representation MultiradialAlgorithm::run(const AlgorithmInput& in) const
{
    Representation R;
    const int l = in.global.ell, ls = (l - 1) / 2;
    const int n = (int)in.places.size();
    R.ell = l;
    R.ell_star = ls;
    R.k = l * (l + 1) / 12.0;
    R.local.resize(n);
    R.theta_ord.assign(n, 0);
    R.rigidity.assign(n, 0);

    for (int i = 0; i < n; i++) R.local[i] = local_invariants(in.places[i].gab);   // (A)-(B)

    // (C)-(D) The theta values qq^(j^2) at the bad places, from their Kummer classes in Delta_Theta.
    for (int i = 0; i < n; i++) {
        const EtalePlace& P = in.places[i];
        if (!P.bad) continue;
        if (!R.local[i].known || !P.theta_group || (int)P.theta.size() != ls)
            throw std::runtime_error("incomplete etale-like data at " + P.name);
        const u64 g = use_rigidity_ ? rigidity_unit(*P.theta_group) : 1;
        const u64 ginv = invmod(g);
        R.rigidity[i] = g;
        std::vector<u64> val(ls);                    // ord_{K_v}(qq^(j^2)) mod N
        for (int j = 1; j <= ls; j++) val[j - 1] = mulmod(P.theta[j - 1].value, ginv);
        for (int j = 1; j <= ls; j++)
            if (val[j - 1] != mulmod(val[0], (u64)j * j)) R.gaussian_ok = false;
        R.theta_ord[i] = (double)val[0] / R.local[i].e;   // ord_p(qq) = ord_{K_v}(qq) / e; the valuations are << N
    }

    // (E)-(F) For each prime p with a bad place, each label j and each tuple t = (t_0, ..., t_j) of places above p
    // (one for each factor of the tensor packet, weight w(t_0)...w(t_j)): the hull of the container with the theta
    // value on the factor j (IUT IV's reading: (Ind2) = units, (Ind3) = the container),
    //     sum_i rho(t_i) - j^2 ord(qq_{t_j})                                                  [units of log p],
    // averaged over the tuples and over the labels (procession normalization, (Ind1)).
    for (const auto& idx : places_by_prime(in)) {
        PrimeImages P;
        const LocalInvariants& L0 = R.local[idx[0]];
        P.p = L0.p;
        P.logp = L0.logp;
        P.small = L0.small;
        P.places = idx;
        const int m = (int)idx.size();
        double wsum = 0, wrho = 0, logq_p = 0;
        for (int s : idx) {
            const double w = in.global.weight[s];
            wsum += w;
            wrho += w * R.local[s].rho;
            logq_p += w * 2 * l * R.theta_ord[s] * P.logp;
        }
        if (std::fabs(wsum - 1) > 1e-12) throw std::runtime_error("the weights above " + P.p + " do not add up to 1");
        for (int j = 1; j <= ls; j++) {
            double th = 0;
            if (std::pow(m, j + 1) <= TUPLE_LIMIT) {
                for_each_tuple(m, j, [&](const std::vector<int>& t) {
                    double wt = 1, rho = 0;
                    for (int i = 0; i <= j; i++) { wt *= in.global.weight[idx[t[i]]]; rho += R.local[idx[t[i]]].rho; }
                    th += wt * (rho - (double)j * j * R.theta_ord[idx[t[j]]]);   // the theta value on the factor j
                });
            } else {                                 // the same average, by linearity
                double rbar = 0, qbar = 0;
                P.by_linearity = true;
                for (int s : idx) { rbar += in.global.weight[s] * R.local[s].rho; qbar += in.global.weight[s] * R.theta_ord[s]; }
                th = (j + 1) * rbar - (double)j * j * qbar;
            }
            P.hull += th * P.logp / ls;
        }
        P.hull_closed = (l + 5) / 4.0 * wrho * P.logp - (l + 1) / 24.0 * logq_p;
        R.primes.push_back(P);
        R.minus_log_theta += P.hull;
    }

    // (G) The archimedean container pi^(j+1) B_I, averaged over the labels: (l+5)/4 log pi.
    R.arch = (l + 5) / 4.0 * std::log(std::acos(-1.0));
    R.minus_log_theta += R.arch;
    return R;
}

QPilot MultiradialAlgorithm::q_pilot(const QPilotInput& q, const AlgorithmInput& coric, const Representation& rep) const
{
    QPilot Q;
    const int n = (int)coric.places.size();
    Q.ord.assign(n, 0);
    double a = 0;
    for (int i = 0; i < n; i++) {
        if (!coric.places[i].bad) continue;
        Q.ord[i] = (double)q.q[i].value / rep.local[i].e;   // mu_N: the Kummer class is the valuation mod N
        a += coric.global.weight[i] * Q.ord[i] * rep.local[i].logp;
    }
    Q.minus_log_q = -a;
    return Q;
}

}  // namespace iutm
