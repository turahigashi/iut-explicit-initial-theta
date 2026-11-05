// iv.cpp -- IUT IV's estimate (the same formulas as iut.c, steps 3-6).
#include "iv.hpp"
#include <cmath>

namespace iutm {

IVEstimate iv_estimate(const AlgorithmInput& coric, const Representation& rep, const QPilot& qp)
{
    IVEstimate E;
    const int l = rep.ell, ls = rep.ell_star;
    const double k = rep.k;
    const double estar = 4096.0 * 27 * 5 * 2, lmod = std::log(estar * l), eta = 2, dmod = 2;
    const GlobalData& G = coric.global;
    double logd_known = 0;

    // Proposition 1.4 (iii) with lambda = j^2 ord(qq_{t_j}) on the same tuples as the possible images:
    //     (-lambda + sum_i dif(t_i) + 1) log p + sum over i with e(t_i) > p - 2 of (3 + log e(t_i)),
    // averaged over the tuples and the labels; in closed form
    //     (l+5)/4 (log d_p + sum_{I*} w (3 + log e)) - (l+1)/24 log q_p + log p.
    for (const PrimeImages& P : rep.primes) {
        const int m = (int)P.places.size();
        const long long p = P.small;
        double iv_p = 0, logd_p = 0, star_p = 0, logq_p = 0;
        auto star = [&](int s) { const long long e = rep.local[s].e; return p > 0 && e > p - 2 ? 3 + std::log((double)e) : 0.0; };
        for (int j = 1; j <= ls; j++) {
            double iv = 0;
            if (std::pow(m, j + 1) <= TUPLE_LIMIT) {
                for_each_tuple(m, j, [&](const std::vector<int>& t) {
                    double wt = 1, dif = 0, st = 0;
                    for (int i = 0; i <= j; i++) {
                        const int s = P.places[t[i]];
                        wt *= G.weight[s];
                        dif += rep.local[s].dif;
                        st += star(s);
                    }
                    const double lambda = (double)j * j * rep.theta_ord[P.places[t[j]]];
                    iv += wt * ((-lambda + dif + 1) * P.logp + st);
                });
            } else {                                 // the same average, by linearity
                double dbar = 0, sbar = 0, qbar = 0;
                E.enumerated = false;
                for (int s : P.places) {
                    dbar += G.weight[s] * rep.local[s].dif;
                    qbar += G.weight[s] * rep.theta_ord[s];
                    sbar += G.weight[s] * star(s);
                }
                iv = (-(double)j * j * qbar + (j + 1) * dbar + 1) * P.logp + (j + 1) * sbar;
            }
            iv_p += iv / ls;
        }
        for (int s : P.places) {
            logd_p += G.weight[s] * rep.local[s].dif * P.logp;
            logq_p += G.weight[s] * 2 * l * rep.theta_ord[s] * P.logp;
            star_p += G.weight[s] * star(s);
        }
        E.iv_closed += (l + 5) / 4.0 * (logd_p + star_p) - (l + 1) / 24.0 * logq_p + P.logp;
        logd_known += logd_p;
        E.iv_primes += iv_p;
    }

    // every other prime must be 2, 3, 5 or l
    std::vector<bool> counted(coric.places.size(), false);
    for (const PrimeImages& P : rep.primes)
        for (int s : P.places) counted[s] = true;
    for (size_t i = 0; i < coric.places.size(); i++)
        if (!counted[i] && rep.local[i].known)
            E.notes.push_back("the prime " + rep.local[i].p + " has no place in V^bad and is not counted");

    // 2, 3, 5 and l: Step (ii) bounds the different of K by those of F and the conductor; (R4) replaces the terms of
    // I* by 4 (j+1) l*_mod.
    const long long sp[4] = {2, 3, 5, l};
    int nsp = 0;
    double logd_rest = G.log_disc_F + G.log_cond_F + 2 * std::log(l) + 21 - logd_known;
    if (logd_rest < 0) logd_rest = 0;
    E.U_rest = (l + 5) / 4.0 * logd_rest;
    for (int s = 0; s < 4; s++) {
        bool dup = false;
        for (int t = 0; t < s; t++) dup |= sp[t] == sp[s];
        if (dup) continue;
        nsp++;
        E.U_rest += std::log((double)sp[s]) + (l + 5) * lmod;   // p <= e* l
    }
    int s_le = nsp;                                              // primes of V^bad below e* l, once each
    for (size_t i = 0; i < coric.places.size(); i++) {
        bool first = true;
        for (size_t t = 0; t < i; t++) first &= !(coric.places[t].bad && G.prime_label[t] == G.prime_label[i]);
        if (coric.places[i].bad && first && rep.local[i].small > 0 && rep.local[i].small <= estar * l) s_le++;
    }

    E.arch = rep.arch;
    E.U = E.iv_primes + E.U_rest + E.arch;
    E.a = -qp.minus_log_q;
    E.wall = (k - 1) * E.a;
    E.C = E.U + k * E.a;

    // Step (viii) (the bound of C_Theta |log qq|) and the form of Theorem 1.10.
    const double logq = 2 * l * E.a;
    E.viii = (l + 1) / 4.0 * ((1 + 12 * dmod / l) * (G.log_disc_F + G.log_cond_F) + 2 * std::log(l) + 56
             - (1 - 12.0 / ((double)l * l)) * logq / 6 + 20.0 / 3 * lmod * s_le) - logq / (2 * l);
    E.thm_lhs = logq / 6;
    E.thm_rhs = (1 + 20 * dmod / l) * (G.log_disc_F + G.log_cond_F) + 20 * (estar * l + eta);
    return E;
}

}  // namespace iutm
