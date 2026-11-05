// classical.hpp -- the height inequality of IUT IV, Theorem 1.10, computed directly from the curve (as classical.c):
// the places of bad reduction, their residue degrees and the orders of q. No labels, no tensor packets, no log-shells.
#pragma once
#include "datum.hpp"

namespace iutm {

struct Classical {
    double log_q_all = 0, log_f_all = 0;   // all places of bad reduction
    double log_q = 0, log_f = 0, log_d = 0; // the places counted for the comparison with IUT
    double rhs = 0;                         // (1 + 20 d/l)(log d + log f) + 20 (e* l + eta)
};

inline Classical classical(const Datum& d)
{
    Classical c;
    const double deg = 2, estar = 4096.0 * 27 * 5 * 2, eta = 2;   // [F:Q], e* = 2^12 3^3 5 e with e = 2
    c.log_d = log_disc_F(d.D);
    for (const Place& v : d.v) {
        if (v.ordq == 0) continue;                                 // good reduction
        c.log_q_all += v.f * v.ordq * v.logp / deg;
        c.log_f_all += v.f * v.logp / deg;
        const long long p = v.small;                              // V^bad of the catalogue minus the places above 3, 5
        if (p == 2 || p == 3 || p == 5 || p == d.ell || v.ordq % d.ell == 0) continue;
        c.log_q += v.f * v.ordq * v.logp / deg;
        c.log_f += v.f * v.logp / deg;
    }
    c.rhs = (1 + 20 * deg / d.ell) * (c.log_d + c.log_f) + 20 * (estar * d.ell + eta);
    return c;
}

}  // namespace iutm
