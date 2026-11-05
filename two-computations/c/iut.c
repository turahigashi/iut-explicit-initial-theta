/* iut.c -- the same inequality computed along IUT.
 *
 * Corollary 3.12 of IUT III compares the log-volume of the q-pilot with that of the holomorphic hull of the union of
 * the possible images of the Theta-pilot; IUT IV, Theorem 1.10, proof, Steps (iv)-(vii), bounds the latter from
 * above:
 *
 *     -|log qq|  <=  -|log Theta|  <=  U(D),       that is   (k - 1) |log qq|  <=  C = U(D) + k |log qq|.
 *
 * The middle term is computed in the reading of IUT IV: the theta value of the label j sits on the factor j of the
 * tensor packet (i-dagger = j); container = the tensor product of the log-shells; (Ind2) = units; hull; the small
 * archimedean container pi^(j+1) B_I. Then Step (viii) and the form of Theorem 1.10.
 * The places above 2, 3, 5 and l are not computed: in the hull their contribution is >= 0 and is set to 0, and in the
 * upper bound they are bounded by Step (ii) and (R4), as in IUT IV.
 *
 * usage: iut <datum file>
 */
#include "localdata.h"

typedef struct {        /* a place of F with the structure that IUT attaches to it */
    double w;           /* weight [F_v : Q_p] / [F : Q]; the weights above p add up to 1 */
    int bad;            /* in V^bad */
    long long eK;       /* ramification index of K_v / Q_p, K = F(E[l]), F = F_mod(i, E[15]); 0 if not known */
    double rq;          /* ord_p of qq = q^(1/2l) at v, with ord_p(p) = 1 (0 outside V^bad) */
    double rho;         /* outer radius of the log-shell (1/2p) log(O_v^x), in units of log p */
    double dif;         /* order of the different of K_v / Q_p (tame): (e - 1)/e */
} Loc;

static long long gcd(long long a, long long b) { while (b) { long long t = a % b; a = b; b = t; } return a; }

/* rho = 1 + [p = 2] - m/e,  m = min over s >= 0 of p^s - s e */
static double log_shell_radius(long long p, long long e)
{
    double m = 1, ps = p;
    for (int s = 1; ps <= (double)(s * e + e) || ps - s * e < m; s++, ps *= p)
        if (ps - s * e < m) m = ps - s * e;
    return 1 + (p == 2) - m / e;
}

#define MAXP 8          /* places of F above one prime */

int main(int argc, char **argv)
{
    if (argc != 2) { fprintf(stderr, "usage: iut <datum file>\n"); return 2; }
    Datum d = read_datum(argv[1]);
    const int l = d.ell, ls = (l - 1) / 2;
    const double k = l * (l + 1) / 12.0;                    /* the average of j^2 over the labels j = 1, ..., l* */
    const double estar = 4096.0 * 27 * 5 * 2, lmod = log(estar * l), eta = 2, dmod = 2;
    Loc L[MAXPLACES];

    /* 1. The structure that IUT attaches to each place: weight, V^bad, the ramification of K, the theta-normalized
     *    order of q, the log-shell and the different. */
    for (int i = 0; i < d.n; i++) {
        const Place *v = &d.v[i];
        long long p = v->small;
        int small = p == 2 || p == 3 || p == 5 || p == l;
        L[i].w = v->f * v->eF / dmod;
        L[i].bad = v->ordq > 0 && !small && v->ordq % l != 0;
        L[i].eK = small ? 0 : v->ordq == 0 ? v->eF : v->eF * 15LL * l / gcd(15LL * l, v->ordq);
        L[i].rq = L[i].bad ? (double)v->ordq / (2.0 * l * v->eF) : 0;
        L[i].rho = !L[i].eK ? 0 : p > 0 ? log_shell_radius(p, L[i].eK) : 1 - 1.0 / L[i].eK;   /* p > e + 1: m = 1 */
        L[i].dif = L[i].eK ? (L[i].eK - 1.0) / L[i].eK : 0;
        if (L[i].eK > 1 && p > 0 && p % L[i].eK == 0) { fprintf(stderr, "wild ramification is not handled\n"); return 1; }
    }

    /* 2. The q-pilot: |log qq| = sum over V^bad of w ord_p(qq) log p. */
    double a = 0, log_fF = 0, log_dF = log_disc_F(d.D);
    for (int i = 0; i < d.n; i++)
        if (L[i].bad) { a += L[i].w * L[i].rq * d.v[i].logp; log_fF += L[i].w / d.v[i].eF * d.v[i].logp; }

    /* 3. The primes that carry theta values (a place in V^bad), one at a time. For each label j and each tuple
     *    T = (t_0, ..., t_j) of places above p (one for each factor of the tensor packet, weight w(t_0)...w(t_j)):
     *      Theta-side: the hull of the container, with the theta value on the factor j:
     *                  sum_i rho(t_i) - j^2 rq(t_j)                                                  [units of log p]
     *      IV:         Proposition 1.4 (iii) with lambda = j^2 rq(t_j):
     *                  (-lambda + sum_i dif(t_i) + 1) log p + sum over i with e(t_i) > p - 2 of (3 + log e(t_i))
     *    Average over the tuples (weighted) and over the labels (procession normalization). */
    double theta_sum = 0, iv_sum = 0, closed_sum = 0, logd_known = 0;
    int done[MAXPLACES] = {0}, enumerated = 1;
    for (int i0 = 0; i0 < d.n; i0++) {
        if (done[i0] || !L[i0].bad) continue;
        int idx[MAXP], m = 0;
        for (int i = 0; i < d.n; i++)
            if (same_prime(&d.v[i], &d.v[i0])) { idx[m++] = i; done[i] = 1; }
        const double logp = d.v[i0].logp;
        const long long p = d.v[i0].small;
        double theta_p = 0, iv_p = 0, wsum = 0;
        for (int j = 1; j <= ls; j++) {
            double th = 0, iv = 0;
            if (pow(m, j + 1) <= (1 << 22)) {                    /* all m^(j+1) tuples */
                int t[128] = {0};
                for (;;) {
                    double wt = 1, rho = 0, dif = 0, star = 0;
                    for (int i = 0; i <= j; i++) {
                        const Loc *u = &L[idx[t[i]]];
                        wt *= u->w; rho += u->rho; dif += u->dif;
                        if (p > 0 && u->eK > p - 2) star += 3 + log((double)u->eK);
                    }
                    double lambda = (double)j * j * L[idx[t[j]]].rq;   /* the theta value sits on the factor j */
                    th += wt * (rho - lambda);
                    iv += wt * ((-lambda + dif + 1) * logp + star);
                    int i = 0;                                   /* next tuple */
                    while (i <= j && ++t[i] == m) t[i++] = 0;
                    if (i > j) break;
                }
            } else {                                             /* the same average, by linearity */
                double rbar = 0, dbar = 0, sbar = 0, qbar = 0;
                enumerated = 0;
                for (int s = 0; s < m; s++) {
                    const Loc *u = &L[idx[s]];
                    rbar += u->w * u->rho; dbar += u->w * u->dif; qbar += u->w * u->rq;
                    if (p > 0 && u->eK > p - 2) sbar += u->w * (3 + log((double)u->eK));
                }
                th = (j + 1) * rbar - (double)j * j * qbar;
                iv = (-(double)j * j * qbar + (j + 1) * dbar + 1) * logp + (j + 1) * sbar;
            }
            theta_p += th * logp / ls;
            iv_p += iv / ls;
        }
        /* the same prime in closed form: (l+5)/4 (log d_p + sum_{I*} w (3 + log e)) - (l+1)/24 log q_p + log p */
        double logd_p = 0, star_p = 0, logq_p = 0;
        for (int s = 0; s < m; s++) {
            const Loc *u = &L[idx[s]];
            wsum += u->w;
            logd_p += u->w * u->dif * logp;
            logq_p += u->w * 2 * l * u->rq * logp;
            if (p > 0 && u->eK > p - 2) star_p += u->w * (3 + log((double)u->eK));
        }
        if (fabs(wsum - 1) > 1e-12) { fprintf(stderr, "weights above %s do not add up to 1\n", d.v[i0].p); return 1; }
        closed_sum += (l + 5) / 4.0 * (logd_p + star_p) - (l + 1) / 24.0 * logq_p + logp;
        logd_known += logd_p;
        theta_sum += theta_p;
        iv_sum += iv_p;
    }

    for (int i = 0; i < d.n; i++)                                    /* every other prime must be 2, 3, 5 or l */
        if (!done[i] && L[i].eK) printf("note: the prime %s has no place in V^bad and is not counted\n", d.v[i].p);

    /* 4. The primes 2, 3, 5 and l: Step (ii) bounds the different of K by those of F and the conductor; (R4) replaces
     *    the terms of I* by 4 (j+1) l*_mod. */
    long long sp[4] = {2, 3, 5, l};
    int nsp = 0, s_le = 0;
    double U_rest = 0, logd_rest = log_dF + log_fF + 2 * log(l) + 21 - logd_known;
    if (logd_rest < 0) logd_rest = 0;
    U_rest = (l + 5) / 4.0 * logd_rest;
    for (int s = 0; s < 4; s++) {
        int dup = 0;
        for (int t = 0; t < s; t++) dup |= sp[t] == sp[s];
        if (dup) continue;
        nsp++;
        U_rest += log((double)sp[s]) + (l + 5) * lmod;               /* p <= e* l */
    }
    s_le = nsp;
    for (int i = 0; i < d.n; i++) {                                  /* primes of V^bad below e* l, once each */
        int first = 1;
        for (int t = 0; t < i; t++) first &= !(L[t].bad && same_prime(&d.v[t], &d.v[i]));
        if (L[i].bad && first && d.v[i].small > 0 && d.v[i].small <= estar * l) s_le++;
    }

    /* 5. The archimedean part: the container pi^(j+1) B_I, averaged over the labels: (l+5)/4 log pi. */
    const double arch = (l + 5) / 4.0 * log(acos(-1.0));

    const double M = theta_sum + arch, U = iv_sum + U_rest + arch, C = U + k * a;
    printf("datum %s  l = %d  k = %.10f%s\n", d.name, l, k, d.unfactored ? "  (a cofactor is not factored)" : "");
    printf("q-pilot      -|log qq|   = %.10f        (log q = 2 l |log qq| = %.10f)\n", -a, 2 * l * a);
    printf("Theta-pilot  -|log Theta| = %.10f       (reading of IUT IV; places above 2, 3, 5, l set to 0)\n", M);
    printf("IUT IV       U(D)         = %.10f       (primes with theta values %.10f, closed form %.10f; 2, 3, 5, l %.10f;"
           " archimedean %.10f)%s\n", U, iv_sum, closed_sum, U_rest, arch, enumerated ? "" : "  [long tuples by linearity]");
    printf("Corollary 3.12: %.10f %s %.10f      IV: %.10f %s %.10f\n", -a, -a <= M ? "<=" : ">", M, M, M <= U ? "<=" : ">", U);
    printf("height inequality (k-1)|log qq| = %.10f %s %.10f = C\n", (k - 1) * a, (k - 1) * a <= C ? "<=" : ">", C);

    /* 6. Step (viii) (the bound of C_Theta |log qq|) and the form of Theorem 1.10. */
    const double logq = 2 * l * a;
    const double viii = (l + 1) / 4.0 * ((1 + 12 * dmod / l) * (log_dF + log_fF) + 2 * log(l) + 56
                         - (1 - 12.0 / ((double)l * l)) * logq / 6 + 20.0 / 3 * lmod * s_le) - logq / (2 * l);
    const double rhs = (1 + 20 * dmod / l) * (log_dF + log_fF) + 20 * (estar * l + eta);
    printf("Step (viii): %.10f      Theorem 1.10: (1/6) log q = %.10f %s %.12e\n", viii, logq / 6, logq / 6 <= rhs ? "<=" : ">", rhs);
    return 0;
}
