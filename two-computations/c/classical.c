/* classical.c -- the height inequality of IUT IV, Theorem 1.10, computed directly from the curve.
 *
 * Uses only the places of bad reduction, their residue degrees and the orders of q: no labels, no tensor packets,
 * no log-shells. The constants are copied from the statement of the theorem; nothing of its proof is used.
 *
 *     (1/6) log q  <=  (1 + 20 d/l) (log d + log f) + 20 (e* l + eta)
 *
 * log q, log f, log d: the normalized degrees of the q-parameter divisor, of the conductor (the same support with
 * coefficient 1) and of the discriminant of F;  d = [F:Q] = 2,  e* = 2^12 3^3 5 e  with e = 2,  eta = 2.
 *
 * usage: classical <datum file>
 */
#include "localdata.h"

/* the places counted for the comparison with IUT: V^bad of the catalogue minus the places above 3 and 5 */
static int counted(const Datum *d, const Place *v)
{
    long long p = v->small;
    return v->ordq > 0 && p != 2 && p != 3 && p != 5 && p != d->ell && v->ordq % d->ell != 0;
}

int main(int argc, char **argv)
{
    if (argc != 2) { fprintf(stderr, "usage: classical <datum file>\n"); return 2; }
    Datum d = read_datum(argv[1]);
    const double deg = 2;                              /* [F:Q] */
    const double estar = 4096.0 * 27 * 5 * 2, eta = 2;
    double log_q = 0, log_f = 0, log_q_all = 0, log_f_all = 0;
    double log_d = log_disc_F(d.D);

    for (int i = 0; i < d.n; i++) {
        const Place *v = &d.v[i];
        if (v->ordq == 0) continue;                    /* good reduction */
        log_q_all += v->f * v->ordq * v->logp / deg;   /* all places of bad reduction */
        log_f_all += v->f * v->logp / deg;
        if (!counted(&d, v)) continue;
        log_q += v->f * v->ordq * v->logp / deg;
        log_f += v->f * v->logp / deg;
    }
    double rhs = (1 + 20 * deg / d.ell) * (log_d + log_f) + 20 * (estar * d.ell + eta);

    printf("datum %s  l = %d%s\n", d.name, d.ell, d.unfactored ? "  (a cofactor is not factored)" : "");
    printf("all places of bad reduction: log q = %.10f  log f = %.10f\n", log_q_all, log_f_all);
    printf("counted places:              log q = %.10f  log f = %.10f  log d = %.10f\n", log_q, log_f, log_d);
    printf("Theorem 1.10: (1/6) log q = %.10f %s %.12e = right-hand side\n", log_q / 6, log_q / 6 <= rhs ? "<=" : ">", rhs);
    printf("Szpiro ratio log q / (log d + log f) = %.10f\n", log_q / (log_d + log_f));
    return 0;
}
