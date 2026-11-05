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
