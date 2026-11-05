// main.cpp -- a MOCKUP of the multiradial algorithm of IUT III, Theorem 3.11, on explicit initial Theta-data.
//
// usage: mockup <datum file>                 the two computations of the height inequality, side by side
//        mockup --selftest <datum file>      non-interference: the output does not depend on the theaters' choices
//        mockup --scan <datum file> <Nmax>   the family q -> q^N: where the reverse-computed Step (xi) stops
#include "classical.hpp"
#include "iv.hpp"
#include "link.hpp"
#include <cstdio>
#include <cstring>
#include <exception>

using namespace iutm;

namespace {

const u64 SEED_DAGGER = 20261105, SEED_DDAGGER = 31211105;

struct Run {
    Representation rep;
    QPilot qp;
    IVEstimate iv;
    StepXiCertificate xi;
    int coric = 0;
};

Run run_iut(const Datum& d, u64 seed_dagger, u64 seed_ddagger, bool rigidity = true)
{
    HodgeTheater dagger(d, seed_dagger), ddagger(d, seed_ddagger);
    ThetaLink link(dagger, ddagger);
    MultiradialAlgorithm alg(rigidity);
    Run r;
    r.coric = link.coric_places();
    r.rep = alg.run(link.algorithm_input());                    // (A)-(G)
    upper_semicompatibility();                                  // ORACLE [ind3]
    r.qp = alg.q_pilot(link.q_pilot_input(), link.algorithm_input(), r.rep);
    r.xi = step_xi(r.rep, r.qp);                                // ORACLE [step-xi]
    r.iv = iv_estimate(link.algorithm_input(), r.rep, r.qp);
    return r;
}

std::string shorten(const std::string& p)   // a prime or a place name of up to 12 characters; longer ones abbreviated
{
    if (p.size() <= 12) return p;
    const bool sign = p.back() == '+' || p.back() == '-';
    const std::string digits = sign ? p.substr(0, p.size() - 1) : p;
    return digits.substr(0, 5) + "..(" + std::to_string(digits.size()) + ")" + (sign ? std::string(1, p.back()) : "");
}

void banner()
{
    std::printf("MOCKUP of the multiradial algorithm of IUT III, Theorem 3.11.\n"
                "  [implemented]  computed here from the etale-like data, with no access to the rings of the theaters\n"
                "  [ORACLE name]  not implemented: the value is REVERSE-COMPUTED, from the ring structure of a theater or\n"
                "                 from the conclusion (ledger at the end). Nothing printed here proves anything.\n\n");
}

int report(const char* path)
{
    const Datum d = read_datum(path);
    banner();
    const Run r = run_iut(d, SEED_DAGGER, SEED_DDAGGER);
    const Representation& R = r.rep;
    const IVEstimate& E = r.iv;
    std::printf("datum %s  l = %d  k = %.10f%s\n", d.name.c_str(), d.ell, R.k, d.unfactored ? "  (a cofactor is not factored)" : "");
    std::printf("Theta-link dagger -> ddagger: the coric data agree at all %d places; Theta-pilot(dagger) |-> q-pilot(ddagger); "
                "no map of rings\n\n", r.coric);

    std::printf("[implemented] (A)-(B) local invariants from G_{K_v}^ab, and (C) cyclotomic rigidity at level N = 2^61 - 1:\n");
    std::printf("   %-14s %-13s %4s %3s %5s %12s %12s  %s\n", "place", "p", "d", "f", "e", "rho", "dif", "");
    int nbad = 0;
    for (size_t i = 0; i < R.local.size(); i++) {
        const LocalInvariants& L = R.local[i];
        if (!L.known) { std::printf("   %-14s %-13s   (above 2, 3, 5 or l: not computed)\n", shorten(d.v[i].name).c_str(), shorten(d.v[i].p).c_str()); continue; }
        nbad += R.rigidity[i] != 0;
        std::printf("   %-14s %-13s %4d %3d %5lld %12.10f %12.10f  %s\n", shorten(d.v[i].name).c_str(), shorten(L.p).c_str(), L.d, L.f, L.e, L.rho, L.dif,
                    R.rigidity[i] ? "bad: coordinates of Delta_Theta recovered from the commutator" : "");
    }
    std::printf("[implemented] (D) theta values from their Kummer classes at the %d bad places; j^2-structure: %s\n", nbad, R.gaussian_ok ? "ok" : "FAILED");
    std::printf("[implemented] (E)-(G) the possible images of the Theta-pilot and the hull, procession-normalized (IUT IV's reading):\n");
    for (const PrimeImages& P : R.primes)
        std::printf("   prime %-13s places %zu  hull %.10f  closed form %.10f%s\n", shorten(P.p).c_str(), P.places.size(), P.hull, P.hull_closed,
                    P.by_linearity ? "  [long tuples by linearity]" : "");
    std::printf("   archimedean container (l+5)/4 log pi = %.10f\n", R.arch);
    std::printf("[ORACLE ind3]  (Ind3): assumed (the possible images are the containers)\n\n");

    std::printf("q-pilot      -|log qq|   = %.10f        (log q = 2 l |log qq| = %.10f)\n", r.qp.minus_log_q, 2 * d.ell * E.a);
    std::printf("Theta-pilot  -|log Theta| = %.10f       (reading of IUT IV; places above 2, 3, 5, l set to 0)\n", R.minus_log_theta);
    std::printf("[ORACLE step-xi]  Step (xi): the q-pilot of ddagger lies in the hull of the possible images: %s  (REVERSE-COMPUTED: "
                "margin %.10f on this datum)\n", r.xi.contained ? "YES" : "NO", r.xi.margin);
    if (r.xi.contained)
        std::printf("Corollary 3.12 (from the oracle step-xi): %.10f <= %.10f\n", r.qp.minus_log_q, R.minus_log_theta);
    else
        std::printf("Corollary 3.12: not obtained (the oracle step-xi refuses)\n");
    std::printf("IUT IV       U(D)         = %.10f       (primes with theta values %.10f, closed form %.10f; 2, 3, 5, l %.10f;"
                " archimedean %.10f)%s\n", E.U, E.iv_primes, E.iv_closed, E.U_rest, E.arch, E.enumerated ? "" : "  [long tuples by linearity]");
    for (const std::string& s : E.notes) std::printf("note: %s\n", s.c_str());
    std::printf("IV: %.10f %s %.10f\n", R.minus_log_theta, R.minus_log_theta <= E.U ? "<=" : ">", E.U);
    std::printf("height inequality (k-1)|log qq| = %.10f %s %.10f = C\n", E.wall, E.wall <= E.C ? "<=" : ">", E.C);
    std::printf("Step (viii): %.10f      Theorem 1.10: (1/6) log q = %.10f %s %.12e\n\n", E.viii, E.thm_lhs, E.thm_lhs <= E.thm_rhs ? "<=" : ">", E.thm_rhs);

    const Classical c = classical(d);
    std::printf("classical    log q = %.10f  log f = %.10f  log d = %.10f   (all places of bad reduction: log q = %.10f  log f = %.10f)\n",
                c.log_q, c.log_f, c.log_d, c.log_q_all, c.log_f_all);
    std::printf("classical    Theorem 1.10: (1/6) log q = %.10f %s %.12e = right-hand side\n", c.log_q / 6, c.log_q / 6 <= c.rhs ? "<=" : ">", c.rhs);
    std::printf("the two computations: log q %.10f vs 2 l |log qq| %.10f; right-hand sides %.12e vs %.12e\n\n", c.log_q, 2 * d.ell * E.a, c.rhs, E.thm_rhs);

    std::printf("ledger of the oracles (every value REVERSE-COMPUTED):\n");
    for (const OracleUse& u : OracleLedger::uses()) std::printf("  %s  %s\n      %s\n", u.id.c_str(), u.what.c_str(), u.how.c_str());
    return 0;
}

// Non-interference: the theaters' own coordinates on Delta_Theta are a choice that the algorithm cannot see. Its
// output must not depend on them; without step (C) it does.
int selftest(const char* path)
{
    const Datum d = read_datum(path);
    std::printf("datum %s: the theaters' coordinates on Delta_Theta (a unit of Z/N per place) are drawn from 8 seeds\n", d.name.c_str());
    int fails = 0;
    const Run base = run_iut(d, 1, 2);
    std::printf("  with step (C):    -|log Theta| =");
    for (u64 s = 1; s <= 8; s++) {
        const Run r = run_iut(d, s, 100 + s);
        std::printf(" %.6f", r.rep.minus_log_theta);
        if (r.rep.minus_log_theta != base.rep.minus_log_theta || r.rep.theta_ord != base.rep.theta_ord || r.iv.C != base.iv.C) fails++;
    }
    std::printf("\n  identical for all 8: %s\n", fails ? "NO" : "yes");
    std::printf("  without step (C): -|log Theta| =");
    int differ = 0;
    bool gaussian = true;
    for (u64 s = 1; s <= 3; s++) {
        const Run r = run_iut(d, s, 100 + s, false);
        std::printf(" %.6e", r.rep.minus_log_theta);
        differ += r.rep.minus_log_theta != base.rep.minus_log_theta;
        gaussian &= r.rep.gaussian_ok;
    }
    std::printf("\n  depends on the choice: %s; the j^2-structure of the classes is still seen: %s\n", differ == 3 ? "yes" : "NO",
                gaussian ? "yes" : "NO");
    const bool ok = !fails && differ == 3 && gaussian;
    std::printf("selftest %s\n", ok ? "PASSED" : "FAILED");
    return ok ? 0 : 1;
}

// The family q -> q^N ([RF]): the implemented part runs the same steps for every N. Where the reverse-computed
// Step (xi) says yes, it says so only because the comparison of the two numbers came out that way.
int scan(const char* path, int Nmax)
{
    const Datum d0 = read_datum(path);
    std::printf("the family q -> q^N for the datum %s (N prime to l = %d)\n", d0.name.c_str(), d0.ell);
    std::printf("%5s %14s %16s %16s %14s %14s   %-8s %s\n", "N", "|log qq|", "-|log Theta|", "U(D)", "wall", "C", "step-xi", "height ineq.");
    int last_yes = 0, first_no = 0, last_h = 0, first_hno = 0;
    for (int N = 1; N <= Nmax; N++) {
        if (N % d0.ell == 0) continue;
        const Datum d = power_of_q(d0, N);
        const Run r = run_iut(d, SEED_DAGGER, SEED_DDAGGER);
        const bool h = r.iv.wall <= r.iv.C;
        std::printf("%5d %14.6f %16.6f %16.6f %14.6f %14.6f   %-8s %s\n", N, r.iv.a, r.rep.minus_log_theta, r.iv.U, r.iv.wall, r.iv.C,
                    r.xi.contained ? "yes" : "no", h ? "holds" : "fails");
        if (r.xi.contained) last_yes = N; else if (!first_no) first_no = N;
        if (h) last_h = N; else if (!first_hno) first_hno = N;
    }
    std::printf("the oracle step-xi (reverse-computed Step (xi)) says yes up to N = %d%s; the height inequality holds up to N = %d%s\n", last_yes,
                first_no ? (", no from N = " + std::to_string(first_no)).c_str() : "", last_h,
                first_hno ? (", fails from N = " + std::to_string(first_hno)).c_str() : "");
    std::printf("the implemented part (A)-(G) ran the same steps for every N: nothing in it tells these data from genuine ones\n");
    return 0;
}

}  // namespace

int main(int argc, char** argv)
{
    try {
        if (argc == 2) return report(argv[1]);
        if (argc == 3 && !std::strcmp(argv[1], "--selftest")) return selftest(argv[2]);
        if (argc == 4 && !std::strcmp(argv[1], "--scan")) return scan(argv[2], std::atoi(argv[3]));
    } catch (const std::exception& e) {
        std::fprintf(stderr, "error: %s\n", e.what());
        return 1;
    }
    std::fprintf(stderr, "usage: mockup <datum file> | --selftest <datum file> | --scan <datum file> <Nmax>\n");
    return 2;
}
