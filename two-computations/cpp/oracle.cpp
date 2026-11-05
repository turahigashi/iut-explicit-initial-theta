// oracle.cpp -- ORACLE: the values of the parts that are not implemented, all of them REVERSE-COMPUTED.
//
// This is the only file besides theater.cpp that reads the ring structure of a theater.
#include "oracle.hpp"
#include "decimal.hpp"

namespace iutm {

namespace {

std::vector<OracleUse>& ledger()
{
    static std::vector<OracleUse> uses;
    return uses;
}

u64 addmod(u64 a, u64 b) { return (a + b) % LEVEL; }       // a, b < N < 2^62
u64 negmod(u64 a) { return a ? LEVEL - a : 0; }
u64 reduce(i64 b) { i64 r = b % (i64)LEVEL; return (u64)(r < 0 ? r + (i64)LEVEL : r); }

// [theta-group]. The theta group at level N in the theater's coordinates. With the multiplication of lana-agents/iut
// (Iut/EtaleTheta/Heisenberg.lean, l = 1), (c, a, b)(c', a', b') = (c + c' + b a', a + a', b + b'), written with the
// theater's coordinates on Delta_Theta, where the standard coordinate c corresponds to gamma c:
//     (c, a, b)(c', a', b') = (c + c' + gamma b a', a + a', b + b').
class ThetaGroupAtLevelN : public ThetaGroupBox {
public:
    explicit ThetaGroupAtLevelN(u64 gamma) : gamma_(gamma) {}
    ThetaGroupElement mul(const ThetaGroupElement& x, const ThetaGroupElement& y) const override
    {
        return {addmod(addmod(x.c, y.c), mulmod(gamma_, mulmod(reduce(x.b), y.a))), addmod(x.a, y.a), x.b + y.b};
    }
    ThetaGroupElement inv(const ThetaGroupElement& x) const override
    {
        return {addmod(negmod(x.c), mulmod(gamma_, mulmod(reduce(x.b), x.a))), negmod(x.a), -x.b};
    }
    ThetaGroupElement generator_t() const override { return {0, 0, 1}; }
    ThetaGroupElement generator_a() const override { return {0, 1, 0}; }

private:
    u64 gamma_;     // hidden from the algorithm
};

}  // namespace

void OracleLedger::record(const std::string& id, const std::string& what, const std::string& how)
{
    for (const OracleUse& u : ledger())
        if (u.id == id) return;
    ledger().push_back({id, what, how});
}
const std::vector<OracleUse>& OracleLedger::uses() { return ledger(); }
void OracleLedger::clear() { ledger().clear(); }

AlgorithmInput etale_like_input(const HodgeTheater& H)
{
    AlgorithmInput in;
    const Datum& d = H.datum_;
    const int ls = (d.ell - 1) / 2;
    in.global.ell = d.ell;
    in.global.log_disc_F = log_disc_F(d.D);
    for (size_t i = 0; i < d.v.size(); i++) {
        const Place& v = d.v[i];
        const HodgeTheater::LocalField& L = H.local_[i];
        EtalePlace P;
        P.name = v.name;
        P.bad = L.bad;
        if (L.known) {                                 // [gab]: G^ab = Zhat x O^x, O^x = mu_{q-1} x mu_{p^oo} x Z_p^d
            P.gab.known = true;
            P.gab.extra_prime = v.p;
            P.gab.extra_rank = (int)(L.eK * L.fK);
            P.gab.prime_to_p_torsion = dec::sub1(dec::pow(v.p, L.fK));
        }
        if (L.bad) {
            for (int j = 1; j <= ls; j++)              // [kummer]: kappa(qq^(j^2)) = j^2 ord(qq), in Delta_Theta: times gamma
                P.theta.push_back({mulmod(L.gamma, mulmod((u64)j * j, (u64)L.ordK_qq))});
            P.theta_group = std::make_shared<ThetaGroupAtLevelN>(L.gamma);   // [theta-group]
        }
        in.places.push_back(P);
        const double w = v.f * v.eF / 2.0;             // [global]: [F_v : Q_p] / [F : Q]
        in.global.prime_label.push_back(v.p);
        in.global.weight.push_back(w);
        if (L.bad) in.global.log_cond_F += w / v.eF * v.logp;
    }
    OracleLedger::record("gab", "G_{K_v}^ab as an abstract group",
                         "reverse-computed from the local fields K_v by local class field theory: (p, [K_v:Q_p], p^f - 1)");
    OracleLedger::record("global", "global data: weights, prime labels, log d^F, log f^F",
                         "reverse-computed from the number field F and V^bad");
    OracleLedger::record("kummer", "Kummer classes at level N of the theta values qq^(j^2) (dagger) and of qq (ddagger)",
                         "reverse-computed from the valuations of q in the fields (in IUT: the etale theta function and "
                         "its evaluation)");
    OracleLedger::record("theta-group", "the theta groups at level N (the finite-level mono-theta environments)",
                         "built from the theater's own coordinates on Delta_Theta");
    return in;
}

QPilotInput q_pilot_input(const HodgeTheater& H)
{
    QPilotInput Q;
    for (const HodgeTheater::LocalField& L : H.local_)
        Q.q.push_back({L.bad ? (u64)L.ordK_qq % LEVEL : 0});   // [kummer]: in mu_N the Kummer class is the valuation mod N
    return Q;
}

UpperSemiCompatibility upper_semicompatibility()
{
    UpperSemiCompatibility U;
    U.statement = "the images of the Theta-pilot under the log-Kummer correspondence lie in the containers "
                  "(IUT III, Proposition 3.5; Theorem 3.11 (ii) (a))";
    OracleLedger::record("ind3", "(Ind3), upper semi-compatibility", "assumed, not computed: " + U.statement);
    return U;
}

StepXiCertificate step_xi(const Representation& rep, const QPilot& qp)
{
    StepXiCertificate X;
    X.margin = rep.minus_log_theta - qp.minus_log_q;
    X.contained = X.margin >= 0;
    X.how = "reverse-computed from the conclusion: the two log-volumes of this datum were compared. A Step (xi) "
            "derived from Theorem 3.11 would give the containment for every initial Theta-datum without comparing "
            "numbers";
    OracleLedger::record("step-xi", "Step (xi): the q-pilot of ddagger lies in the hull of the possible images", X.how);
    return X;
}

}  // namespace iutm
