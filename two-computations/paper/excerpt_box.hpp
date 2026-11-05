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

struct QPilotInput {
    ...
};
