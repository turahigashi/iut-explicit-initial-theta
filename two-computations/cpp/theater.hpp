// theater.hpp -- a Hodge theater of this mockup: the ring side ("Frobenius-like" data) of one copy of the initial
// Theta-datum.
//
// Everything is private. Only the oracle functions of oracle.cpp (friends) read it, to produce the etale-like data
// by reverse computation. multiradial.cpp does not include this header.
#pragma once
#include "common.hpp"
#include "datum.hpp"

namespace iutm {

class HodgeTheater;
AlgorithmInput etale_like_input(const HodgeTheater& dagger);   // oracle.cpp: ORACLE [gab] [global] [kummer] [theta-group]
QPilotInput q_pilot_input(const HodgeTheater& ddagger);         // oracle.cpp: ORACLE [kummer]

class HodgeTheater {
public:
    // seed: the theater's own choice of coordinates on its cyclotome Delta_Theta, one unit of Z/N per place
    HodgeTheater(const Datum& d, u64 seed);
    const std::string& name() const { return datum_.name; }
    int ell() const { return datum_.ell; }
    bool unfactored() const { return datum_.unfactored != 0; }

private:
    friend AlgorithmInput etale_like_input(const HodgeTheater& dagger);
    friend QPilotInput q_pilot_input(const HodgeTheater& ddagger);

    struct LocalField {         // K_v, K = F(E[l]) with F = F_mod(i, E[15]), as far as IUT IV's reading uses it
        bool known = false;     // false above 2, 3, 5 and l
        bool bad = false;       // v in V^bad
        long long eK = 0;       // ramification index of K_v / Q_p
        int fK = 0;             // residue degree of K_v (assumed equal to that of F_v; only eK enters)
        long long ordK_q = 0;   // ord_{K_v}(q)
        long long ordK_qq = 0;  // ord_{K_v}(qq), qq = q^(1/2l) (bad places)
        u64 gamma = 1;          // the theater's coordinates on Delta_Theta: mu_N -> Delta_Theta is a |-> gamma a
    };
    Datum datum_;
    std::vector<LocalField> local_;
};

}  // namespace iutm
