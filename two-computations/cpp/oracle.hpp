// oracle.hpp -- ORACLE: the parts of the multiradial algorithm that this mockup does not implement.
//
// Every value produced here is REVERSE-COMPUTED: the first four from the ring structure of the theaters (the fields,
// the q-parameter and the valuations), which the multiradial algorithm itself is not allowed to read; [step-xi] from
// the conclusion that Step (xi) is supposed to yield. Each oracle that is used is entered in the ledger.
//
//   [gab]          G_{K_v}^ab as an abstract group             computed from the field by local class field theory
//   [global]       the global data (weights, labels, d^F, f^F)  computed from the number field F
//   [kummer]       the Kummer classes of the theta values and of the q-pilot
//                                                              computed from the valuations in the fields, at level N
//   [theta-group]  the theta groups at level N                 built from the theater's coordinates on Delta_Theta
//   [ind3]         (Ind3), upper semi-compatibility            assumed: the actual images lie in the containers
//   [step-xi]      Step (xi) of the proof of Corollary 3.12    reverse-computed from the conclusion on the datum at hand
//
// In IUT, the first four are to be produced from the abstract profinite groups by the mono-anabelian reconstructions
// (Belyi cuspidalization, [AbsTopIII] Theorem 1.9), the etale theta function and its evaluation ([EtTh], IUT II)
// and the mono-theta environments; [ind3] is IUT III, Proposition 3.5 and Theorem 3.11 (ii); [step-xi] is the
// disputed step.
#pragma once
#include "common.hpp"
#include "multiradial.hpp"
#include "theater.hpp"
#include <string>
#include <vector>

namespace iutm {

struct OracleUse { std::string id, what, how; };

class OracleLedger {
public:
    static void record(const std::string& id, const std::string& what, const std::string& how);
    static const std::vector<OracleUse>& uses();
    static void clear();
};

// [gab], [global], [kummer] and [theta-group] come from the friends declared in theater.hpp:
//     AlgorithmInput etale_like_input(const HodgeTheater& dagger);
//     QPilotInput q_pilot_input(const HodgeTheater& ddagger);

struct UpperSemiCompatibility {        // [ind3]
    bool assumed = true;
    std::string statement;
};
UpperSemiCompatibility upper_semicompatibility();

struct StepXiCertificate {             // [step-xi]
    bool contained = false;            // the q-pilot of ddagger lies in the hull of the possible images
    double margin = 0;                 // -|log Theta| - (-|log qq|)
    std::string how;
};
StepXiCertificate step_xi(const Representation& rep, const QPilot& qp);

}  // namespace iutm
