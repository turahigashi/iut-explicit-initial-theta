// link.hpp -- the Theta-link between two Hodge theaters dagger -> ddagger, as far as this mockup uses it.
//
// The link identifies the Theta-pilot of dagger with the q-pilot of ddagger as objects of the value groups, and the
// coric data of the two theaters (here: the abstract groups G_{K_v}^ab, the labels and the weights). It is not a map
// of rings. The comparison of Corollary 3.12 is made in the frame of these coric data.
#pragma once
#include "oracle.hpp"

namespace iutm {

class ThetaLink {
public:
    ThetaLink(const HodgeTheater& dagger, const HodgeTheater& ddagger);
    const AlgorithmInput& algorithm_input() const { return dagger_in_; }   // dagger's etale-like data + global data
    const QPilotInput& q_pilot_input() const { return ddagger_q_; }        // ddagger's q-pilot
    int coric_places() const { return coric_places_; }

private:
    AlgorithmInput dagger_in_;
    QPilotInput ddagger_q_;
    int coric_places_ = 0;
};

}  // namespace iutm
