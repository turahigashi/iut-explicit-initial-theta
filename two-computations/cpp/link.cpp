// link.cpp -- the Theta-link: check that the coric data of the two theaters agree, place by place.
#include "link.hpp"
#include <stdexcept>

namespace iutm {

ThetaLink::ThetaLink(const HodgeTheater& dagger, const HodgeTheater& ddagger)
    : dagger_in_(etale_like_input(dagger)), ddagger_q_(iutm::q_pilot_input(ddagger))
{
    const AlgorithmInput ddagger_in = etale_like_input(ddagger);
    const auto& A = dagger_in_.places;
    const auto& B = ddagger_in.places;
    if (A.size() != B.size() || dagger_in_.global.ell != ddagger_in.global.ell)
        throw std::runtime_error("the two theaters do not have the same places");
    for (size_t i = 0; i < A.size(); i++) {
        const AbelianizationType &g = A[i].gab, &h = B[i].gab;
        if (g.known != h.known || g.extra_prime != h.extra_prime || g.extra_rank != h.extra_rank
            || g.prime_to_p_torsion != h.prime_to_p_torsion || A[i].bad != B[i].bad
            || dagger_in_.global.weight[i] != ddagger_in.global.weight[i]
            || dagger_in_.global.prime_label[i] != ddagger_in.global.prime_label[i])
            throw std::runtime_error("the coric data differ at " + A[i].name);
        coric_places_++;
    }
}

}  // namespace iutm
