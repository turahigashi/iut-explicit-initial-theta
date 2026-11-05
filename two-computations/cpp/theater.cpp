// theater.cpp -- the ring side of a Hodge theater, built from the initial Theta-datum.
#include "theater.hpp"
#include <random>
#include <stdexcept>

namespace iutm {

static long long gcd(long long a, long long b) { while (b) { long long t = a % b; a = b; b = t; } return a; }

HodgeTheater::HodgeTheater(const Datum& d, u64 seed) : datum_(d)
{
    const long long l = d.ell;
    std::mt19937_64 rng(seed);
    std::uniform_int_distribution<u64> unit(1, LEVEL - 1);
    for (const Place& v : d.v) {
        LocalField L;
        const long long p = v.small;
        const bool small = p == 2 || p == 3 || p == 5 || p == l;
        L.known = !small;
        L.bad = v.ordq > 0 && !small && v.ordq % l != 0;
        // the ramification index of K_v / Q_p in the reading of the catalogue [Cat]: K_v / F_v is the extension cut out
        // by the 15 l-torsion; at a bad place its ramification index is 15 l / gcd(15 l, ord q)
        L.eK = small ? 0 : v.ordq == 0 ? v.eF : v.eF * 15 * l / gcd(15 * l, v.ordq);
        L.fK = v.f;
        L.gamma = unit(rng);
        if (L.bad) {
            L.ordK_q = L.eK / v.eF * v.ordq;
            if (L.ordK_q % (2 * l) != 0)
                throw std::runtime_error("the 2l-th root of q is not in K_v at " + v.name + " in this model");
            L.ordK_qq = L.ordK_q / (2 * l);
        }
        local_.push_back(L);
    }
}

}  // namespace iutm
