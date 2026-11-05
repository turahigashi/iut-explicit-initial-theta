// datum.hpp -- one initial Theta-datum as local data: the same files as the C programs read (data/D*.txt).
//
// The prime l, the field F = Q(sqrt D), and the places of F above the primes that divide N(a)N(1-a), where
// E: y^2 = x(x-1)(x-a). For each place: its prime p, its residue degree f, its ramification index eF over Q_p,
// and ord_v(q), the order of the Tate parameter (0 if the reduction is good).
#pragma once
#include "decimal.hpp"
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

namespace iutm {

struct Place {
    std::string name, p;      // e.g. "211+" and "211"
    double logp = 0;
    long long small = -1;     // p, or -1 if p has more than 18 digits
    int f = 0, eF = 0;
    long long ordq = 0;
};

struct Datum {
    std::string name;
    int ell = 0;
    long long D = 0;
    int unfactored = 0;
    std::vector<Place> v;
};

inline Datum read_datum(const std::string& path)
{
    std::ifstream in(path);
    if (!in) throw std::runtime_error("cannot open " + path);
    Datum d;
    std::string line;
    while (std::getline(in, line)) {
        std::istringstream ss(line);
        std::string key;
        if (!(ss >> key) || key[0] == '#') continue;
        if (key == "name") ss >> d.name;
        else if (key == "ell") ss >> d.ell;
        else if (key == "D") ss >> d.D;
        else if (key == "unfactored") ss >> d.unfactored;
        else if (key == "place") {
            Place v;
            if (!(ss >> v.name >> v.p >> v.f >> v.eF >> v.ordq)) throw std::runtime_error("bad line: " + line);
            v.logp = dec::log(v.p);
            v.small = dec::small(v.p);
            d.v.push_back(v);
        }
    }
    return d;
}

// q -> q^N: the order of the Tate parameter is multiplied by N at every place (the adversarial family of [RF]).
inline Datum power_of_q(Datum d, long long N)
{
    for (auto& v : d.v) v.ordq *= N;
    d.name += "^" + std::to_string(N);
    return d;
}

// log |disc F| / [F:Q], the normalized log of the discriminant of F = Q(sqrt D)
inline double log_disc_F(long long D)
{
    long long disc = ((D % 4) + 4) % 4 == 1 ? D : 4 * D;
    return std::log((double)std::llabs(disc)) / 2;
}

inline bool same_prime(const Place& u, const Place& v) { return u.p == v.p; }

}  // namespace iutm
