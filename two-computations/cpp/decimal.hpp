// decimal.hpp -- the few operations on decimal strings that the 40-digit primes of the data need.
#pragma once
#include <cmath>
#include <cstdint>
#include <stdexcept>
#include <string>
#include "common.hpp"

namespace iutm::dec {

inline std::string strip(std::string s)
{
    size_t i = 0;
    while (i + 1 < s.size() && s[i] == '0') i++;
    return s.substr(i);
}

inline std::string mul(const std::string& x, const std::string& y)   // schoolbook multiplication
{
    std::string r(x.size() + y.size(), 0);
    for (size_t i = x.size(); i-- > 0;)
        for (size_t j = y.size(); j-- > 0;) {
            int t = r[i + j + 1] + (x[i] - '0') * (y[j] - '0');
            r[i + j + 1] = t % 10;
            r[i + j] += t / 10;
        }
    for (size_t i = r.size(); i-- > 1;)
        if (r[i] >= 10) { r[i - 1] += r[i] / 10; r[i] %= 10; }
    for (auto& c : r) c += '0';
    return strip(r);
}

inline std::string sub1(std::string x)                                 // x - 1 for x >= 1
{
    size_t i = x.size();
    while (i-- > 0) {
        if (x[i] > '0') { x[i]--; break; }
        x[i] = '9';
    }
    return strip(x);
}

inline std::string pow(const std::string& p, int f)
{
    std::string r = "1";
    for (int i = 0; i < f; i++) r = mul(r, p);
    return r;
}

inline u64 mod_level(const std::string& x)                           // x mod N
{
    u64 r = 0;
    for (char c : x) r = reduce61(mulmod(r, 10) + (u64)(c - '0'));
    return r;
}

inline double log(const std::string& x) { return std::log(std::stod(x)); }

inline long long small(const std::string& x) { return x.size() <= 18 ? std::stoll(x) : -1; }

}  // namespace iutm::dec
