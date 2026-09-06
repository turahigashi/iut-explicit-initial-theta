// Exhaustive seventh-power-free check for the explicit N=29 datum.
// Requires Boost.Multiprecision headers and a C++17 compiler.
// The residual cofactor is NOT asserted to be prime.
#ifdef NDEBUG
#error "Compile with assertions enabled (do not define NDEBUG)."
#endif
#include <boost/multiprecision/cpp_int.hpp>
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <utility>
#include <vector>

using boost::multiprecision::cpp_int;
using Pair = std::pair<cpp_int, cpp_int>;

Pair multiply(const Pair& x, const Pair& y) {
    return {x.first*y.first + 5*x.second*y.second,
            x.first*y.second + x.second*y.first};
}

cpp_int seventh(std::uint32_t n) {
    cpp_int p = 1;
    for (unsigned k = 0; k < 7; ++k) p *= n;
    return p;
}

int main() {
    Pair lambda = {1, 0};
    for (unsigned k = 0; k < 29; ++k) lambda = multiply(lambda, {16, 3});
    const cpp_int a = lambda.first, b = lambda.second;
    const cpp_int norm_lambda = a*a - 5*b*b;
    cpp_int power_211 = 1;
    for (unsigned k = 0; k < 29; ++k) power_211 *= 211;
    assert(norm_lambda == power_211);
    const cpp_int norm_one_minus = (1-a)*(1-a) - 5*b*b;
    assert(norm_one_minus > 0);
    assert(norm_one_minus == cpp_int("25362449986390845063221249700759698691829298140087354726503101384580"));
    std::cout << "lambda_a=" << a << "\nlambda_b=" << b
              << "\nnorm_lambda=" << norm_lambda
              << "\nnorm_one_minus_lambda=" << norm_one_minus << '\n';

    cpp_int remaining = norm_one_minus, reconstructed = 1;
    unsigned maximum_exponent = 0;
    for (std::uint32_t p : {2u, 3u, 5u, 59u, 80621u}) {
        unsigned exponent = 0;
        while (remaining % p == 0) {
            remaining /= p;
            reconstructed *= p;
            ++exponent;
        }
        for (std::uint32_t d = 2; std::uint64_t(d)*d <= p; ++d)
            assert(p % d != 0); // Certify each preliminary factor is prime.
        assert(exponent > 0 && exponent < 7);
        maximum_exponent = std::max(maximum_exponent, exponent);
        std::cout << "preliminary_factor=" << p << " exponent=" << exponent << '\n';
    }
    const cpp_int initial_cofactor = remaining;
    assert(initial_cofactor == cpp_int("29622281599338016545834674091843816951690863770835007573979"));
    std::uint32_t lo = 0, hi = 1;
    while (seventh(hi) <= initial_cofactor) {
        assert(hi < UINT32_MAX / 2);
        hi *= 2;
    }
    while (hi - lo > 1) {
        const std::uint32_t mid = lo + (hi-lo)/2;
        if (seventh(mid) <= initial_cofactor) lo = mid;
        else hi = mid;
    }
    const std::uint32_t bound = lo;
    assert(seventh(bound) <= initial_cofactor && seventh(bound+1) > initial_cofactor);
    std::cout << "initial_cofactor=" << initial_cofactor
              << "\nexact_floor_seventh_root=" << bound << std::endl;

    // Eratosthenes: each integer marked prime below is a prime, and every
    // prime <= bound occurs. No probabilistic primality test is used.
    std::vector<bool> composite(static_cast<std::size_t>(bound)+1, false);
    for (std::uint32_t p = 2; std::uint64_t(p)*p <= bound; ++p) {
        if (!composite[p]) {
            for (std::uint64_t m = std::uint64_t(p)*p; m <= bound; m += p)
                composite[static_cast<std::size_t>(m)] = true;
        }
    }
    std::uint64_t prime_count = 0;
    for (std::uint32_t p = 2; p <= bound; ++p) {
        if (composite[p]) continue;
        ++prime_count;
        unsigned exponent = 0;
        while (remaining % p == 0) {
            remaining /= p;
            reconstructed *= p;
            ++exponent;
        }
        assert(exponent < 7);
        maximum_exponent = std::max(maximum_exponent, exponent);
        if (exponent) std::cout << "additional_factor=" << p << " exponent=" << exponent << '\n';
    }
    assert(reconstructed * remaining == norm_one_minus);
    // The residual has no prime divisor <= bound. A seventh power dividing
    // it would have a prime divisor <= floor(initial_cofactor^(1/7)).
    std::cout << "tested_primes=" << prime_count
              << "\nresidual_after_all_tested_primes=" << remaining
              << "\nmaximum_detected_prime_exponent=" << maximum_exponent
              << "\nresidual_primality=not_asserted"
              << "\nnorm_one_minus_lambda_seventh_power_free=true"
              << "\nEXIT:0\n";
}
