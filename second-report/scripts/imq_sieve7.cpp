// Exhaustive seventh-power-free sieve for the Q(i) datum (second report, section 3).
//
// Reads one decimal integer C on stdin and reports whether any prime q satisfies
// q^7 | C.  The search is exhaustive: q^7 <= C forces q <= floor(C^(1/7)), and every
// prime up to that bound is tested.  A negative result is therefore a proof that C
// is seventh-power free, not a heuristic.
//
// Self-contained: no multiprecision library.  The only operation needed on C is
// division by a machine word, done digit by digit on the decimal representation.
//
// C MUST be supplied on stdin; the program exits 2 on empty or non-numeric input
// rather than reporting success on nothing (internal check, 2026-09-07).
//
//   g++ -O2 -std=c++17 -o imq_sieve7 imq_sieve7.cpp
//   printf '%s\n' <C> | ./imq_sieve7
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

typedef std::vector<uint8_t> Big;          // decimal digits, most significant first

static Big parse(const std::string& s) {
    Big d;
    for (char c : s) if (c >= '0' && c <= '9') d.push_back((uint8_t)(c - '0'));
    size_t i = 0; while (i + 1 < d.size() && d[i] == 0) ++i;
    return Big(d.begin() + i, d.end());
}
// quotient in out, returns remainder; q < 2^30 so r*10+digit fits in 64 bits
static uint64_t divmod(const Big& n, uint64_t q, Big& out) {
    out.clear(); out.reserve(n.size());
    uint64_t r = 0; bool lead = true;
    for (uint8_t dg : n) {
        uint64_t cur = r * 10 + dg;
        uint64_t qd  = cur / q; r = cur % q;
        if (!(lead && qd == 0)) { out.push_back((uint8_t)qd); lead = false; }
    }
    if (out.empty()) out.push_back(0);
    return r;
}
// integer seventh root by binary search on a 64-bit candidate, checked against C
// Search cap.  If the true floor(C^(1/7)) reaches it, the binary search below
// SATURATES and returns the cap; sieving only that far and then reporting
// seventh_power_free = true would be a verdict on an incomplete search.  main()
// therefore refuses rather than reporting (internal check, 2026-09-07).
static const uint64_t ROOT_CAP = 100000000;          // 10^8

static uint64_t seventh_root(const Big& C) {
    uint64_t lo = 1, hi = ROOT_CAP;
    while (lo < hi) {
        uint64_t m = lo + (hi - lo + 1) / 2;
        // test m^7 <= C by dividing C by m seven times and seeing if it survives
        Big cur = C, tmp; bool le = true;
        for (int i = 0; i < 7 && le; ++i) {
            divmod(cur, m, tmp);
            if (tmp.size() == 1 && tmp[0] == 0) le = false;   // quotient hit zero
            cur = tmp;
        }
        if (le) lo = m; else hi = m - 1;
    }
    return lo;
}
int main() {
    std::string s;
    // Input validation.  Without it an empty stdin parses as C = 0, the search bound
    // collapses to 1, and the program reports seventh_power_free = true after testing
    // no primes at all -- a success verdict on nothing.
    if (!(std::cin >> s)) {
        std::cerr << "ERROR: no input.  Supply C on stdin, e.g.\n"
                  << "  printf '%s\\n' <C> | ./imq_sieve7\n";
        return 2;
    }
    for (char c : s) if (c < '0' || c > '9') {
        std::cerr << "ERROR: non-numeric input character '" << c << "'.\n";
        return 2;
    }
    // `std::cin >> s` reads ONE whitespace-delimited token and would silently ignore
    // the rest, so a C wrapped across two lines would be sieved as its first fragment
    // and reported free -- a verdict on a number nobody supplied (internal check,
    // 2026-09-07).  Refuse if anything but whitespace follows.
    {
        std::string extra;
        if (std::cin >> extra) {
            std::cerr << "ERROR: more than one token on stdin (second is \""
                      << extra << "\").\n  Supply C as a single number; a value split"
                         " across lines would otherwise be\n  sieved as its first"
                         " fragment only.\n";
            return 2;
        }
    }
    Big C = parse(s);
    if (C.empty() || (C.size() == 1 && C[0] < 2)) {
        std::cerr << "ERROR: C must be at least 2; got \"" << s << "\".\n";
        return 2;
    }
    std::cout << "  C has " << C.size() << " decimal digits\n";
    uint64_t L = seventh_root(C);
    if (L >= ROOT_CAP) {
        std::cerr << "ERROR: floor(C^(1/7)) reaches the search cap " << ROOT_CAP
                  << ".\n  The exhaustive range would be truncated, so no verdict is"
                     " reported.\n  This input needs a sieve built for it (for the"
                     " Q(sqrt5) datum of the first\n  report, see"
                     " scripts/check_norm_seventh_power_free.cpp).\n";
        return 3;
    }
    std::cout << "  exhaustive bound floor(C^(1/7)) = " << L << "\n";

    std::vector<bool> comp((size_t)L + 1, false);
    long tested = 0, found = 0;
    Big t1, t2;
    for (uint64_t q = 2; q <= L; ++q) {
        if (comp[(size_t)q]) continue;
        for (uint64_t m = q * 2; m <= L; m += q) comp[(size_t)m] = true;
        ++tested;
        if (divmod(C, q, t1) != 0) continue;          // q does not divide C
        int v = 1; Big cur = t1;
        while (v < 7) {
            if (divmod(cur, q, t2) != 0) break;
            cur = t2; ++v;
        }
        if (v >= 7) { std::cout << "  SEVENTH POWER FACTOR: " << q << "\n"; ++found; }
    }
    std::cout << "  primes tested = " << tested << "\n";
    std::cout << (found ? "RESULT: NOT seventh-power free\n"
                        : "RESULT: seventh_power_free = true\n");
    return found ? 1 : 0;
}
