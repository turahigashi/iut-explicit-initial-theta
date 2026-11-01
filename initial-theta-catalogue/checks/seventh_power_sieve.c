/* List every prime q <= B dividing one of the given integers.
 *
 *   seventh_power_sieve B threads hexN1 [hexN2 ...]
 *
 * The integers are given in hexadecimal.  A segmented sieve of Eratosthenes over the odd numbers
 * up to B (base primes up to sqrt(B)) enumerates the primes; for each prime q and each integer N
 * the residue N mod q is computed by Horner's rule over 28-bit chunks (7 hexadecimal digits), which
 * stays inside 64 bits because q < 2^36.  Output:
 *   "DIV i q"        for every prime q <= B with q | N_i (i = 0, 1, ...),
 *   "COUNT c"        the number of primes <= B that were enumerated (a check of the sieve),
 *   "BOUND B"        echoed.
 * The caller computes the exponents of the reported primes and checks that none is >= 7; a prime
 * q > B = floor(N^(1/7)) cannot divide N to the seventh power.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>

#define MAXN 8
#define MAXCHUNK 64
#define SEG 1048576ULL /* odd numbers per segment */

static uint64_t B;
static int nthreads, nnum;
static uint64_t chunk[MAXN][MAXCHUNK];
static int nchunk[MAXN];
static uint32_t *base;
static size_t nbase;
static uint64_t nseg;
static pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;

static int hexval(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  fprintf(stderr, "bad hex digit %c\n", c);
  exit(2);
}

static void load(int i, const char *s) {
  size_t len = strlen(s);
  size_t pad = (7 - len % 7) % 7;
  size_t total = len + pad;
  if (total / 7 > MAXCHUNK) { fprintf(stderr, "number too large\n"); exit(2); }
  nchunk[i] = (int)(total / 7);
  for (size_t c = 0; c < total / 7; c++) {
    uint64_t v = 0;
    for (size_t d = 0; d < 7; d++) {
      size_t pos = c * 7 + d;
      int digit = pos < pad ? 0 : hexval(s[pos - pad]);
      v = (v << 4) | (uint64_t)digit;
    }
    chunk[i][c] = v;
  }
}

static uint64_t modq(int i, uint64_t q) {
  uint64_t r = 0;
  for (int c = 0; c < nchunk[i]; c++) r = ((r << 28) | chunk[i][c]) % q;
  return r;
}

static void test_prime(uint64_t q) {
  for (int i = 0; i < nnum; i++) {
    if (modq(i, q) == 0) {
      pthread_mutex_lock(&lock);
      printf("DIV %d %llu\n", i, (unsigned long long)q);
      fflush(stdout);
      pthread_mutex_unlock(&lock);
    }
  }
}

static void *worker(void *arg) {
  long t = (long)arg;
  unsigned char *seg = malloc(SEG);
  uint64_t count = 0;
  for (uint64_t s = (uint64_t)t; s < nseg; s += (uint64_t)nthreads) {
    /* segment covers odd numbers lo, lo+2, ..., lo + 2*(SEG-1) */
    uint64_t lo = 1 + 2 * s * SEG;
    memset(seg, 1, SEG);
    for (size_t k = 1; k < nbase; k++) { /* skip base[0] = 2 */
      uint64_t q = base[k];
      uint64_t q2 = q * q;
      uint64_t hi = lo + 2 * (SEG - 1);
      if (q2 > hi) break;
      uint64_t start = q2 > lo ? q2 : ((lo + q - 1) / q) * q;
      if (start % 2 == 0) start += q;
      for (uint64_t m = start; m <= hi; m += 2 * q) seg[(m - lo) / 2] = 0;
    }
    for (uint64_t idx = 0; idx < SEG; idx++) {
      if (!seg[idx]) continue;
      uint64_t q = lo + 2 * idx;
      if (q < 3 || q > B) continue;
      count++;
      test_prime(q);
    }
  }
  free(seg);
  return (void *)(uintptr_t)count;
}

int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: %s B threads hexN...\n", argv[0]); return 2; }
  B = strtoull(argv[1], NULL, 10);
  nthreads = atoi(argv[2]);
  nnum = argc - 3;
  if (nnum > MAXN) return 2;
  if (B >= (1ULL << 36)) { fprintf(stderr, "B must be < 2^36\n"); return 2; }
  for (int i = 0; i < nnum; i++) load(i, argv[3 + i]);
  uint64_t r = 1;
  while ((r + 1) * (r + 1) <= B) r++;
  unsigned char *small = calloc(r + 1, 1);
  base = malloc(sizeof(uint32_t) * (r + 1));
  nbase = 0;
  for (uint64_t i = 2; i <= r; i++) {
    if (small[i]) continue;
    base[nbase++] = (uint32_t)i;
    for (uint64_t m = i * i; m <= r; m += i) small[m] = 1;
  }
  uint64_t count = 0;
  if (B >= 2) { count++; test_prime(2); }
  nseg = (B / 2 + SEG) / SEG + 1;
  pthread_t th[64];
  for (long t = 0; t < nthreads; t++) pthread_create(&th[t], NULL, worker, (void *)t);
  for (long t = 0; t < nthreads; t++) {
    void *ret;
    pthread_join(th[t], &ret);
    count += (uint64_t)(uintptr_t)ret;
  }
  printf("COUNT %llu\n", (unsigned long long)count);
  printf("BOUND %llu\n", (unsigned long long)B);
  return 0;
}
