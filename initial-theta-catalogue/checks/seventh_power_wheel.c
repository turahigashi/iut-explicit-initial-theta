/* Independent check for seventh_power_sieve.c: trial division by every integer
 * q <= B that is 2, 3, 5, 7 or prime to 210 (a wheel; no sieve, so composite q are also tested).
 *
 *   seventh_power_wheel B threads decN1 [decN2 ...]
 *
 * The integers are given in decimal and held as 64-bit limbs; N mod q is computed by Horner's rule
 * with 128-bit intermediates (a different representation and a different reduction from the sieve
 * program).  Output "DIV i q" for every tested q dividing N_i, and "TESTED t", the number of q tested.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>

#define MAXN 8
#define MAXLIMB 16

typedef unsigned __int128 u128;
static uint64_t B;
static int nthreads, nnum;
static uint64_t limb[MAXN][MAXLIMB]; /* little endian */
static int nlimb[MAXN];
static pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;
static int res[48];

static void load(int i, const char *s) {
  memset(limb[i], 0, sizeof(limb[i]));
  nlimb[i] = 1;
  for (const char *c = s; *c; c++) {
    if (*c < '0' || *c > '9') { fprintf(stderr, "bad digit\n"); exit(2); }
    u128 carry = (u128)(*c - '0');
    for (int k = 0; k < nlimb[i]; k++) {
      u128 v = (u128)limb[i][k] * 10 + carry;
      limb[i][k] = (uint64_t)v;
      carry = v >> 64;
    }
    if (carry) {
      if (nlimb[i] == MAXLIMB) { fprintf(stderr, "too large\n"); exit(2); }
      limb[i][nlimb[i]++] = (uint64_t)carry;
    }
  }
}

static uint64_t modq(int i, uint64_t q) {
  u128 r = 0;
  for (int k = nlimb[i] - 1; k >= 0; k--) r = ((r << 64) | limb[i][k]) % q;
  return (uint64_t)r;
}

static void test(uint64_t q) {
  for (int i = 0; i < nnum; i++)
    if (modq(i, q) == 0) {
      pthread_mutex_lock(&lock);
      printf("DIV %d %llu\n", i, (unsigned long long)q);
      fflush(stdout);
      pthread_mutex_unlock(&lock);
    }
}

static void *worker(void *arg) {
  long t = (long)arg;
  uint64_t tested = 0;
  /* blocks of 210 starting at 210*b; residues res[] prime to 210 */
  for (uint64_t b = (uint64_t)t; 210 * b <= B; b += (uint64_t)nthreads) {
    for (int k = 0; k < 48; k++) {
      uint64_t q = 210 * b + (uint64_t)res[k];
      if (q < 11 || q > B) continue;
      tested++;
      test(q);
    }
  }
  return (void *)(uintptr_t)tested;
}

int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: %s B threads decN...\n", argv[0]); return 2; }
  B = strtoull(argv[1], NULL, 10);
  nthreads = atoi(argv[2]);
  nnum = argc - 3;
  if (nnum > MAXN || nthreads > 64) return 2;
  for (int i = 0; i < nnum; i++) load(i, argv[3 + i]);
  int m = 0;
  for (int r = 1; r < 210; r++)
    if (r % 2 && r % 3 && r % 5 && r % 7) res[m++] = r;
  if (m != 48) return 3;
  uint64_t tested = 0;
  uint64_t small[4] = {2, 3, 5, 7};
  for (int k = 0; k < 4; k++)
    if (small[k] <= B) { tested++; test(small[k]); }
  pthread_t th[64];
  for (long t = 0; t < nthreads; t++) pthread_create(&th[t], NULL, worker, (void *)t);
  for (long t = 0; t < nthreads; t++) {
    void *ret;
    pthread_join(th[t], &ret);
    tested += (uint64_t)(uintptr_t)ret;
  }
  printf("TESTED %llu\n", (unsigned long long)tested);
  return 0;
}
