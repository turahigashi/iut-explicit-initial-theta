/* localdata.h -- the common input of classical.c and iut.c.
 *
 * One initial Theta-datum: the prime l, the field F = Q(sqrt D), and the places of F above the primes that divide
 * N(a)N(1-a), where E: y^2 = x(x-1)(x-a). For each place: its prime p, its residue degree f, its ramification
 * index eF over Q_p, and ord_v(q), the order of the Tate parameter (0 if the reduction is good).
 * Primes can have 40 digits, so p is kept as a string with its logarithm; `small` is its value when it fits.
 */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXPLACES 64

typedef struct {
    char name[72];      /* e.g. 211+ for the place of F above 211 with sqrt D = +r mod 211 */
    char p[64];         /* the prime, in decimal */
    double logp;        /* log p */
    long long small;    /* p, or -1 if p has more than 18 digits */
    int f, eF;          /* residue degree and ramification index of F_v / Q_p */
    long long ordq;     /* ord_v(q) */
} Place;

typedef struct {
    char name[24];
    int ell;            /* the prime l of the initial Theta-datum */
    long long D;        /* F = Q(sqrt D) */
    int unfactored;     /* 1 if N(a)N(1-a) has a cofactor that is not factored */
    int n;
    Place v[MAXPLACES];
} Datum;

static Datum read_datum(const char *path)
{
    Datum d;
    char line[512], key[32];
    FILE *fp = fopen(path, "r");
    memset(&d, 0, sizeof d);
    if (!fp) { perror(path); exit(1); }
    while (fgets(line, sizeof line, fp)) {
        if (line[0] == '#' || sscanf(line, "%31s", key) != 1) continue;
        if (!strcmp(key, "name")) sscanf(line, "%*s %23s", d.name);
        else if (!strcmp(key, "ell")) sscanf(line, "%*s %d", &d.ell);
        else if (!strcmp(key, "D")) sscanf(line, "%*s %lld", &d.D);
        else if (!strcmp(key, "unfactored")) sscanf(line, "%*s %d", &d.unfactored);
        else if (!strcmp(key, "place")) {
            Place *v = &d.v[d.n++];
            if (d.n > MAXPLACES) { fprintf(stderr, "too many places\n"); exit(1); }
            if (sscanf(line, "%*s %71s %63s %d %d %lld", v->name, v->p, &v->f, &v->eF, &v->ordq) != 5) {
                fprintf(stderr, "bad line: %s", line); exit(1);
            }
            v->logp = log(strtod(v->p, NULL));
            v->small = strlen(v->p) <= 18 ? atoll(v->p) : -1;
        }
    }
    fclose(fp);
    return d;
}

static inline int same_prime(const Place *u, const Place *v) { return !strcmp(u->p, v->p); }

/* log |disc F| / [F:Q], the normalized log of the discriminant of F = Q(sqrt D) */
static double log_disc_F(long long D)
{
    long long disc = ((D % 4) + 4) % 4 == 1 ? D : 4 * D;
    return log((double)llabs(disc)) / 2;
}
