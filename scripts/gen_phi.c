// One period of max-plus value iteration for Erdős #455 (paper, Section 4 and Appendix A).
// Usage: ./gen_phi z [phi_out]
//   Starting from w = 0, applies T_2, T_4, ..., T_{2M-2} and normalises to max = 0; this is phi.
//   Then applies one more period starting from phi and reports max/min of (w - phi) and the span.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static long gcdl(long a, long b) { while (b) { long t = a % b; a = b; b = t; } return a; }
static long M; static unsigned char *U;
static int leastNonDiv(long d) { int P = 2; while (d % P == 0) { P++; for (;;) { int ok = 1; for (int k = 2; k * k <= P; k++) if (P % k == 0) ok = 0; if (ok) break; P++; } } return P; }
static void period(int32_t *cur, int32_t *nxt, long *spanmax) {
  for (long d = 2; d <= 2 * M - 2; d += 2) {
    int P = leastNonDiv(d);
    memcpy(nxt, cur, 4 * M);
    long dd = d % M;
    for (long r0 = 0; r0 < M; r0++) {
      if (!U[r0]) continue;
      long pos = r0; int m = 0;
      for (;;) {
        pos += dd; if (pos >= M) pos -= M;
        if (!U[pos]) break;
        m++;
        if (m > P - 2) { printf("cap violated\n"); exit(1); }
        if (cur[r0] + m > nxt[pos]) nxt[pos] = cur[r0] + m;
      }
    }
    memcpy(cur, nxt, 4 * M);
    if (spanmax) {
      int32_t lo = INT32_MAX, hi = INT32_MIN;
      for (long s = 0; s < M; s++) if (U[s]) { if (cur[s] < lo) lo = cur[s]; if (cur[s] > hi) hi = cur[s]; }
      if (hi - lo > *spanmax) *spanmax = hi - lo;
    }
  }
}
int main(int argc, char **argv) {
  int z = atoi(argv[1]);
  M = 1; for (int n = 3; n <= z; n++) { int ok = 1; for (int k = 2; k * k <= n; k++) if (n % k == 0) ok = 0; if (ok) M *= n; }
  U = malloc(M); long nU = 0; for (long r = 0; r < M; r++) { U[r] = gcdl(r, M) == 1; nU += U[r]; }
  int32_t *cur = calloc(M, 4), *nxt = calloc(M, 4), *phi = calloc(M, 4);
  period(cur, nxt, NULL);
  int32_t hi = INT32_MIN; for (long s = 0; s < M; s++) if (U[s] && cur[s] > hi) hi = cur[s];
  for (long s = 0; s < M; s++) phi[s] = U[s] ? cur[s] - hi : 0;
  memcpy(cur, phi, 4 * M);
  long span = 0; period(cur, nxt, &span);
  int32_t lam = INT32_MIN, lo = INT32_MAX, pmax = INT32_MIN, pmin = INT32_MAX;
  for (long s = 0; s < M; s++) if (U[s]) { int32_t df = cur[s] - phi[s]; if (df > lam) lam = df; if (df < lo) lo = df; if (phi[s] > pmax) pmax = phi[s]; if (phi[s] < pmin) pmin = phi[s]; }
  printf("z=%d M=%ld units=%ld LAMBDA(max)=%d min=%d SPAN(phi)=%d maxspan(w_i)=%ld\n", z, M, nU, lam, lo, pmax - pmin, span);
  if (argc > 2) { FILE *f = fopen(argv[2], "w"); fprintf(f, "%d %ld\n", z, M); for (long s = 0; s < M; s++) if (U[s]) fprintf(f, "%ld %d\n", s, phi[s]); fclose(f); }
  return 0;
}
