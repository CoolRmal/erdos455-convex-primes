// Headroom statistics for the verification run from phi (z = 17): the minimum and maximum of w_i
// over the units, relative to the running normalisation, and the deviation from the linear trend.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static long gcdl(long a, long b) { while (b) { long t = a % b; a = b; b = t; } return a; }
int main(int argc, char **argv) {
  long M = 255255; FILE *f = fopen(argv[1], "r"); int z; long MM; fscanf(f, "%d %ld", &z, &MM);
  unsigned char *U = malloc(M); for (long r = 0; r < M; r++) U[r] = gcdl(r, M) == 1;
  int32_t *cur = calloc(M, 4), *nxt = calloc(M, 4); long r; int v;
  while (fscanf(f, "%ld %d", &r, &v) == 2) cur[r] = v;
  int K = argc > 2 ? atoi(argv[2]) : 8;   // normalisation period
  int32_t off = 0; int maxRel = 0, minRelAtNorm = 1 << 30, maxRelAtNorm = 0; long worstDev = 0;
  for (long d = 2; d <= 2 * M - 2; d += 2) {
    memcpy(nxt, cur, 4 * M);
    long dd = d % M;
    for (long r0 = 0; r0 < M; r0++) { if (!U[r0]) continue; long pos = r0; int m = 0;
      for (;;) { pos += dd; if (pos >= M) pos -= M; if (!U[pos]) break; m++; if (cur[r0] + m > nxt[pos]) nxt[pos] = cur[r0] + m; } }
    memcpy(cur, nxt, 4 * M);
    int32_t lo = INT32_MAX, hi = INT32_MIN;
    for (long s = 0; s < M; s++) if (U[s]) { if (cur[s] < lo) lo = cur[s]; if (cur[s] > hi) hi = cur[s]; }
    long i = d / 2;
    if (hi - off > maxRel) maxRel = hi - off;
    if (i % K == 0) { // normalise so that the minimum is 0
      if (hi - lo > maxRelAtNorm) maxRelAtNorm = hi - lo;
      off = lo;
    }
    long trend = (long)((double)295318 * i / (M - 1));
    long dev1 = labs((long)lo - trend), dev2 = labs((long)hi - trend);
    if (dev1 > worstDev) worstDev = dev1; if (dev2 > worstDev) worstDev = dev2;
  }
  printf("K=%d: max(field - offset) over run = %d, max span at normalisation = %d, worst deviation from linear trend = %ld\n", K, maxRel, maxRelAtNorm, worstDev);
  return 0;
}
