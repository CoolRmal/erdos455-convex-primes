// Estimate the work of a CRT-split packed (SIMD) value iteration over one period for z = 17.
// For a split modulus Q | M, the state is stored as phi(Q) bignums over Z/(M/Q).
// Reports: number of (component, m) iterations and total field-iterations.
#include <stdio.h>
#include <stdlib.h>
static long gcdl(long a, long b) { while (b) { long t = a % b; a = b; b = t; } return a; }
int main(int argc, char **argv) {
  long M = 255255, Q = atol(argv[1]);
  long Mq = M / Q;
  long compIters = 0, fieldIters = 0;
  for (long i = 1; i < M; i++) {
    long d = 2 * i;
    // max run length over units mod M for this d is P(d)-2
    static const int primes[] = {3, 5, 7, 11, 13, 17, 19};
    int P = 0; for (int k = 0; k < 7; k++) if (d % primes[k]) { P = primes[k]; break; }
    // count nonempty components for m = 1..P-2
    for (int m = 1; m <= P - 2; m++) {
      long cnt = 0;
      for (long c = 0; c < Q; c++) {
        int ok = 1;
        for (int j = 0; j <= m; j++) if (gcdl(((c - j * d) % Q + Q) % Q, Q) != 1) { ok = 0; break; }
        cnt += ok;
      }
      compIters += cnt; fieldIters += cnt * Mq;
    }
  }
  printf("Q=%ld comps=%ld Mq=%ld compIters=%ld fieldIters=%.3e perStepFields=%.0f\n", Q, 0L, Mq, compIters, (double)fieldIters, (double)fieldIters / (M - 1));
  return 0;
}
