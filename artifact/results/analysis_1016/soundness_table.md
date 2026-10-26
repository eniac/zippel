Source: artifact/output/soundness_results.json (10 rows, timeout=120s, memory_limit_mb=16384)

| Protocol | Pass | Time | Status | Reason |
|---|---|---|---|---|
| Schnorr | ✓ | 27.9ms | ok |  |
| Multi-Schnorr | ✓ | 13.4s | ok |  |
| Pedersen-Eq | ✓ | 29.1ms | ok |  |
| Okamoto | ✗ | 14.6ms | failed | No valid extractor for witness r: NoExtractor |
| ElGamal | ✓ | 146.1ms | ok |  |
| Chaum-Pedersen | ✓ | 54.2ms | ok |  |
| CDS Disjunction | ✗ | - | failed | Unit ideal: soundness search |
| E-Cash Coin | ✗ | - | timeout | exceeded 120s timeout |
| Dot Product | ✗ | 64.3ms | failed | No valid extractor for witness r_tau: NoExtractor |
| Product Proof | ✗ | 2.1s | failed | No valid extractor for witness r_X: NoExtractor |

soundness pass=5 failed=4 timeout=1 unexpected=0
