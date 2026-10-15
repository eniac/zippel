Source: experiments/results/analysis_1015/soundness_results.json (8 rows, timeout=1200s, memory_limit_mb=16384)

| Protocol | Pass | Time | Status | Reason |
|---|---|---|---|---|
| Schnorr | ✓ | 50.3ms | ok |  |
| Multi-Schnorr | ✓ | 12.6s | ok |  |
| Pedersen-Eq | ✓ | 28.9ms | ok |  |
| Okamoto | ✗ | 15.3ms | failed | No valid extractor for witness r: NoExtractor |
| ElGamal | ✓ | 146.5ms | ok |  |
| Chaum-Pedersen | ✓ | 54.9ms | ok |  |
| CDS Disjunction | ✗ | - | failed | Unit ideal: soundness search |
| E-Cash Coin | ✗ | - | timeout | exceeded 1200s timeout |

soundness pass=5 failed=2 timeout=1 unexpected=0
