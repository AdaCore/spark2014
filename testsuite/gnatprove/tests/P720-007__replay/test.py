from test_support import prove_all

contains_manual_proof = False

prove_all(replay=True)
prove_all(cache_allowed=False)
prove_all(cache_allowed=False, replay=True)
