import os

from test_support import prove_all

# The root project needs an object directory but no sources of its own. An
# empty "Source_Dirs" would make it abstract, and abstract projects have no
# object directory, so point it at an empty directory instead.
os.makedirs("dummy", exist_ok=True)

# Replay the committed session in "proof". "-U" is needed so the lemma in the
# withed "Lemmas" project (a different object directory) is analyzed.
prove_all(
    replay="session",
    prover=["coq"],
    counterexample=False,
    opt=["-U"],
    #  Silence a harmless Coq grammar-extension warning.
    filter_output=".*Grammar extension",
)
