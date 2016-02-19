from test_support import *

conf_file = "test.whyconf"
write_why3_config_file_with_coq(conf_file)

prove_all(prover=["coq"],opt=["-P", "test.gpr", "--steps=1", "--why3-conf="+ conf_file])
prove_all(prover=["coq"],opt=["-P", "test.gpr", "--steps=1", "--why3-conf="+ conf_file])
