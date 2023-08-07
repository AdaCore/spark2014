from subprocess import call

call(["gprbuild", "-q", "-U", "-P", "test.gpr"])
call(["gprbuild", "-q", "-P", "test.gpr"])
call(["./test_lemmas"])
