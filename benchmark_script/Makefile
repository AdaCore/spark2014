CVC4=cvc4
ALTERGO=alt-ergo

FILES := $(shell find bench -name "*.smt2" -or -name "*.why")
BENCH := $(patsubst %.why,%.result,$(patsubst %.smt2,%.result,$(FILES)))

all: $(BENCH)

%.result: %.smt2
	@echo "[CVC4] $*"
	@-$(CVC4) --lang=smt2 \
             --inst-when=full-last-call \
             --user-pat=trust \
             --tlimit=2000 $*.smt2 > $*.result

%.result: %.why
	@echo "[ERGO] $*"
	@-$(ALTERGO) -max-split 5 -timelimit 2 $*.why > $*.result || true

clean:
	find bench -name "*.result" -delete
