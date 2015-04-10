SUBDIR=realize
SPARKDEV=$(realpath ../../../)
WHY3DIR=$(SPARKDEV)/why3
WHY3=$(WHY3DIR)/bin/why3realize.opt

$(SUBDIR)/Integer.v: _gnatprove_standard.mlw
	$(WHY3) -L . -T "_gnatprove_standard.Integer" -o realize -D $(WHY3DIR)/drivers/coq-realize.drv

check: $(SUBDIR)/Integer.v
	# need an extra level of (..) here because we change to the subdir
	cd $(SUBDIR) && coqc -R $(SPARKDEV)/../why3/lib/coq Why3 Integer.v
