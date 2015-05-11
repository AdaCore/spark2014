SUBDIR=realize
SPARKDEV=$(realpath ../../../)
WHY3DIR=$(SPARKDEV)/why3
WHY3=$(WHY3DIR)/bin/why3realize.opt
REALIZED=Integer Int_Power Int_Minmax Int_Abs Int_Division
FILE_NAMES=$(addsuffix .v, $(REALIZED))
COQ_FILES=$(addprefix $(SUBDIR)/, $(FILE_NAMES))

all: $(COQ_FILES)

$(SUBDIR)/%.v: _gnatprove_standard.mlw
	$(WHY3) -L . -T '_gnatprove_standard.$(basename $(notdir $@))' -o realize -D $(WHY3DIR)/drivers/coq-realize.drv

check: $(COQ_FILES)
	# need an extra level of (..) here because we change to the subdir
	cd $(SUBDIR) && for FILE in $(FILE_NAMES); do coqc -R $(SPARKDEV)/why3/lib/coq Why3 $$FILE; done
