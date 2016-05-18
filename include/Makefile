ALL_CTX=$(wildcard proof/Coq/*/*.ctx)
ALL_COQ=$(sort $(patsubst %.ctx,%.v,$(ALL_CTX)))

%.v: %.ctx
	cpp -w -P -I proof/Coq/common -o $@ $<

clean:
	rm proof/Coq/*/*.v

generate: $(ALL_COQ)
