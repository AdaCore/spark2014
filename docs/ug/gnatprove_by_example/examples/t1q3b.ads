package T1Q3B
is

  procedure NandGate(P,Q: in Boolean; R: out Boolean)
    with Post => ((if ((not P) and (not Q)) then R) and
    (if ((not P) and Q) then R) and
    (if (P and (not Q)) then R) and
    (if (P and Q) then (not R)));

end T1Q3B;
