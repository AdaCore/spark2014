package T1Q3_Alt
is

  type Day is (Mon, Tue, Wed, Thu, Fri, Sat, Sun);

  procedure Swap(X,Y: in out Integer)
    with Post => ((X = Y'Old) and (Y = X'Old));
  --# derives X from Y & Y from X;
  --# post X = Y~ and Y = X~;

  procedure NandGate(P,Q: in Boolean; R: out Boolean)
    with Post => ((if ((not P) and (not Q)) then R) and
    (if ((not P) and Q) then R) and
    (if (P and (not Q)) then R) and
    (if (P and Q) then (not R)));
  --# derives R from P, Q;
  --# post ( ((not P) and (not Q)) -> R    ) and
  --#      ( ((not P) and    Q   ) -> R    ) and
  --#      ( (   P    and (not Q)) -> R    ) and
  --#      ( (   P    and    Q   ) -> not R);
  --  The above is the truth table for "A nand B"

  procedure NextDay_A(Today: in Day; Tomorrow: out Day)
    with Post => ((if (Today=Mon) then Tomorrow=Tue) and
    (if (Today=Tue) then Tomorrow=Wed) and
    (if (Today=Wed) then Tomorrow=Thu) and
    (if (Today=Thu) then Tomorrow=Fri) and
    (if (Today=Fri) then Tomorrow=Sat) and
    (if (Today=Sat) then Tomorrow=Sun) and
    (if (Today=Sun) then Tomorrow=Mon));
  --# derives Tomorrow from Today;
  --# post (Today=Mon -> Tomorrow=Tue) and
  --#      (Today=Tue -> Tomorrow=Wed) and
  --#      (Today=Wed -> Tomorrow=Thu) and
  --#      (Today=Thu -> Tomorrow=Fri) and
  --#      (Today=Fri -> Tomorrow=Sat) and
  --#      (Today=Sat -> Tomorrow=Sun) and
  --#      (Today=Sun -> Tomorrow=Mon);

  procedure NextDay_B(Today: in Day; Tomorrow: out Day)
    with Post => ((if (Today=Mon) then Tomorrow=Tue) and
    (if (Today=Tue) then Tomorrow=Wed) and
    (if (Today=Wed) then Tomorrow=Thu) and
    (if (Today=Thu) then Tomorrow=Fri) and
    (if (Today=Fri) then Tomorrow=Sat) and
    (if (Today=Sat) then Tomorrow=Sun) and
    (if (Today=Sun) then Tomorrow=Mon));
  --# derives Tomorrow from Today;
  --# post (Today=Mon -> Tomorrow=Tue) and
  --#      (Today=Tue -> Tomorrow=Wed) and
  --#      (Today=Wed -> Tomorrow=Thu) and
  --#      (Today=Thu -> Tomorrow=Fri) and
  --#      (Today=Fri -> Tomorrow=Sat) and
  --#      (Today=Sat -> Tomorrow=Sun) and
  --#      (Today=Sun -> Tomorrow=Mon);

end T1Q3_Alt;
