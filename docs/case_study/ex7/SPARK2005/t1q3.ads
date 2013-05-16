package T1Q3
is

  type Day is (Mon, Tue, Wed, Thu, Fri, Sat, Sun);

  procedure Swap(X,Y: in out Integer);
  --# derives X from Y & Y from X;
  --# post X = Y~ and Y = X~;

  procedure NandGate(P,Q: in Boolean; R: out Boolean);
  --# derives R from P, Q;
  --# post ( ((not P) and (not Q)) -> R    ) and
  --#      ( ((not P) and    Q   ) -> R    ) and
  --#      ( (   P    and (not Q)) -> R    ) and
  --#      ( (   P    and    Q   ) -> not R);
  --  The above is the truth table for "A nand B"

  procedure NextDay_A(Today: in Day; Tomorrow: out Day);
  --# derives Tomorrow from Today;
  --# post (Today=Mon and Tomorrow=Tue) or
  --#      (Today=Tue and Tomorrow=Wed) or
  --#      (Today=Wed and Tomorrow=Thu) or
  --#      (Today=Thu and Tomorrow=Fri) or
  --#      (Today=Fri and Tomorrow=Sat) or
  --#      (Today=Sat and Tomorrow=Sun) or
  --#      (Today=Sun and Tomorrow=Mon);

  procedure NextDay_B(Today: in Day; Tomorrow: out Day);
  --# derives Tomorrow from Today;
  --# post (Today=Mon and Tomorrow=Tue) or
  --#      (Today=Tue and Tomorrow=Wed) or
  --#      (Today=Wed and Tomorrow=Thu) or
  --#      (Today=Thu and Tomorrow=Fri) or
  --#      (Today=Fri and Tomorrow=Sat) or
  --#      (Today=Sat and Tomorrow=Sun) or
  --#      (Today=Sun and Tomorrow=Mon);

end T1Q3;
