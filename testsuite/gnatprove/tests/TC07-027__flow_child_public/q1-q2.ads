package Q1.Q2 with Abstract_State => S2 --, Initializes => S2
  --  S2 is *not* fully initialized.
  --  However adding the above Initializes contract passes???
is
   procedure Dummy with Global => null;
end;
