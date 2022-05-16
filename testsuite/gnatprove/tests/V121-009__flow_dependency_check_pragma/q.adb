procedure Q (X1, X2 : Integer; Y1, Y2, Y3 : out Integer) with
   Depends => (Y1 => X1, Y2 => X2, Y3 => X2),
  --  Dependency contract is correct.
   Post => Y1 = X1 and Y2 = X2       --@POSTCONDITION:PASS
is
   type T is record
      C1 : Integer := X1;
      C2 : Integer := X2;
   end record;
begin
   --  Test checks that flow via box notation works
   --  as desired in the case of record components.
   Y1 := T'(C1 => <>, C2 => 1).C1;
   Y2 := T'(C1 => 1, others => <>).C2;
   --  Y3 "should" have an equivalent dependency to Y2
   --  however GNATProve's conservative approach means
   --  it thinks Y3 depends on X1
   Y3 := T'(others => <>).C2;

end Q;
