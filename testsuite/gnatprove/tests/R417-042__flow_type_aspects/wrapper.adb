procedure Wrapper (Low, High : Integer) with Global => null is

   procedure Test1 with Global => (Proof_In => (Low, High)) is
      subtype T is Integer with Predicate => T in Low .. High;
      function Id (Arg : T) return Integer is (Arg) with Global => null;
      Y : Integer := Id (0);
   begin
      null;
   end;
begin
   Test1;
end;
