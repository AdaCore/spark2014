package body Uninitialized is
   procedure Compare is
      B : Integer;
   begin
      A := 100;
      pragma Assert (A > B);
   end Compare;
end Uninitialized;
