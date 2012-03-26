package body C is

   procedure P (X : Integer) is
   begin
      pragma Assert (X >= 1);
   end P;

end C;
