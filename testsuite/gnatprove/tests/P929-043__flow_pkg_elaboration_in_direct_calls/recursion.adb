procedure Recursion with Always_Terminates is
   package Pack is
      procedure P with Always_Terminates;
   end Pack;

   package body Pack is
      procedure P is
         A : Boolean := True;
      begin
         for I in 1 .. 3 loop
            Recursion; -- this call is not detected
            A := False;
         end loop;
      end P;
   begin
      P;
   end Pack;
begin
   null;
end Recursion;
