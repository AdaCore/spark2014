procedure Recursion with Annotate => (GNATprove, Always_Return) is
   package Pack is
      procedure P with Annotate => (GNATprove, Always_Return);
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
