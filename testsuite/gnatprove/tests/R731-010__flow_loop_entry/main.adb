procedure Main is

   X : Integer := 1;

   procedure Test is
   begin
      for J in 1 .. 5 loop
         pragma Assert (J >= X'Loop_Entry);
      end loop;
   end;
begin
   Test;
end;
