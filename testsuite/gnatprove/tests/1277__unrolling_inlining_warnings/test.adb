procedure Test is

   procedure P is
   begin
      for I in 1 .. 100 loop
         null;
      end loop;
   exception
      when others =>
         null;
   end P;

   procedure Q is
   begin
      for I in 1 .. 2 loop
         null;
      end loop;
   end Q;

begin
   P;
   Q;
end Test;
