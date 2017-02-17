package body P is

   procedure S (A : Natural)
   is
   begin
      for J in 1 .. A loop
         declare
            Col : constant Integer := 0;
         begin
            for K in 1 .. A loop
              null;
            end loop;
         end;
      end loop;
   end S;

end P;
