package body u5 is

   X : Positive;
   Y : Positive;

   procedure s5_1 is
   begin
      null;
   end s5_1;

   procedure s5_2 is
      L : Positive := Positive'First;
      M : Positive := Positive'First;
   begin

      X := Positive'First;
      Y := Positive'First;

      for I in 1..50 loop
         for J in 1..50 loop
            for K in 1..50 loop

               -- Medium message for the following line
               L := Positive'Succ(L);

               -- Low message for the following line
               M := M + 1;

            end loop;
         end loop;
      end loop;

      X := L;
      Y := M;

   end s5_2;

end u5;
