with AA;  use AA;

package body A
  with SPARK_Mode,
    Refined_State => (Global_AS => Global_A)
is
   function Global_A_Initalized return Boolean is (Global_A'Valid_Scalars);

   procedure initGlobalsA(Status : out Natural) is
   begin
      Main_Body :
      for Unused_Loop_Var in 1..1 loop
         initGlobalsAA(Status);
         if Status /= 0 then
            exit Main_Body;
         end if;

         -- In produciton code, there are case where we have many
         -- call in a row like the above, to initalize "sub-object",
         -- and only if they all succeed does this "object"'s construction
         -- succeed.

         Global_A := 1;
         UseAA(Global_A);
      end loop Main_Body;
   end initGlobalsA;

   procedure UseA (X : in out Natural) is
   begin
      -- X := X + Global_Var;
      if X < Natural'Last - Global_A then
         X := X + Global_A;
      else
         X := 0;
      end if;
   end UseA;

end A;
