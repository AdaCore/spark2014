package body Simple_Illegal_With_Contracts is
   procedure P (Par : in out Level_0_T) is
   begin
      pragma Assert (PI = 0);
      if Par.D = 0 then
         Par.Extra := 0;
      end if;
      IO := I + IO;
      O  := IO;
   end P;

   procedure P (Par : in out Level_1_1_T) is
   begin
      if Par.D = PI then
         Par.Extra := 0;
      end if;
      IO := I + IO;
      O  := IO;
   end P;

   procedure P (Par : in out Level_1_2_T) is
   begin
      pragma Assert (PI = 0);
      if Par.D = 0 then
         Par.Extra := 0;
      end if;
      I  := I + IO;
      IO := I;
      O  := IO;
   end P;

   procedure P (Par : in out Level_1_3_T) is
   begin
      pragma Assert (PI = 0);
      if Par.D = 0 then
         Par.Extra := 0;
      end if;
      I  := 0;
      IO := 0;
      O  := 0;
   end P;

   procedure P (Par : in out Level_1_T) is
   begin
      pragma Assert (PI = 0);
      if Par.D = 0 then
         Par.Extra := 0;
      end if;
      IO := I;
      O  := IO;
   end P;

   procedure P (Par : in out Level_2_1_T) is
   begin
      pragma Assert (PI = I);
      if Par.D = 0 then
         Par.Extra := 0;
      end if;
      O := 0;
   end P;
end Simple_Illegal_With_Contracts;
