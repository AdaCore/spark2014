package body Simple_Illegal_Without_Contracts is
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
      if Par.D = PI then  --  PROBLEM: PI cannot be an Input
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
      I  := I + IO;  --  PROBLEM: I cannot be an In_Out
      IO := I;
      O  := IO;
   end P;

   procedure P (Par : in out Level_1_3_T) is
   begin
      pragma Assert (PI = 0);
      if Par.D = 0 then
         Par.Extra := 0;
      end if;
      I  := 0;  --  PROBLEM: I cannot be an output
      IO := 0;
      O  := 0;
   end P;

   procedure P (Par : in out Level_1_T) is  --  ALL OK
   begin
      pragma Assert (PI = 0);
      if Par.D = 0 then
         Par.Extra := 0;
      end if;
      IO := I;
      O  := IO;
   end P;

   procedure P (Par : in out Level_2_1_T) is
      --  PROBLEM: IO has to be an output
   begin
      pragma Assert (PI = I);
      if Par.D = 0 then
         Par.Extra := 0;
      end if;
      O := 0;

   end P;
end Simple_Illegal_Without_Contracts;

