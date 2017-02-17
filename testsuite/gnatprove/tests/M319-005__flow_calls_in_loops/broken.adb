package body Broken is
   I : Integer := 0;

   procedure Do_Stuff (N : Integer)
   is
   begin
      I := I + N;
   end Do_Stuff;

   procedure Test_01
   is
   begin
      for I in 1 .. 10 loop
         Do_Stuff (I);
      end loop;
   end Test_01;

   procedure Test_02
   is
   begin
      loop
         Do_Stuff (I);
      end loop;
   end Test_02;


end Broken;
