package body Use_Generic with
  SPARK_Mode => Off
is
   type T is access Integer;

   --  this generic instance is not analyzed
   package G2 is new Exclude_Generic_Unit_Body (T);

   procedure Do_Nothing is
   begin
      null;
   end Do_Nothing;

end Use_Generic;
