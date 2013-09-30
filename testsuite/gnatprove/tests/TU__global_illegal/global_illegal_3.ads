package Global_Illegal_3
  with SPARK_Mode
is
   pragma Elaborate_Body (Global_Illegal_3);

   X, Y, Z : Integer := 0;

   type Array_T is array (1 .. 10) of Integer;

   Arr  : Array_T := Array_T'(others => 0);
   Arr2 : Array_T;
end Global_Illegal_3;
