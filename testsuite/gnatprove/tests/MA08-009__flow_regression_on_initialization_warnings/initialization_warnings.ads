package Initialization_Warnings
  with SPARK_Mode
is
   type Array_T is array (1 .. 10) of Integer;

   A : Array_T;
   V : Integer;

   procedure Init_Arr_Warn (An_Arr : out Array_T);

   procedure Init_Arr_Warn_2 (An_Arr : out Array_T; X : out Integer);

   procedure Init_Arr_Warn_3
     with Global => (Output => A);

   procedure Init_Arr_Warn_4
     with Global => (Output => (A, V));
end Initialization_Warnings;
