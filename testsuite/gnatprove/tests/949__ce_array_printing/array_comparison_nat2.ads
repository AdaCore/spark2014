package Array_Comparison_Nat2 is

   pragma Warnings (Off, "subprogram * has no effect");

   type Natural_Array is array (Integer range <>) of Natural;
   type Natural_Array_2D is
     array (Integer range <>, Integer range <>) of Natural;
   type Natural_Array_Array4 is
     array (Integer range <>) of Natural_Array (1 .. 4);

   procedure P_Nat (I : Integer);

end Array_Comparison_Nat2;
