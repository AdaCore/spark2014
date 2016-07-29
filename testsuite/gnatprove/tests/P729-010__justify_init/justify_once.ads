with Private_Type; use Private_Type;
package Justify_Once with SPARK_Mode is
   type My_Array is array (Positive range <>) of Fully_Init;

   type My_Kind is (One, Two, Three, Four);

   function Test (K : My_Kind) return My_Array;

   function Test return Fully_Init;

   procedure Check_Init (A : My_Array) is null with Ghost;

   procedure Check_Init (P : Fully_Init) is null with Ghost;
end Justify_Once;
