package body Loop_Related_Illegal_2
  with SPARK_Mode
is
   procedure Loop_Invariant_Acts_As_Cut_Point is
   --  TU: 1. Pragma Loop_Invariant is like a pragma Assert except it also acts
   --  as a *cut point* in formal verification. A cut point means that a prover
   --  is free to forget all information about modified variables that has been
   --  established within the loop. Only the given Boolean expression is
   --  carried forward.
      X : Integer := 10;
      Y : Integer;
   begin
      loop
         Y := 10;
         pragma Loop_Invariant (X >= 10 and X <= Integer'Last / 2);
         X := X * 2;
         exit when X > 10;
      end loop;
      pragma Assert (Y = 10);  --  This should not be provable
   end Loop_Invariant_Acts_As_Cut_Point;


   procedure Expression_Remains_The_Same (Par : Natural) is
   --  TU: 2. Pragma Loop_Variant is used to demonstrate that a loop will
   --  terminate by specifying expressions that will increase or decrease as
   --  the loop is executed.
      X : Natural := 0;
   begin
      loop
         pragma Loop_Invariant (X <= Natural'Last - Par);
         pragma Loop_Variant (Increases => X);
         --  The above should not be provable (Par = 0)
         X := X + Par;
         exit when X > 2000;
      end loop;
   end Expression_Remains_The_Same;
end Loop_Related_Illegal_2;
