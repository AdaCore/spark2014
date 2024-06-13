with Ada.Text_IO;  use Ada.Text_IO;

procedure FLB_Multidimensional_Subtypes is

   type Matrix is array (Integer range <>, Integer range <>) of Integer;

   subtype FLB_0_Matrix is Matrix (0 .. <>, 0 .. <>);

   subtype FLB_1_Matrix is Matrix (1 .. <>, 1 .. <>);

   procedure Proc_FLB_0 (A : in out FLB_0_Matrix) is
   begin
      pragma Assert (A'first(1) = 0 and A'first(2) = 0);

      Put_Line ("A'first(1) =" & A'first(1)'Image);
      Put_Line ("A'last(1)  =" & A'last(1)'Image);
      Put_Line ("A'first(2) =" & A'first(2)'Image);
      Put_Line ("A'last(2)  =" & A'last(2)'Image);

      A(0, A'last(2)) := A(2, A'last(2));
   end Proc_FLB_0;

   procedure Proc_FLB_1 (A : in out FLB_1_Matrix) is
   begin
      pragma Assert (A'first(1) = 1 and A'first(2) = 1);

      Put_Line ("A'first(1) =" & A'first(1)'Image);
      Put_Line ("A'last(1)  =" & A'last(1)'Image);
      Put_Line ("A'first(2) =" & A'first(2)'Image);
      Put_Line ("A'last(2)  =" & A'last(2)'Image);

      A(1,2) := A(3,4);
   end Proc_FLB_1;

   A10_x_20 : Matrix (3 .. 7, 8 .. 15);

   A_FLB_0_7_x_0_12 : FLB_0_Matrix (0 .. 7, 0 .. 12);

   A_FLB_1_10_x_20 : FLB_1_Matrix := A10_x_20;  -- Sliding implemented here

   A_1_5_x_3_16 : Matrix (1 .. 5, 3 .. 16);
   A_2_7_x_0_11 : Matrix (2 .. 7, 0 .. 11);

begin
   Proc_FLB_0 (A_FLB_0_7_x_0_12);
   Proc_FLB_0 (A10_x_20);      -- Sliding implemented here
   Proc_FLB_0 (A_2_7_x_0_11);  -- Sliding implemented here

   Proc_FLB_1 (A_FLB_1_10_x_20);
   Proc_FLB_1 (A10_x_20);       -- Sliding implemented here
   Proc_FLB_1 (A_1_5_x_3_16);   -- Sliding implemented here
end FLB_Multidimensional_Subtypes;
