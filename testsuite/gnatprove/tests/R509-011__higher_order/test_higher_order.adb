
package body Test_Higher_Order with SPARK_Mode is

   procedure Test1 is
   begin
      pragma Assert (Sum_L.Sum (A => (1, 2, 3, 4, 5, 6, 7, 1, 1)) = 30);
   end Test1;

   procedure Test2 is
   begin
      pragma Assert (Cnt.Count (A => (1, -2, 3, -4, -5, 6, 7, 13, 0)) = 6);
   end Test2;

   procedure Test3 is
   begin
      pragma Assert (Sum2_L.No_Overflows (A => (1 => (1, 2, 3, 4, 5, 6, 7),
                                                2 => (1, 2, 3, 4, 5, 6, 7))));

      pragma Assert (Sum2_L.Sum (A => (1 => (1, 2, 3, 4, 5, 6, 7),
                                       2 => (1, 2, 3, 4, 5, 6, 7))) = 56);
   end Test3;

   procedure Test4 is
   begin
      pragma Assert (Cnt2.Count (A => (1 => (1, -2, 3, -4, -5, 6, 7, 13, 0),
                                       2 => (1, -2, 3, -4, -5, 6, 7, 13, 0),
                                       3 => (1, -2, 3, -4, -5, 6, 7, 13, -1))) = 17);
   end Test4;
end Test_Higher_Order;
