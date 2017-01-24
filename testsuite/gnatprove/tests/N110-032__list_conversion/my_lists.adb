package body My_Lists is
   pragma SPARK_Mode (On);

   procedure P is
      L1 : List (100);
      L2 : C_List1 := L1;
      L3 : C_List2;
      L4 : C_List11;
      L5 : C_List12;
      L6 : C_List21;
      L7 : C_List22;
   begin
      Clear (L1);
      Clear (L2);
      Clear (L3);
      Clear (L4);
      Clear (L5);
      Clear (L6);
      Clear (L7);
      pragma Assert (L1.Capacity = 100);
      pragma Assert (L2.Capacity = 100);
      pragma Assert (L3.Capacity = 100);
      pragma Assert (L4.Capacity = 100);
      pragma Assert (L5.Capacity = 100);
      pragma Assert (L6.Capacity = 100);
      pragma Assert (L7.Capacity = 100);
   end P;

end My_Lists;
