package body DIC_Of_Cont with SPARK_Mode is
   procedure Main (Capacity : Count_Type) is
      Dlli : My_DLLI.List (Capacity);
      Dhama : My_HAMA.Map (Capacity, My_HAMA.Default_Modulus (Capacity));
      Dhase : My_HASE.Set (Capacity, My_HASE.Default_Modulus (Capacity));
      Dorma : My_ORMA.Map (Capacity);
      Dorse : My_ORSE.Set (Capacity);
      Dfove : My_FOVE.Vector (Capacity);
   begin
      pragma Assert (My_DLLI.Is_Empty (Dlli));
      pragma Assert (Dlli.Capacity = Capacity);
      pragma Assert (My_HAMA.Is_Empty (Dhama));
      pragma Assert (Dhama.Capacity = Capacity);
      pragma Assert (My_HASE.Is_Empty (Dhase));
      pragma Assert (Dhase.Capacity = Capacity);
      pragma Assert (My_ORMA.Is_Empty (Dorma));
      pragma Assert (Dorma.Capacity = Capacity);
      pragma Assert (My_ORSE.Is_Empty (Dorse));
      pragma Assert (Dorse.Capacity = Capacity);
      pragma Assert (My_FOVE.Is_Empty (Dfove));
      pragma Assert (Dfove.Capacity = Capacity);
   end Main;
end DIC_Of_Cont;
