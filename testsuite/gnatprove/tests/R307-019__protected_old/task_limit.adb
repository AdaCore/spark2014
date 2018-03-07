package body Task_Limit is

   protected body Task_Count_Type is
      procedure Increment
        with Refined_Post => Foo'Old
      is
      begin
         null;
      end Increment;
   end Task_Count_Type;

end Task_Limit;
