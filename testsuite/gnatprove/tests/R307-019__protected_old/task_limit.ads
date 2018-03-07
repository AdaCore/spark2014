package Task_Limit is
   protected type Task_Count_Type is
      procedure Increment with Global => null;
      procedure Increment_2 with Global => null;
   private
      Foo : Natural := 0;
   end Task_Count_Type;

   protected Task_Count_Type_2 is
      procedure Increment with Global => null;
      procedure Increment_2 with Global => null;
   end Task_Count_Type_2;

private
   Foo_2 : Natural := 0 with Part_Of => Task_Count_Type_2;
end Task_Limit;
