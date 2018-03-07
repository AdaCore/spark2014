package body Task_Limit is

   protected body Task_Count_Type is
      procedure Increment
        with Refined_Post => Foo'Old <= Foo
      is
      begin
         if Foo < Integer'Last then
            Foo := Foo + 1;
         end if;
      end Increment;
      procedure Increment_2
        with Refined_Post => Foo'Old <= Foo
      is
      begin
         Increment;
      end Increment_2;
   end Task_Count_Type;

   protected body Task_Count_Type_2 is
      procedure Increment
        with Refined_Post => Foo_2'Old <= Foo_2
      is
      begin
         if Foo_2 < Integer'Last then
            Foo_2 := Foo_2 + 1;
         end if;
      end Increment;
      procedure Increment_2
        with Refined_Post => Foo_2'Old <= Foo_2
      is
      begin
         Increment;
      end Increment_2;
   end Task_Count_Type_2;

end Task_Limit;
