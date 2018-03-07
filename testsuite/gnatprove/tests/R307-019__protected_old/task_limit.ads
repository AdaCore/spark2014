package Task_Limit is
   protected type Task_Count_Type is
      procedure Increment with Global => null;
   private
      Foo : Boolean := True;
   end Task_Count_Type;
end Task_Limit;
