package Stacks is pragma SPARK_Mode (Off);  --  tagged types

   type Stack (Max : Positive) is tagged private;

   function Is_Empty (S : Stack) return Boolean;

private

   type Stack (Max : Positive) is tagged record
      Top  : Natural := 0;
   end record;

   function Is_Empty (S : Stack) return Boolean is (S.Max = 0);
end Stacks;
