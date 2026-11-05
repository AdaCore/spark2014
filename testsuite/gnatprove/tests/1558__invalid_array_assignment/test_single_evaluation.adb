procedure Test_Single_Evaluation with SPARK_Mode is
   type State is record
      Count : Natural;
   end record;

   function Read (Count : in out Natural) return Boolean with
     Side_Effects,
     Pre => Count < Natural'Last,
     Post => Count = Count'Old + 1 and then Read'Result;

   function Read (Count : in out Natural) return Boolean is
   begin
      Count := Count + 1;
      return True;
   end Read;

   S : State := (Count => 0);
   X : Boolean with Potentially_Invalid;
begin
   X := Read (S.Count);
   pragma Assert (X);
   pragma Assert (S.Count = 1);
   pragma Assert (S.Count = 2); --  @ASSERT:FAIL
end Test_Single_Evaluation;
