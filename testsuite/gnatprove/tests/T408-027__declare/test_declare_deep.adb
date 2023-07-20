procedure Test_Declare_Deep with SPARK_Mode is
   type Int_Ptr is access Integer;

   function Create return Int_Ptr with Import,
     Post => Create'Result /= null and Create'Result.all <= 1000;

   procedure OK1 with Pre => True is
      X : Integer := 1;
      Y : constant Int_Ptr := Create; --@RESOURCE_LEAK_AT_END_OF_SCOPE:FAIL
   begin
      X := Y.all + X;
   end OK1;

   procedure OK2 with Pre => True is
      X : Integer := 1;
   begin
      declare
         Y : constant Int_Ptr := Create; --@RESOURCE_LEAK_AT_END_OF_SCOPE:FAIL
      begin
         X := Y.all + X;
      end;
   end OK2;

   X : Integer := 1;
begin
   null;
end Test_Declare_Deep;
