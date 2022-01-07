procedure Main with SPARK_Mode is

   package Nested is
      type T (D : Boolean) is private
      with Default_Initial_Condition => True;
   private
      pragma SPARK_Mode (Off);
      type T (D : Boolean) is record
         F : Integer := 22;
      end record;
   end Nested;
   use Nested;

   X : T (True) with Relaxed_Initialization;

begin
   pragma Assert (X'Initialized);
end;
