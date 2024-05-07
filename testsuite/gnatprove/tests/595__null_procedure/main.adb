procedure Main with SPARK_Mode is
   procedure P (X : out Positive) is null; -- @INITIALIZED:CHECK

   X : Positive;
begin
   P (X);
   pragma Assert (X > 0);
end Main;
