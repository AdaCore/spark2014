package body External with SPARK_Mode is

   procedure Create (X : out T) is
   begin
      Reentrancy.Create (X);  --  @INVARIANT_CHECK:NONE
   end Create;

   procedure Update (X : in out T) is
   begin
      Reentrancy.Update (X);  --  @INVARIANT_CHECK:NONE
   end Update;

   function Get (X : T) return Integer is
     (Reentrancy.Get (X));  --  @INVARIANT_CHECK:NONE

end External;
