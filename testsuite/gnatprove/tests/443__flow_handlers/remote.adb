package body Remote is

   U : Boolean := True; -- U is not synchronized, it should not be accessed by handlers

   procedure P is
   begin
      U := not U;
   end;

   function F return Boolean is
   begin
      U := not U;
      return U;
   end F;

   package Hidden with SPARK_Mode => Off is
      X : access Boolean := new Boolean'(True) with Atomic;
   end;

   procedure Heap with SPARK_Mode => Off is
   begin
      Hidden.X.all := not Hidden.X.all;
   end;

end Remote;
