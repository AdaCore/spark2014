package body Foo
with
   SPARK_Mode,
   Refined_State => (State => Value)
is


   Value : Natural := 0;

   -------------------------------------------------------------------------

   function Get_Data return Natural
   with
      Refined_Global => (Input => Value),
      Refined_Post   => Get_Data'Result = Value
   is
   begin
      return Value;
   end Get_Data;

   -------------------------------------------------------------------------

   procedure Set_Data (Data : Natural)
   with
      Refined_Global  => (Output => Value),
      Refined_Depends => (Value => Data),
      Refined_Post    => Value = Data
   is
   begin
      Value := Data;
   end Set_Data;

end Foo;
