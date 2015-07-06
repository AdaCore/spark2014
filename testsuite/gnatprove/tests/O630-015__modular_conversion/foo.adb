package body Foo
with
   SPARK_Mode,
   Refined_State => (State => Value)
is

   use type Interfaces.Unsigned_64;

   Value : array (Field_Type) of Interfaces.Unsigned_64;

   -------------------------------------------------------------------------

   procedure Init
   with
      Refined_Global  => (Output => Value),
      Refined_Depends => (Value  => null)
   is
   begin
      Value := (others => 0);
   end Init;

   -------------------------------------------------------------------------

   procedure Get
     (Field :     Field_Type;
      Data  : out Interfaces.Unsigned_64)
   with
      Refined_Global  => (Input => Value),
      Refined_Depends => (Data  => (Field, Value)),
      Refined_Post    => Data = Value (Field)
   is
   begin
      Data := Value (Field);
   end Get;

end Foo;
