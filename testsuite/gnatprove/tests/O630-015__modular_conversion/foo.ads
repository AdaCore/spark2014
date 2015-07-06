with Interfaces;

package Foo
with
   SPARK_Mode,
   Abstract_State => State
is

   type Field_Type is new Natural range 0 .. 4;

   procedure Init
   with
      Global => (Output => State),
      Depends => (State => null);

   procedure Get
     (Field :     Field_Type;
      Data  : out Interfaces.Unsigned_64)
   with
      Global  => (Input => State),
      Depends => (Data  => (Field, State));

end Foo;
