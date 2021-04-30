private with System;

with Interfaces;

package Foo
with
   SPARK_Mode => On,
   Abstract_State => (State with External => Async_Readers),
   Initializes    => State
is

   type Bar_Type is new Interfaces.Unsigned_64;

   function Get return Bar_Type
   with
      Global => (Input => State);

   procedure Set (Value : Bar_Type)
   with
      Global  => (In_Out => State),
      Depends => (State  =>+ Value);

private

   Instance : Bar_Type
   with
      Import,
      Volatile,
      Async_Readers,
      Part_Of => State,
      Size    => 8 * 8,
      Address => System'To_Address (16#1234_5678#);

end Foo;
