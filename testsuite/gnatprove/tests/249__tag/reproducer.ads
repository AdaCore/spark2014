package Reproducer with
  Pure,
  SPARK_Mode
is

   --  A simple class hierarchy

   type Root is abstract tagged null record;

   type Derived is new Root with private;

   --  A simple wrapper around the Derived type

   type Wrapper is private;

   procedure Foo (Ctx : Wrapper);

private

   -------------
   -- Derived --
   -------------

   type Derived is new Root with record
      Is_Set_F : Boolean;
   end record;

   -------------
   -- Wrapper --
   -------------

   type Wrapper is record
      Inner_Ctx : Derived;
   end record;

end Reproducer;
