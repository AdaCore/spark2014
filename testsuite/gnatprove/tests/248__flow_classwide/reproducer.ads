package Reproducer with
  SPARK_Mode
is

   --  A simple class hierarchy

   type Root is abstract tagged null record;

   function Is_Set (Ctx : Root) return Boolean is abstract;

   type Derived is new Root with private;

   overriding
   function Is_Set (Ctx : Derived) return Boolean;

   --  A simple wrapper around the Derived type

   type Wrapper is private;

   function Is_Set (Ctx : Wrapper) return Boolean;

   procedure Foo (Ctx : in out Wrapper);

private

   -------------
   -- Derived --
   -------------

   type Derived is new Root with record
      Is_Set : Boolean;
   end record;

   overriding
   function Is_Set  (Ctx : Derived) return Boolean is
     (Ctx.Is_Set);

   -------------
   -- Wrapper --
   -------------

   type Wrapper is record
      Inner_Ctx : Derived;
   end record;

   function Is_Set (Ctx : Wrapper) return Boolean is
     (Is_Set (Ctx.Inner_Ctx));

end Reproducer;
