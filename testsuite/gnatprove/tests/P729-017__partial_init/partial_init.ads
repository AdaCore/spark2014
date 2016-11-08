package Partial_Init
  with Initializes => G
is

   type A is array (Integer range <>) of Integer;

   type T is record
      X : Integer := 0;
      Y : A(1..10);
   end record;

   G : T;

   procedure Create (V : out T);
   function Create return T;

end Partial_Init;
