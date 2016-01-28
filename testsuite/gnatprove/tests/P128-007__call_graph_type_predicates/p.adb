with Ada.Dispatching;

package body P
  with SPARK_Mode
is

   function Foo return Boolean;
   --  Potentially blocking

   ---------
   -- Foo --
   ---------

   function Foo return Boolean is
   begin
      Ada.Dispatching.Yield;
      return True;
   end Foo;

   type T is null record with Dynamic_Predicate => Foo;

   --------
   -- PO --
   --------

   protected body PO is
      entry E when True is
         X : T;
      begin
         null;
      end;
   end;

end P;
