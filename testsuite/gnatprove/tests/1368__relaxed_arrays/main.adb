procedure Main with SPARK_Mode is

   --  Test that we know that from_wrapper (to_wrapper x) is logically equal
   --  to x on arrays.

   type A is array (Positive range 1 .. 10) of Integer;

   function F (X : A) return Boolean with
     Global => null,
     Import;

   type R is record
      F : A;
   end record;

   procedure Write (X : in out R; Y : A) with
     Relaxed_Initialization => X,
     Pre => F (Y),
     Post => F (X.F); --@POSTCONDITION:PASS

   procedure Write (X : in out R; Y : A) is
   begin
      X.F := Y;
   end Write;

begin
   null;
end Main;
