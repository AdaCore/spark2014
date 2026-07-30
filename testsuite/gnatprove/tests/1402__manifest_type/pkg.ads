package Pkg
  with SPARK_Mode
is

   --  A private type carries its own proof obligations (here the check that
   --  the default value satisfies the Default_Initial_Condition), which are
   --  proved in a translation keyed on the type itself.

   type T is private with Default_Initial_Condition => Is_Valid (T);

   function Is_Valid (X : T) return Boolean;

   procedure Reset (X : out T)
   with Post => Is_Valid (X);

private

   type T is record
      Lo : Integer := 0;
      Hi : Integer := 5;
   end record;

   function Is_Valid (X : T) return Boolean
   is (X.Lo <= X.Hi);

end Pkg;
