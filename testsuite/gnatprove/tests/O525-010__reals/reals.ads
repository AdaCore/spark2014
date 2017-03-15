package Reals
  with SPARK_Mode, Ghost
is
   --  Package Reals is not implemented. Instead, an axiomatization of real
   --  operations is directly given in Why3, to use in GNATprove.
   pragma Annotate (GNATprove, External_Axiomatization);

   type Real is private;

   Zero : constant Real;

   function "+" (X, Y : Real) return Real
     with Import;

   function "-" (X, Y : Real) return Real
     with Import;

   function "*" (X, Y : Real) return Real
     with Import;

   pragma Warnings (Off, "check would fail at run time",
     Reason => "Compiler warns that precondition cannot pass" &
               "at run time, because Real is a singleton type." &
               "This is ok as operation cannot be executed.");
   function "/" (X, Y : Real) return Real
     with Import,
          Pre => Y /= Zero;
   pragma Warnings (On, "check would fail at run time");

   function "<" (X, Y : Real) return Boolean
     with Import;

   function "<=" (X, Y : Real) return Boolean
     with Import;

   function ">=" (X, Y : Real) return Boolean
     with Import;

   function ">" (X, Y : Real) return Boolean
     with Import;

private
   pragma SPARK_Mode (Off);

   --  The actual type used for type Real does not matter. Since the private
   --  part of package Reals is marked SPARK_Mode (Off), GNATprove treats type
   --  Real as an abstract type.
   type Real is null record;

   Zero : constant Real := (null record);

end Reals;
