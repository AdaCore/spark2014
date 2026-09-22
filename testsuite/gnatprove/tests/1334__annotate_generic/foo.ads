package Foo with SPARK_Mode is

   function Last return Integer is (Integer'Last) with Pre => True;

   --  Justification written as a pragma after a generic subprogram

   generic
   procedure Bar with Pre => Last + 1 = Last + 1, Import;
   pragma Annotate (GNATprove, Intentional, "overflow check", "Just a test");

   --  Justification written as an aspect on a generic subprogram

   generic
   procedure Baz with Pre => Last + 1 = Last + 1, Import,
     Annotate => (GNATprove, Intentional, "overflow check", "Just a test");

   --  Justification for a generic package

   generic
   package Gen is
      procedure Bar with Pre => Last + 1 = Last + 1, Import;
   end Gen;
   pragma Annotate (GNATprove, Intentional, "overflow check", "Just a test");

   --  Justification whose pattern does not match the check

   generic
   procedure Unrelated with Pre => Last + 1 = Last + 1, Import;
   pragma Annotate (GNATprove, Intentional, "range check", "Not applicable");

   --  Generic subprogram which is never instantiated

   generic
   procedure Never with Pre => Last + 1 = Last + 1, Import;
   pragma Annotate (GNATprove, Intentional, "overflow check", "Just a test");
end Foo;
