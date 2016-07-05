package My_Package with SPARK_Mode is
   type Nat_Array is array (Positive range <>) of Natural;

   type Stack is private with Default_Initial_Condition;

   procedure Search (A      : Nat_Array;
                     E      : Natural;
                     Found  : out Boolean;
                     Result : out Positive);
   pragma Annotate
     (GNATprove, Intentional, """Result"" might not be initialized",
      "Result is always initialized when Found is True and never read otherwise");

   pragma Warnings
     (Off, "subprogram ""Test"" has no effect",
      Reason => "Test was only written to demonstrate GNATprove's capabilities");

   procedure Test;

   pragma Warnings
     (On, "subprogram ""Test"" has no effect");

private
   Max : constant := 100;
   type Stack is record
      Size    : Natural := 0;
      Content : Nat_Array (1 .. Max);
   end record;
   pragma Annotate
     (GNATprove, Intentional, """Stack"" is not fully initialized",
      String'("The only indices that can be accessed in a stack are those"
        & " smaller than Size. These indices will always have been"
        & " initialized when Size is increased."));
end My_Package;
