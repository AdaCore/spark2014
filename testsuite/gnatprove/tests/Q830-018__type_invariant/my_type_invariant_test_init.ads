package My_Type_Invariant_Test_Init
  with SPARK_Mode => On,
       Initializes => null  --  @INITIALIZES:CHECK
is
   pragma Elaborate_Body;

   type My_Type is private;

   procedure Test;

private

   type My_Type is
      record
         My_Field : Boolean := True;
      end record
   with Type_Invariant => My_Field = True;

   Bar : My_Type := (My_Field => True);

   Bad : My_Type := (My_Field => False);

end My_Type_Invariant_Test_Init;
