package My_Type_Invariant_Test
   with SPARK_Mode => On
is

   type My_Type is private;

   Foo : constant My_Type;

private

   type My_Type is
      record
         My_Field : Boolean;
      end record
   with Type_Invariant => True;

   Bar : My_Type := (My_Field => True);

   Baz : constant My_Type := (My_Field => True);

   Foo : constant My_Type := (My_Field => True);

end My_Type_Invariant_Test;
