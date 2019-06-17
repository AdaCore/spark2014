package Foo with
  SPARK_Mode => On
is
   subtype Init_Char is Character;
   pragma Annotate (GNATprove, Init_By_Proof, Init_Char);

   type Init_String is array (Positive range <>) of Init_Char;

   procedure Read (Fd : Integer; Buf : out Init_String; Has_Read : out Integer);

   procedure Read_Str (Fd : Integer; Buf : out String; Has_Read : out Integer);

end Foo;
