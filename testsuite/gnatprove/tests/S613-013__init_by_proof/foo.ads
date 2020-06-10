package Foo with
  SPARK_Mode => On
is
   type Init_String is array (Positive range <>) of Character with
     Relaxed_Initialization;

   procedure Read (Fd : Integer; Buf : out Init_String; Has_Read : out Integer);

   procedure Read_Str (Fd : Integer; Buf : out String; Has_Read : out Integer);

end Foo;
