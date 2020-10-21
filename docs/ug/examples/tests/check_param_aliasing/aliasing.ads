package Aliasing with
  SPARK_Mode
is
   Glob : Integer;

   procedure Whatever (In_1, In_2 : Integer; Out_1, Out_2 : out Integer) with
     Global => Glob;

end Aliasing;
