package Unsound with
   SPARK_Mode => On
is

   subtype My_Range_Type is Natural range 1 .. 10;

   type My_Array_Type is array (My_Range_Type) of Boolean;

   function Find_False (My_Array : My_Array_Type) return My_Range_Type with
      Annotate => (GNATprove, Terminating);

end Unsound;
