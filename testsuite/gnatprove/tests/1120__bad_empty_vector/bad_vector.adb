pragma Ada_2022;
with SPARK.Containers.Formal.Vectors;

procedure Bad_Vector with SPARK_Mode => On
is

   subtype Vector_Index_T is Natural range 0 .. 20;

   subtype The_Value is Positive;

   package Bounded_SPARK_Vector is new SPARK.Containers.Formal.Vectors
     (Index_Type   => Vector_Index_T,
      Element_Type => The_Value);

   use type Bounded_SPARK_Vector.Capacity_Range;

   The_Vec2 : Bounded_SPARK_Vector.Vector := Bounded_SPARK_Vector.Empty_Vector (Capacity => 50); -- @PRECONDITION:FAIL

begin
  null;
end Bad_Vector;
