package Math with SPARK_Mode => On is

   -- Represents a vector in the stationary three phase reference frame
   type Stationary_3_Phase_Vector is record
      A : Float := 0.0;
      B : Float := 0.0;
      C : Float := 0.0;
   end record with Size => 96,
     Dynamic_Predicate => abs Stationary_3_Phase_Vector.A < 8.2
     and abs Stationary_3_Phase_Vector.B < 8.2
     and abs Stationary_3_Phase_Vector.C < 8.2;

   type Stationary_2_Phase_Vector is record
      Alfa : Float := 0.0;
      Beta : Float := 0.0;
   end record;

   function Clarke_Transform (Input : Stationary_3_Phase_Vector)
                              return Stationary_2_Phase_Vector with
     Inline,
     Global => null,
     Pre =>  abs Input.A < 8.2 and abs Input.B < 8.2 and abs Input.C < 8.2;

end Math;
