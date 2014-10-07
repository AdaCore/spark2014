with Types;

package Unknown_1
  with Abstract_State => Hidden_State
is
   pragma Spark_Mode;

   procedure Procedure_1 (input_parameter : in     Types.Float_2_T)
     with Global => (In_Out => Hidden_State);

end Unknown_1;
