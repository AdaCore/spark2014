
package body Unknown_1
   with Refined_State => (Hidden_State => State)
is
   pragma SPARK_Mode;

   type State_T is range -20 .. 20;

   State : State_T;



   procedure Procedure_1 (input_parameter : in Types.Float_2_T)
     with Refined_Global => (In_Out => State)
   is

      function function_1 return Types.Record_T
        with Global => (Input => input_parameter)

      is
         Box : Types.Record_T;
      begin
         Box := Types.Record_T'
           (A => 0.0,
            B   => 0,
            C   => 0,
            D   => 0,
            E   => 0);

         return Box;

      end function_1;

      procedure Procedure_2
        with Global => (In_Out => State)
      is


         function function_2 return Boolean
         is
         begin
               declare
                  Record_var : constant Types.Record_T
                                            := function_1;
               begin
                  return Types.Float_1_T
                           (Record_var.C)
                         <= Types.Float_1_T
                             (Record_var.B);
               end;

         end function_2;

      begin
         if function_2
         then
            State := 1;
         end if;
      end Procedure_2;


   begin
      Procedure_2;
   end Procedure_1;

end Unknown_1;
