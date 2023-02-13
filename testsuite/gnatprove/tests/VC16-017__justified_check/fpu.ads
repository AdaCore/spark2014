package FPU
with
   Abstract_State => State,
   Initializes    => State
is
   pragma Elaborate_Body;

   type Subject_FPU_State_Array is array (1 .. 10) of Integer;

private
   Subject_FPU_States : Subject_FPU_State_Array
   with
      Part_Of => State;
   pragma Annotate
     (GNATprove, Intentional,
      "not initialized",
      "Subject FPU states are initialized by their owning CPU.");

end FPU;
