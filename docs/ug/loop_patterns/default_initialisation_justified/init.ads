with Loop_Types; use Loop_Types;
package Init
  with SPARK_Mode
is

   procedure Default_Initialize (A : out Arr_T; Init_Val : in Component_T) with
     --  every element of the output array has been initialized:
     Post => (for all J in A'Range => A (J) = Init_Val);
   pragma Annotate (GNATprove, False_Positive,
                    "might not be initialized",
                    "A is initialized for A'Range by Default_Initialize");

end Init;
