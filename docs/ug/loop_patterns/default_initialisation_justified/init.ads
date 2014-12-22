package Init
  with SPARK_Mode
is
   Max_Seq_Length : constant Natural := 1000;

   subtype Index_T is Natural range 1 .. Max_Seq_Length;

   subtype Component_T is Positive;

   type Arr_T is array (Index_T range <>) of Component_T;

   procedure Default_Initialize (A : out Arr_T; Init_Val : in Component_T) with
     --  every element of the output array has been initialized:
     Post => (for all J in A'Range => A (J) = Init_Val);
   pragma Annotate (GNATprove, False_Positive,
                    "might not be initialized",
                    "A is initialized for A'Range by Default_Initialize");

end Init;
