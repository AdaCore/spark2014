with Loop_Types; use Loop_Types;
package Init
  with SPARK_Mode
is

   procedure Dynamic_Initialize (A : out Arr_T; Init_Val : in Component_T) with
     --  sufficiently strong precondition for calculation of dynamic expression:
     Pre  =>  Init_Val + A'Last <= Component_T'Last,
     --  every element of the output array has been initialized:
     Post =>  (for all J in A'Range => A (J) = Init_Val + J);

end Init;
