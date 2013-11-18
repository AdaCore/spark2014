package Update_Uninitialized
  with SPARK_Mode
is
   type Arr_Range is range 1 .. 3;

   type Arr_T is array (Arr_Range) of Integer;

   procedure LHS_Uninitialized (Choise  : in     Integer;
                                Element :    out Arr_Range;
                                Arr     : in out Arr_T);

   procedure RHS_Uninitialized (Choise  : in     Integer;
                                Element :    out Arr_Range;
                                Arr     : in out Arr_T);
end Update_Uninitialized;
