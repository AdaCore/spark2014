package Update
  with SPARK_Mode
is
   Max_Seq_Length : constant Natural := 1000;

   subtype Index_T is Natural range 1 .. Max_Seq_Length;

   subtype Component_T is Positive;

   type Arr_T is array (Index_T) of Component_T;

   procedure Array_Update (A : in out Arr_T;
                           First_Idx, Last_Idx: in Index_T;
                           New_Val : in Component_T) with
     Post =>  (for all J in First_Idx .. Last_Idx => A (J) = New_Val);

end Update;
