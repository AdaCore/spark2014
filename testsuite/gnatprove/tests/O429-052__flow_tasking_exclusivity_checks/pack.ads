package pack is

   function F return Natural is (5);

   task type T1;
   task type T2;

   protected type P is
   end P;

   type var_array_of_tasks is array (0 .. F) of T1;
   type var_array_of_pos   is array (0 .. F) of P;

   TA : array (0 .. F) of T1;
   PA : array (0 .. F) of P;

   type rec_with_var_array_of_tasks is
      record
        RT1 : T1;
        RT2 : T2;
        VT  : var_array_of_tasks;
        VP  : var_array_of_pos;
      end record with Volatile;

   R : rec_with_var_array_of_tasks;

end pack;
