package Task_In_Empty_Arrays is

   --  There are no instances of this task type
   task type TT;

   task type T1;

   --  Empty arrays
   A1 : array (1 .. 0) of TT;
   A2 : array (1 .. 0, 1 .. 0) of TT;
   A3 : array (1 .. 2, 1 .. 0) of TT;

   --  This one also is empty but with variable bound
   X : Positive;

   A4 : array (X .. 0) of TT;

end;
