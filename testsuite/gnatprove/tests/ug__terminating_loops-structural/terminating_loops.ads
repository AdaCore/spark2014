package Terminating_Loops with
  SPARK_Mode
is
   type Cell;
   type List is access Cell;
   type Cell is record
      Value : Integer;
      Next  : List;
   end record;

   procedure Set_All_To_Zero (L : List);

end Terminating_Loops;
