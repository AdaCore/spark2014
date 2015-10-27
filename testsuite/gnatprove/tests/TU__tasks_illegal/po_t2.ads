package PO_T2 is

   --  TU: 4. A protected type shall define full default initialization. A
   --  variable whose Part_Of aspect specifies a task unit or protected unit
   --  shall be of a type which defines full default initialization, or shall
   --  be declared with an initial value expression, or shall be imported.

   protected P_Int is
      function Get return Integer;

      entry Set (X : Integer);
   private
      Condition : Boolean  --  This should be initialized.
        with Part_Of => P_Int;
   end P_Int;

   The_Protected_Int : Integer := 0;


end PO_T2;
