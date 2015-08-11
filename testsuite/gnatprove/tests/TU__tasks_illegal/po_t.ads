package PO_T is

   --  4. A protected type shall define full default initialization. A
   --  variable whose Part_Of aspect specifies a task unit or protected unit
   --  shall be of a type which defines full default initialization, or shall
   --  be declared with an initial value expression, or shall be imported.

   protected P_Int is
      function Get return Integer;

      entry Set (X : Integer);
   private
      The_Protected_Int : Integer;  --  This should be initialized.
   end P_Int;

   Condition : Boolean := True
     with Part_Of => P_Int;

end PO_T;
