package PO_T6 is
   protected P_Int is
      function Get return Integer;

      entry Set (X : Integer);
   private
      Condition : Boolean := True;
   end P_Int;

   The_Protected_Int : Integer := 0
     with Part_Of => P_Int;
end PO_T6;
