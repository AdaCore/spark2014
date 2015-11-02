package PO_T9 is
   protected P_Int is
      function Get return Integer;

      procedure Allow_Increase with Pre => True;

      entry Increase;
   private
      Condition : Boolean := True;
      The_Protected_Int : Integer := 0;
   end P_Int;
end PO_T9;
