package body PO_T9 is
   protected body P_Int is
      function Get return Integer is (The_Protected_Int);

      procedure Allow_Increase is
      begin
         Condition := True;
      end Allow_Increase;

      entry Increase when Condition is
      begin
         Condition := False;
         The_Protected_Int := The_Protected_Int + 1;
         Allow_Increase;
         Allow_Increase;
      end Increase;
   end P_Int;
end PO_T9;
