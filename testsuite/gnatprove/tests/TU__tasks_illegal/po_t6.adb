package body PO_T6 is
   protected body P_Int is
      function Get return Integer is
         (if The_Protected_Int >= 0
          then The_Protected_Int
          else The_Protected_Int + 10);

      entry Set (X : Integer) when Condition is
      begin
         The_Protected_Int := X;
      end Set;
   end P_Int;
end PO_T6;
