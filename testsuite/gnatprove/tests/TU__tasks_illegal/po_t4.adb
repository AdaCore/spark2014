package body PO_T4 is
   protected body Protected_Int is
      procedure Set (X : Integer) is
      begin
         Safe_Int := X;
      end Set;

      function Get return Integer is (Safe_Int);
   end Protected_Int;
end PO_T4;
