package body PO_T2 is

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

begin
   P_Int.Set (-10);
   pragma Assert (P_Int.Get = 0);
end PO_T2;
