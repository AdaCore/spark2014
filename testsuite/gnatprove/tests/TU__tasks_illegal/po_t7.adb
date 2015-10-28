package body PO_T7 is
   function Get_Not_CAE return Boolean is
   begin
      return Not_CAE;
   end Get_Not_CAE;

   protected body P_Int is
      function Get return Integer is
         (if The_Protected_Int >= 0
          then The_Protected_Int
          else The_Protected_Int + 10);

      procedure Increase is
      begin
         if The_Protected_Int = Integer'Last then
            The_Protected_Int := Integer'First;
         else
            The_Protected_Int := The_Protected_Int + 1;
         end if;
      end Increase;
   end P_Int;
end PO_T7;
