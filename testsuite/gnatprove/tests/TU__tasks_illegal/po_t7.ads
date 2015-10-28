package PO_T7 is
   Not_CAE : Boolean := True;

   function Get_Not_CAE return Boolean;

   protected P_Int is
      --  TU: 10. The precondition of a protected operation shall not reference
      --  a global variable, unless it is *constant after elaboration*.

      function Get return Integer
        with Pre => Not_CAE;  --  Problem

      procedure Increase
        with Pre => Get_Not_CAE;  --  Problem
   private
      The_Protected_Int : Integer := 0;
   end P_Int;
end PO_T7;
