package PO_T is
   CAE : Boolean := True
     with Constant_After_Elaboration;

   Not_CAE : Boolean := True;

   function Get_CAE return Boolean;

   function Get_Not_CAE return Boolean;

   protected P_Int is
      function Get return Integer
        with Pre => Not_CAE;  --  Problem

      procedure Increase
        with Pre => Get_Not_CAE;  --  Problem

      procedure Decrease
        with Pre => CAE and then Get_CAE;  --  OK
   private
      The_Protected_Int : Integer := 0;
   end P_Int;
end PO_T;
