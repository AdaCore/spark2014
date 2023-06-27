package Local_Variable_Subp is
   function Aux return Boolean with Import;
   function Func return Boolean with Post => Aux;
end Local_Variable_Subp;
