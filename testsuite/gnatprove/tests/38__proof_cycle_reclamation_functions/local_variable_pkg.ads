package Local_Variable_Pkg is
   function Aux return Boolean with Import;
   function Func return Boolean with Post => Aux;
end Local_Variable_Pkg;
