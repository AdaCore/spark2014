package P is

   --  This is not a volatile function; a warning would be nice
   function Func_1 return Integer with
     Volatile_Function;

end P;
