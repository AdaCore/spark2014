package Semantics is 

   function Ghost_Func return Integer
     with Convention => Ghost;
   --  Simple ghost function

   function Ren_Ghost_Func return Integer renames Ghost_Func;
   --  Renaming of a ghost function

   procedure Check_Assertion_Exprs (Formal : in out Integer)
     with Pre  => Formal = Ghost_Func,
          Post => Formal = Ren_Ghost_Func + 1,
          Contract_Cases => (Formal = 0 => Formal = Ghost_Func,
                             others     => Formal = Ren_Ghost_Func + 1);
   --  Check all legal calls to a ghost function in assertion expressions

   function Check_Within_Ghost_Function return Integer
     with Convention => Ghost;
   --  Check all legal calls to a ghost function from within another ghost
   --  function.

   function Non_Callable_Ghost_Function return Integer
     with Convention => Ghost, Import;
   --  Non-callable ghost function. The convention is temporary until a better
   --  approach or a name has been found.

end Semantics;
