package body Refined_Post_Illegal
  with SPARK_Mode
is
   function Inv_Func_1 return Boolean is
   begin
      return True;
   end Inv_Func_1;


   function Inv_Func_2 return Integer
     --  TU: 1. A Refined_Post aspect may only appear on a body_stub (if one is
     --  present) or the body (if no stub is present) of a subprogram which is
     --  declared in the specification of a package, its abstract view. If the
     --  subprogram declaration in the visible part has no explicit
     --  postcondition, a postcondition of True is assumed for the abstract
     --  view.
     with Refined_Post => Inv_Func_2'Result > 10
   is
   begin
      return 11;
   end Inv_Func_2;


   function Inv_Func_3 (X : Integer) return Boolean
     with Post => (if X > 1000 then Inv_Func_3'Result);


   function Inv_Func_3 (X : Integer) return Boolean
     --  TU: 1. A Refined_Post aspect may only appear on a body_stub (if one is
     --  present) or the body (if no stub is present) of a subprogram which is
     --  declared in the specification of a package, its abstract view. If the
     --  subprogram declaration in the visible part has no explicit
     --  postcondition, a postcondition of True is assumed for the abstract
     --  view.
     with Refined_Post => (if X >= 10 then Inv_Func_3'Result)
   is
   begin
      if X >= 10 then
         return True;
      end if;
      return False;
   end Inv_Func_3;


   function Inv_Func_4 (X, Y : Boolean) return Boolean is (X and Y)
     --  TU: 1. A Refined_Post aspect may only appear on a body_stub (if one is
     --  present) or the body (if no stub is present) of a subprogram which is
     --  declared in the specification of a package, its abstract view. If the
     --  subprogram declaration in the visible part has no explicit
     --  postcondition, a postcondition of True is assumed for the abstract
     --  view.
     with Refined_Post => (if (X or Y) then Inc_Func_4'Result);


   procedure Inv_Proc_1 (X, Y : in out Integer) is separate;
end Refined_Post_Illegal;
