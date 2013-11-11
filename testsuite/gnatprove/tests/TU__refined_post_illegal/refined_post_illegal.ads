package Refined_Post_Illegal
  with SPARK_Mode
is
   function Inv_Func_1 return Boolean
     --  TU: 1. A Refined_Post aspect may only appear on a body_stub (if one is
     --  present) or the body (if no stub is present) of a subprogram which is
     --  declared in the specification of a package, its abstract view. If the
     --  subprogram declaration in the visible part has no explicit
     --  postcondition, a postcondition of True is assumed for the abstract
     --  view.
     with Refined_Post => True;


   procedure Inv_Proc_1 (X, Y : in out Integer)
     --  TU: 1. A Refined_Post aspect may only appear on a body_stub (if one is
     --  present) or the body (if no stub is present) of a subprogram which is
     --  declared in the specification of a package, its abstract view. If the
     --  subprogram declaration in the visible part has no explicit
     --  postcondition, a postcondition of True is assumed for the abstract
     --  view.
     with Post => X < Y and Y > Y'Old;
end Refined_Post_Illegal;
