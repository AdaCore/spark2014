package Exprfun is

   function F (X : Integer) return Boolean;

   procedure P (X : out Integer) with
     Post => F(X);  --  @POSTCONDITION:FAIL

   type Ptr is access function (X : Integer) return Boolean;

   G : Ptr := F'Access;

   procedure P2 (Func : Ptr; X : out Integer) with
     Post => Func(X);  --  @POSTCONDITION:FAIL

   procedure P3 (Func : Ptr; X : out Integer) with
     Post => G(X);  --  @POSTCONDITION:FAIL

end Exprfun;
