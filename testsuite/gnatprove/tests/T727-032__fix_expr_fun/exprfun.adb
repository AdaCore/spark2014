package body Exprfun is

   function F (X : Integer) return Boolean is
   begin
      return X = 42;
   end F;

   procedure P (X : out Integer) is
   begin
      X := 42;
   end P;

   procedure P2 (Func : Ptr; X : out Integer) is
   begin
      X := 42;
   end P2;

   procedure P3 (Func : Ptr; X : out Integer) is
   begin
      X := 42;
   end P3;

end Exprfun;
