package body S is

   --  Abstract type with an abstract operation

   package P is
      type T is abstract tagged null record;

      procedure P (X : T) is abstract;
   end P;

   --  Concrete type with a concrete operation

   package Q is
      type TT is new P.T with null record;

      procedure P (X : TT);
   end Q;

   package body Q is

      procedure P (X : TT) is
      begin
         null;
      end P;

   end Q;

   --  Concrete object with an class-wide (abstract) type

   X : P.T'Class := Q.TT'(null record);

   procedure Proxy2 with
     Pre => True  --  disable frontend inlining
   is
   begin
      X.P;  --  Dispatching call
   end Proxy2;

   procedure Proxy1 with
     Pre => True  --  disable frontend inlining
   is
   begin
      Proxy2;
   end Proxy1;

   protected body PT is
      procedure Proc is
      begin
         Proxy1;  --  2-level indirect dispatching call in protected operation
      end Proc;
   end PT;
end S;
