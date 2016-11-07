procedure Foo is

   package T1_Pkg is
      type T1 is tagged null record;
      procedure Prim_Proc (X : T1);
      function  Prim_Func return T1;
      T1_Var : T1;
      procedure Cw_Operand (X : T1'Class := T1_Var);
   end T1_Pkg;

   package T2_Pkg is
      type T2 is new T1_Pkg.T1 with null record;
      T2_Var : T2;
      procedure Cw_Operand (X : T2'Class := T2_Var);
   end T2_Pkg;

   package T3_Pkg is
      type T3 is new T2_Pkg.T2 with null record;
      T3_Var : T3;
      procedure Cw_Operand (X : T3'Class := T3_Var);
   end T3_Pkg;

   package body T1_Pkg is
      procedure Prim_Proc (X : T1) is null;
      function  Prim_Func return T1 is (T1_Var);
      procedure Cw_Operand (X : T1'Class := T1_Var) is null;
   end T1_Pkg;

   package body T2_Pkg is
      procedure Cw_Operand (X : T2'Class := T2_Var) is null;
   end T2_Pkg;

   package body T3_Pkg is
      procedure Cw_Operand (X : T3'Class := T3_Var) is null;
   end T3_Pkg;

   package Late_Resolver is
      procedure Proc
        with Pre => (Prim_Func = Prim_Func);

      use type T1_Pkg.T1;
      use all type T2_Pkg.T2;
      use type T3_Pkg.T3;
   end Late_Resolver;

   package body Late_Resolver is
      procedure Proc is null;
   end Late_Resolver;

begin
   null;
end Foo;
