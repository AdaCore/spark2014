package Foo is

   package T1_Pkg is
      type T1 is tagged limited null record;
      function Prim_Func return T1 is (null record);
   end T1_Pkg;

   package T2_Pkg is
      type T2 is new T1_Pkg.T1 with null record;
   end T2_Pkg;

end Foo;
