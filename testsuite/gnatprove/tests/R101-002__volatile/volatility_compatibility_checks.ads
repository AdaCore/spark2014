package Volatility_Compatibility_Checks with
   SPARK_Mode
is

   package Pkg1 is
      type T is new Integer with
         Volatile,
         Effective_Writes,
         Async_Readers;
      X1 : T with
         Effective_Reads  => False,
         Effective_Writes => False,
         Async_Readers;
      X2 : T with
         Async_Writers => True; -- illegal; SPARK RM 7.1.3(2)
   end Pkg1;

   package Pkg2 is
      type Component is new Integer with
         Volatile,
         Async_Readers;

      type Rec is record
         F1, F2 : Float;
         F3     : Component; -- illegal; SPARK RM 7.1.3(6)
      end record with
         Volatile,
         Async_Writers;

      type Vec is array
          (Character) of Component -- illegal; SPARK RM 7.1.3(6)
      with
         Volatile,
         Async_Writers;
   end Pkg2;

   package Pkg3 is
      type Designated is new Integer with
         Volatile,
         Async_Readers;
      type Ref is access Designated with
         Volatile,
         Async_Writers; -- illegal; SPARK RM 7.1.3(6)
   end Pkg3;

   package Pkg4 is
      package Aaa is
         type T1 is new Integer with Volatile, Async_Readers;
      end Aaa;

      procedure Op (X : in out Aaa.T1);

      type T2 is new Aaa.T1 with Async_Writers;
      X2 : T2 := 123;
   end Pkg4;

   package Pkg5 is
      generic
         type Priv is private with
            Volatile,
            Async_Readers;
      package G is
      end G;

      type A1 is new String (1 .. 4) with
         Volatile,
         Async_Readers;
      type A2 is new String (1 .. 4) with
         Volatile,
         Async_Writers;

      package I1 is new G (A1);
      package I2 is new G (A2); -- illegal; SPARK RM 7.1.3(7)
   end Pkg5;

   package Pkg6 is
      type A1 is new String (1 .. 4) with
         Volatile,
         Async_Readers;

      generic
         A1_Obj : in out A1;
      package G is
      end G;

      Good_Obj : A1;
      Bad_Obj  : A1 with Async_Writers;

      package I1 is new G (Good_Obj);
      package I2 is new G (Bad_Obj); -- illegal; SPARK RM 7.1.3(7)
   end Pkg6;

end Volatility_Compatibility_Checks;
