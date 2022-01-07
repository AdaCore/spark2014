procedure Main with SPARK_Mode is
   package Base is
      type T1 is new Integer with Default_Value => 0; --@RANGE_CHECK:FAIL
      function Id (X : T1) return T1 is (X);
      subtype Bad1 is T1 range Id (1) .. 10;

      type T2 is new Integer with Default_Value => 0; --@RANGE_CHECK:FAIL
      function Id (X : T2) return T2 is (X);
      subtype Bad2 is T2 range Id (1) .. 10;

      type R is record
         OK1 : T1;
         KO1 : Bad1;
         KO3 : Bad1 := 0; --@RANGE_CHECK:FAIL
         OK2 : T2;
         KO2 : Bad2;
         KO4 : Bad2 := 0; --@RANGE_CHECK:FAIL
      end record;

      X : R;
   end Base;

   package Use_Generics is
      generic
         First : Integer;
      package Gen1 is
         type T is new Integer with Default_Value => 0; --@RANGE_CHECK:FAIL
         function Id (X : T) return T is (X);
         subtype Bad is T range Id (T (First)) .. 10;
      end Gen1;

      generic
         type T1 is range <>;
         type Bad1 is range <>;
         type T2 is range <>;
         type Bad2 is range <>;
      package Gen2 is
         type R is record
            OK1 : T1;
            KO1 : Bad1;
            KO3 : Bad1 := 0; --@RANGE_CHECK:FAIL
            OK2 : T2;
            KO2 : Bad2;
            KO4 : Bad2 := 0; --@RANGE_CHECK:FAIL
         end record;
      end Gen2;

      generic
         type T is private;
      package Gen3 is
         X : T;
      end Gen3;

      package I1 is new Gen1 (1);
      package I2 is new Gen1 (1);
      package I3 is new Gen2 (I1.T, I1.Bad, I2.T, I2.Bad);
      package I4 is new Gen3 (I3.R);
   end Use_Generics;

   package Box is
      type T1 is new Integer with Default_Value => 0; --@RANGE_CHECK:FAIL
      function Id (X : T1) return T1 is (X);
      subtype Bad1 is T1 range Id (1) .. 10;

      type T2 is new Integer with Default_Value => 0; --@RANGE_CHECK:FAIL
      function Id (X : T2) return T2 is (X);
      subtype Bad2 is T2 range Id (1) .. 10;

      type R1 is record
         OK1 : T1;
         KO1 : Bad1;
      end record;
      type R2 is record
         OK2 : T2;
         KO2 : Bad2;
      end record;
      type R is record
         X1 : R1 := (others => <>);
         X2 : R2 := (others => <>);
      end record;

      X : R;
   end Box;
begin
   null;
end;
