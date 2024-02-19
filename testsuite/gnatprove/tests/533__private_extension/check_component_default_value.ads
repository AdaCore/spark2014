package Check_Component_Default_Value with SPARK_Mode is
   function Rand (X : Integer) return Integer with
     Global => null,
     Import;

   package P is
      type T1 is tagged record
         F1 : Positive := Rand (1); --@RANGE_CHECK:FAIL
      end record;
      type T2 is new T1 with record
         F2 : Positive := Rand (2); --@RANGE_CHECK:FAIL
      end record;
      type T3 is new T1 with private;
   private
      type T3 is new T2 with record
         F3 : Positive := Rand (3); --@RANGE_CHECK:FAIL
      end record;
   end P;

   type T4 is new P.T3 with null record;

   X : T4;
end Check_Component_Default_Value;
