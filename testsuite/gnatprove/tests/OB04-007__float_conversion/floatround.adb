procedure Floatround with
  SPARK_Mode
is
   type T1 is new Float range -10.0 .. 10.0;
   subtype T2 is T1 with Static_Predicate => T2 in -1.0 .. 1.0;

   function Convert (X : T1) return T2 is (T2(X)) with
     Pre => X in T2;

   X1 : T1 := 0.5;
   X2 : T2 := Convert (X1);
begin
   null;
end Floatround;
