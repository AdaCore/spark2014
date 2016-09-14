procedure Integerround with
  SPARK_Mode
is
   type T1 is new Integer range -10 .. 10;
   subtype T2 is T1 with Static_Predicate => T2 in -1 .. 1;

   function Convert (X : T1) return T2 is (T2(X)) with
     Pre => X in T2;

   X1 : T1 := 1;
   X2 : T2 := Convert (X1);
begin
   null;
end Integerround;
