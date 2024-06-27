package P with SPARK_Mode is
   type S2 is private;
   type T is private;
   function Value_Is_OK_1 return Boolean;
   function Value_Is_OK_2 return Boolean;
   function Id (X : S2) return S2;

private

   package Nested is
      type S1 is private;
      function Is_OK (X : S1) return Boolean;
   private
      type S1 is new Integer with Type_Invariant => S1 >= 0, Default_Value => 0;
      function Is_OK (X : S1) return Boolean is (X >= 0);
   end Nested;
   use Nested;

   type S2 is new Integer with Type_Invariant => S2 >= 0, Default_Value => 0;
   function Is_OK (X : S2) return Boolean is (X >= 0);
   function Incr (X : S2) return S2 is (X + 1) with Pre => X < S2'Last;
   function Decr (X : S2) return S2 is (X - 1) with Pre => X > S2'First;
   function Id (X : S2) return S2 is (Incr (Decr (X)));

   type T is record
      F1 : S1;
      F2 : S2;
   end record;

   function Value return T with Import, Global => null;
   function Value_Is_OK_1 return Boolean is
     (Is_Ok (Value.F1));
   function Value_Is_OK_2 return Boolean is
     (Is_OK (Value.F2));
end P;
