package Test_Type with SPARK_Mode is
   type T is private;
   function Decr (X : T) return T;
private
   type T is record
      F : Integer := 0;
   end record
     with Type_Invariant => F in Natural;

   function Decr_Int (X : T) return T is
     (F => X.F - 1)
   with Pre => X.F > Integer'First;

   function Saturate (X : T) return T is
      (if X.F < 0 then (F => 0) else X);

   function Decr (X : T) return T is
     (Saturate (Decr_Int (X)));

   procedure Decr_Int (X : in out T) with
     Pre => X.F > Integer'First,
     Post => X.F = X.F'Old - 1;
end Test_Type;
