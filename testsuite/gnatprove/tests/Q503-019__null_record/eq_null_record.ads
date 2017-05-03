package Eq_Null_Record with SPARK_Mode is

  type T is null record;

  function "=" (X, Y : T) return Boolean is (False);

  type P is private;

   type S is record
      X : T;
   end record;

   function Always_True (X, Y : S) return Boolean is (True) with
   Post => Always_True'Result and X /= Y;

private
   pragma SPARK_Mode (Off);

   type P is null record;

  function "=" (X, Y : P) return Boolean is (False);

end Eq_Null_Record;
