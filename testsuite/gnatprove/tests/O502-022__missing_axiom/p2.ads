package P2 with SPARK_Mode is
    type S is record
       X : Integer;
    end record;
    function "=" (X, Y : S) return Boolean is (False);

    type T2 (D : Boolean) is  record
       C : S;
    end record;

    function Always_True (X, Y : T2) return Boolean is (True) with
      Post => Always_True'Result and (X /= Y);

end P2;
