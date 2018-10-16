package Pointers with SPARK_Mode is

   type T is new Integer;

   type T_Ptr is access T;

   procedure Swap (X, Y : T_Ptr) with
     Pre  => X /= null and Y /= null,
     Post => X /= null and Y /= null and X.all = Y.all'Old and Y.all = X.all'Old;

   type Index is range 1 .. 10;
   type T_Arr is array (Index) of T_Ptr
     with Predicate => (for all K in Index => T_Arr(K) /= null);

   procedure Swap (A : in out T_Arr; I, J : Index) with
     Pre  => I /= J,
     Post => A(I).all = A(J).all'Old and A(J).all = A(I).all'Old;

end Pointers;
