package Pointers with SPARK_Mode is

   type T is new Integer;

   type T_Ptr is not null access T;

   procedure Swap (X, Y : T_Ptr) with
     Post => X.all = Y.all'Old and Y.all = X.all'Old;

end Pointers;
