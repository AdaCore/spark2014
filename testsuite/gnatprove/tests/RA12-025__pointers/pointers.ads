pragma SPARK_Mode;
package Pointers is

   type T is new Integer;

   type T_Ptr is access T;

   procedure Swap (X, Y : T_Ptr) with
     Pre  => X /= null and Y /= null,
     Post => X.all = Y.all'Old and Y.all = X.all'Old;

   type T_Rec is record
      A, B : T_Ptr;
   end record;

   procedure Swap (R : T_Rec) with
     Pre  => R.A /= null and R.B /= null,
     Post => R.A.all = R.B.all'Old and R.B.all = R.A.all'Old;

end Pointers;
