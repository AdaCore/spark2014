with SPARK.Pointers.Poisoned.Views;

package Acc_Views with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Int_Acc is access Integer;
   type Acc_Array is array (Positive range <>) of aliased Int_Acc;

   function Is_Reclaimed (X : Int_Acc) return Boolean is (X = null)
   with Ghost => Static;

   package Views is new SPARK.Pointers.Poisoned.Views (Int_Acc, Is_Reclaimed);
   use Views;

   package Arrays is new Views.Array_Operations (Positive, Acc_Array);

   function Make (V : Integer) return Int_Acc is (new Integer'(V));
   function Create_View is new Views.Create (Integer, Make);

end Acc_Views;
