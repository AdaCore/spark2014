with Acc_Views; use Acc_Views;

package Replacing with SPARK_Mode is
   use Views, Arrays;

   procedure Replace_In_View
     (A   : in out View_Array;
      I   : Positive;
      V   : Integer;
      Old : out Int_Acc)
   with
     Pre  =>
       I in A'Range
       and then (for all K in A'Range => not Is_Poisoned (A (K))),
     Post => (for all K in A'Range => not Is_Poisoned (A (K)));

   procedure Replace
     (A   : aliased in out Acc_Array;
      I   : Positive;
      V   : Integer;
      Old : out Int_Acc)
   with Pre => I in A'Range;

end Replacing;
