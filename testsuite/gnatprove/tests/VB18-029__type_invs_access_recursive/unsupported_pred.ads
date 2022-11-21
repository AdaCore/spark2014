package Unsupported_Pred with SPARK_Mode is
   type List_Cell_1 is private;
   type List_1 is access List_Cell_1;

   type Int_Pos is private;
   type List_Cell_2 is private;
   type List_2 is access List_Cell_2;
private
   type List_Cell_1 is record
      V : Integer := 0;
      N : List_1;
   end record with
     Invariant => V >= 0;

   type Int_Pos is new Integer with
     Default_Value => 0,
     Invariant => Int_Pos >= 0;

   type List_Cell_2 is record
      V : Int_Pos;
      N : List_2;
   end record;
end;
