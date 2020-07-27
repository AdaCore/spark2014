package Pointers is

   type Int_Acc is access Integer;

   type Rec is record
      X : Int_Acc;
      Y : Integer;
   end record;

   procedure Test;

   type List;
   type List_Acc is access List;

   type List is record
      Next : List_Acc;
   end record;

   procedure Test_List (L : in out List);

end Pointers;
