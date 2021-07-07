package Ext is
   type Int_Acc is access Integer with
     Predicate => Int_Acc = null or else Int_Acc.all /= 0;

   type T;
   type T_Acc is access T;

   type R is record
      X : T_Acc;
      Y : Int_Acc;
   end record;

   type T is record
      V : access R;
   end record;

   package Mode_Off with SPARK_Mode => Off is
      type Bad_Inter is interface;
   end Mode_Off;

   type Untagged is private;

   function Get (X : Untagged) return Integer;

private
   type My_Int is new Integer with Relaxed_Initialization;
   type Untagged is tagged record
      F : Integer := 15;
      G : My_Int;
   end record;

   function Get (X : Untagged) return Integer is (Untagged'Class (X).F);
end Ext;
