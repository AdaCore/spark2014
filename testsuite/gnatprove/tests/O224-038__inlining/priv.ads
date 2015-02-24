package Priv with SPARK_Mode is
   type Nat_Array is array (Positive range <>) of Natural;
   type Priv_Rec (C : Natural) is private;

   procedure Init (P : in out Priv_Rec) with
     Pre => P.C > 0;
private
   type Priv_Rec (C : Natural) is record
      Content : Nat_Array (1 .. C);
   end record;
end Priv;
