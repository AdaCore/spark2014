with System;
package Ext with SPARK_Mode is

   --  Test validity check in unsupported address clauses

   type Int_Acc is access Integer;

   package Nested_Off is
      type Priv is private;
   private
      pragma SPARK_Mode (Off);
      type Priv is new Integer;
   end Nested_Off;
   use Nested_Off;

   package Nested_Inv is
      type T_Inv is private;
   private
      type T_Inv is new Integer with
        Default_Value => 0,
        Type_Invariant => T_Inv >= 0;
   end Nested_Inv;
   use Nested_Inv;

   type T_Inv_2 is new T_Inv;

   type Root is tagged record
      F, G : Integer;
   end record;

   function Id (X : Integer) return Integer is (X);
   subtype Dyn_Low is Integer range Id (1) .. 10;
   subtype Dyn_High is Integer range 1 .. Id (10);

   --  All the objects below should lead to a warnings about data validity

   X_Acc : Int_Acc with Import, Address => System'To_Address (1);
   X_Priv : Priv with Import, Address => System'To_Address (2);
   X_Inv : T_Inv with Import, Address => System'To_Address (3);
   X_Inv_2 : T_Inv_2 with Import, Address => System'To_Address (4);
   X_Tag : Root with Import, Address => System'To_Address (5);
   X_Low : Dyn_Low with Import, Address => System'To_Address (6);
   X_High : Dyn_High with Import, Address => System'To_Address (7);
end Ext;
