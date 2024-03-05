package Ext with SPARK_Mode is

   --  R1 can be abstracted

   type R1 is record
      F1, F2 : Integer;
   end record;

   --  R2 cannot be abstracted if objects of this type are initialized

   type R2 is record
      F1 : Integer := 12;
      F2 : Integer;
   end record;

   --  R3 cannot be abstracted if objects of this type are initialized

   type Int_Acc is access Integer;
   type R3 is record
      F : Int_Acc;
   end record;

   function "=" (X, Y : R3) return Boolean is
     (if X.F = null then Y.F = null
      else Y.F /= null and then X.F.all = Y.F.all);

   --  R4 cannot be abstracted if objects of this type are compared

   type R4 is record
      F1, F2 : Float;
   end record;

   type RR is record
      G1 : R1;
      G2 : R2;
      G3 : R3;
      G4 : R4;
      H  : Integer := 1;
   end record;
end Ext;
