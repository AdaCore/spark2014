package Gen_Ada_Global_Incorrect with
  SPARK_Mode
is

   type Int_Access is access Integer;

   type Holder is record I : Int_Access; end record;

   procedure Set_Access_To_Variable (V : in Holder) with SPARK_Mode => Off;

   procedure Set_Global_Access;

end Gen_Ada_Global_Incorrect;
