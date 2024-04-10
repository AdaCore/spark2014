package Hidden_Predefined_Eq with SPARK_Mode is

   type T_Cst_Acc is private with
     Annotate => (GNATprove, Predefined_Equality, "Only_Null");

   C_Cst_Acc : constant T_Cst_Acc with
     Annotate => (GNATprove, Predefined_Equality, "Null_Value");

   type T_Cst_Acc_Holder is private with
     Annotate => (GNATprove, Predefined_Equality, "No_Equality");

   type T_Priv_No_Eq is private with
     Annotate => (GNATprove, Predefined_Equality, "No_Equality");

   type T_Priv_Only_Null (D : Integer) is private;
   pragma Annotate (GNATprove, Predefined_Equality, "Only_Null", T_Priv_Only_Null);

   C_Priv_Only_Null : constant T_Priv_Only_Null;
   pragma Annotate (GNATprove, Predefined_Equality, "Null_Value", C_Priv_Only_Null);

private
   pragma Annotate (GNATprove, Hide_Info, "Private_Part", Hidden_Predefined_Eq);

   type T_Cst_Acc is access constant Integer;

   C_Cst_Acc : constant T_Cst_Acc := null;

   type Cst_Acc is access constant Integer;

   type T_Cst_Acc_Holder is record
      Content : Cst_Acc;
   end record;

   package Nested is

      type P_No_Eq is private with
        Annotate => (GNATprove, Predefined_Equality, "No_Equality");

      type P_Only_Null (D : Integer) is private with
        Annotate => (GNATprove, Predefined_Equality, "Only_Null");

      D_Only_Null : constant P_Only_Null with
        Annotate => (GNATprove, Predefined_Equality, "Null_Value");

   private
      pragma SPARK_Mode (Off);

      type P_No_Eq is null record;

      type P_Only_Null (D : Integer) is null record;

      D_Only_Null : constant P_Only_Null := (D => 0);
   end Nested;

   type T_Priv_No_Eq is new Nested.P_No_Eq;

   type T_Priv_Only_Null (D : Integer) is new Nested.P_Only_Null (D);

   C_Priv_Only_Null : constant T_Priv_Only_Null :=
     T_Priv_Only_Null (Nested.D_Only_Null);

end Hidden_Predefined_Eq;
