package Illegal_Hidden_Predefined_Eq with SPARK_Mode is

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

   --  Missing predefined equality annotations

   package Missing_Annot is
      type T_Cst_Acc is private;

      type T_Cst_Acc_Holder is private;

      type T_Priv_No_Eq is private;

      type T_Priv_Only_Null (D : Integer) is private;

   private
      pragma Annotate (GNATprove, Hide_Info, "Private_Part", Missing_Annot);

      type T_Cst_Acc is access constant Integer;

      type Cst_Acc is access constant Integer;

      type T_Cst_Acc_Holder is record
         Content : Cst_Acc;
      end record;

      type T_Priv_No_Eq is new Nested.P_No_Eq;

      type T_Priv_Only_Null (D : Integer) is new Nested.P_Only_Null (D);

   end Missing_Annot;

   --  Unexpected predefined equality annotations on regular types

   package Unexpected is

      type T_Float is private with
        Annotate => (GNATprove, Predefined_Equality, "Only_Null");

      C_Float : constant T_Float with
        Annotate => (GNATprove, Predefined_Equality, "Null_Value");

      type T_Int is private with
        Annotate => (GNATprove, Predefined_Equality, "No_Equality");

   private
      pragma Annotate (GNATprove, Hide_Info, "Private_Part", Unexpected);

      type T_Float is new Float;

      C_Float : constant T_Float := 0.0;

      type T_Int is record
         F : Integer;
      end record;

   end Unexpected;

   --  Incorrect kinds of predefined equality annotations

   package Bad_Flavor is
      type T_Cst_Acc is private with
        Annotate => (GNATprove, Predefined_Equality, "No_Equality");

      type T_Cst_Acc_Holder is private with
        Annotate => (GNATprove, Predefined_Equality, "Only_Null");

      type T_Priv_No_Eq is private with
        Annotate => (GNATprove, Predefined_Equality, "Only_Null");

      type T_Priv_Only_Null (D : Integer) is private with
        Annotate => (GNATprove, Predefined_Equality, "No_Equality");

   private
      pragma Annotate (GNATprove, Hide_Info, "Private_Part", Bad_Flavor);

      type T_Cst_Acc is access constant Integer;

      type Cst_Acc is access constant Integer;

      type T_Cst_Acc_Holder is record
         Content : Cst_Acc;
      end record;

      type T_Priv_No_Eq is new Nested.P_No_Eq;

      type T_Priv_Only_Null (D : Integer) is new Nested.P_Only_Null (D);
   end Bad_Flavor;

end Illegal_Hidden_Predefined_Eq;
