package Illegal_Hidden_Ownership with SPARK_Mode is

   type Int_Acc is access Integer;

   type Int_Gen_Acc is access all Integer;

   package Nested is

      type P_No_Reclaim is private with
        Annotate => (GNATprove, Ownership);

      type P_Reclaim (D : Integer) is private;
      pragma Annotate (GNATprove, Ownership, "Needs_Reclamation", P_Reclaim);

      function P_Is_Reclaimed (X : P_Reclaim) return Boolean;
      pragma Annotate (GNATprove, Ownership, "Is_Reclaimed", P_Is_Reclaimed);

   private
      pragma SPARK_Mode (Off);

      type P_No_Reclaim is access all Integer;

      type P_Reclaim (D : Integer) is record
         X : Int_Acc;
      end record;

      function P_Is_Reclaimed (X : P_Reclaim) return Boolean is (X.X = null);
   end Nested;

   --  Missing ownership annotations

   package Missing_Annot is

      type T_Acc is private with
        Annotate => (GNATprove, Predefined_Equality, "Only_Null");

      C_Acc : constant T_Acc with
        Annotate => (GNATprove, Predefined_Equality, "Null_Value");

      type T_Gen_Acc is private with
        Annotate => (GNATprove, Predefined_Equality, "Only_Null");

      C_Gen_Acc : constant T_Gen_Acc with
        Annotate => (GNATprove, Predefined_Equality, "Null_Value");

      type T_Acc_Holder is private with
        Annotate => (GNATprove, Predefined_Equality, "No_Equality");

      type T_Gen_Acc_Holder is private with
        Annotate => (GNATprove, Predefined_Equality, "No_Equality");

      type T_Priv_No_Reclaim is private;

      type T_Priv_Reclaim (D : Integer) is private;

   private
      pragma Annotate (GNATprove, Hide_Info, "Private_Part", Missing_Annot);

      type T_Acc is access Integer;

      C_Acc : constant T_Acc := null;

      type T_Gen_Acc is access all Integer;

      C_Gen_Acc : constant T_Gen_Acc := null;

      type T_Acc_Holder is record
         X : Int_Acc;
      end record;

      type T_Gen_Acc_Holder is record
         X : Int_Gen_Acc;
      end record;

      type T_Priv_No_Reclaim is new Nested.P_No_Reclaim;

      type T_Priv_Reclaim (D : Integer) is new Nested.P_Reclaim (D);

   end Missing_Annot;

   --  Unexpected ownership annotations on shallow types

   package Unexpected is

      type T_Float is private with
        Annotate => (GNATprove, Ownership, "Needs_Reclamation");

      C_Float : constant T_Float with
        Annotate => (GNATprove, Ownership, "Reclaimed_Value");

      type T_Int is private with
        Annotate => (GNATprove, Ownership);

   private
      pragma Annotate (GNATprove, Hide_Info, "Private_Part", Unexpected);

      type T_Float is new Float;

      C_Float : constant T_Float := 0.0;

      type T_Int is record
         F : Integer;
      end record;

   end Unexpected;

   --  Incorrect kinds of ownership annotations

   package Bad_Flavor is

      type T_Acc is private with
        Annotate => (GNATprove, Predefined_Equality, "Only_Null"),
        Annotate => (GNATprove, Ownership);

      C_Acc : constant T_Acc with
        Annotate => (GNATprove, Predefined_Equality, "Null_Value");

      type T_Gen_Acc is private with
        Annotate => (GNATprove, Predefined_Equality, "Only_Null"),
        Annotate => (GNATprove, Ownership, "Needs_Reclamation");

      C_Gen_Acc : constant T_Gen_Acc with
        Annotate => (GNATprove, Predefined_Equality, "Null_Value");

      type T_Acc_Holder is private with
        Annotate => (GNATprove, Predefined_Equality, "No_Equality"),
        Annotate => (GNATprove, Ownership);

      type T_Gen_Acc_Holder is private with
        Annotate => (GNATprove, Predefined_Equality, "No_Equality"),
        Annotate => (GNATprove, Ownership, "Needs_Reclamation");

      type T_Priv_No_Reclaim is private with
        Annotate => (GNATprove, Ownership, "Needs_Reclamation");

      type T_Priv_Reclaim (D : Integer) is private with
        Annotate => (GNATprove, Ownership);

   private
      pragma Annotate (GNATprove, Hide_Info, "Private_Part", Bad_Flavor);

      type T_Acc is access Integer;

      C_Acc : constant T_Acc := null;

      type T_Gen_Acc is access all Integer;

      C_Gen_Acc : constant T_Gen_Acc := null;

      type T_Acc_Holder is record
         X : Int_Acc;
      end record;

      type T_Gen_Acc_Holder is record
         X : Int_Gen_Acc;
      end record;

      type T_Priv_No_Reclaim is new Nested.P_No_Reclaim;

      type T_Priv_Reclaim (D : Integer) is new Nested.P_Reclaim (D);

   end Bad_Flavor;

end Illegal_Hidden_Ownership;
