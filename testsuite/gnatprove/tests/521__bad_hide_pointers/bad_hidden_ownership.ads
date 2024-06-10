package Bad_Hidden_Ownership with SPARK_Mode is

   type T_Acc is private with
     Annotate => (GNATprove, Predefined_Equality, "Only_Null"),
     Annotate => (GNATprove, Ownership, "Needs_Reclamation");

   C_Acc : constant T_Acc with --@RECLAMATION_ENTITY:FAIL
     Annotate => (GNATprove, Ownership, "Reclaimed_Value");

   type T_Acc_Holder is private with
     Annotate => (GNATprove, Predefined_Equality, "No_Equality"),
     Annotate => (GNATprove, Ownership, "Needs_Reclamation");

   function T_Acc_Holder_Is_Reclaimed (X : T_Acc_Holder) return Boolean; --@RECLAMATION_ENTITY:FAIL
   pragma Annotate (GNATprove, Ownership, "Is_Reclaimed", T_Acc_Holder_Is_Reclaimed);

   type T_Priv_Reclaim (D : Integer) is private;
   pragma Annotate (GNATprove, Ownership, "Needs_Reclamation", T_Priv_Reclaim);

   function T_Priv_Needs_Reclamation (X : T_Priv_Reclaim) return Boolean; --@RECLAMATION_ENTITY:FAIL
   pragma Annotate (GNATprove, Ownership, "Needs_Reclamation", T_Priv_Needs_Reclamation);

private
   pragma Annotate (GNATprove, Hide_Info, "Private_Part", Bad_Hidden_Ownership);

   type T_Acc is access Integer;

   C_Acc : constant T_Acc := new Integer'(12);

   type Int_Acc is access Integer;

   type T_Acc_Holder is record
      X : Int_Acc;
   end record;

   function T_Acc_Holder_Is_Reclaimed (X : T_Acc_Holder) return Boolean is
     (X.X /= null);

   package Nested is

      type P_Reclaim (D : Integer) is private;
      pragma Annotate (GNATprove, Ownership, "Needs_Reclamation", P_Reclaim);

      function P_Is_Reclaimed (X : P_Reclaim) return Boolean;
      pragma Annotate (GNATprove, Ownership, "Is_Reclaimed", P_Is_Reclaimed);

   private
      pragma SPARK_Mode (Off);

      type P_Reclaim (D : Integer) is record
         X : Int_Acc;
      end record;

      function P_Is_Reclaimed (X : P_Reclaim) return Boolean is (X.X = null);
   end Nested;

   type T_Priv_Reclaim (D : Integer) is new Nested.P_Reclaim (D);

   function T_Priv_Needs_Reclamation (X : T_Priv_Reclaim) return Boolean is
     (Nested.P_Is_Reclaimed (Nested.P_Reclaim (X)));

end Bad_Hidden_Ownership;
