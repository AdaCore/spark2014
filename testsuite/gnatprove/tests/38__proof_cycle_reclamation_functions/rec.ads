with Local_Variable_Rec; use Local_Variable_Rec;

package Rec is

   type T1 is private with
     Annotate => (GNATprove, Ownership, "Needs_Reclamation");

   function Is_Null (V : T1) return Boolean
   with
     Import,
     Annotate => (GNATprove, Ownership, "Is_Reclaimed");

   type T2 is private with
     Annotate => (GNATprove, Ownership, "Needs_Reclamation");

   function Is_Null (V : T2) return Boolean is (Func)
   with
     Annotate => (GNATprove, Ownership, "Is_Reclaimed");

   type R is record
      A : T1;
      B : T2;
   end record;

private
   pragma SPARK_Mode (Off);
   type T1 is record
      OK : Boolean;
   end record;

   type T2 is record
      OK : Boolean;
   end record;
end Rec;
