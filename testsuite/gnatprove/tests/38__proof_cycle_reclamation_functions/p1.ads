with Local_Variable_Subp; use Local_Variable_Subp;

package P1 is

   type T is private with
     Annotate => (GNATprove, Ownership, "Needs_Reclamation");

   function Is_Null (V : T) return Boolean is (Func)
   with
     Annotate => (GNATprove, Ownership, "Is_Reclaimed");

private
   pragma SPARK_Mode (Off);
   type T is record
      OK : Boolean;
   end record;
end P1;
