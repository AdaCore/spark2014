with Local_Variable_Pkg; use Local_Variable_Pkg;

package P2 is

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
end P2;
