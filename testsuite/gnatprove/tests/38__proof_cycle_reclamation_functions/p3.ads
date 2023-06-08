package P3 is

   type T is private with
     Annotate => (GNATprove, Ownership, "Needs_Reclamation");

   function Create return T;

   function Is_Null (V : T) return Boolean
   with
     Annotate => (GNATprove, Ownership, "Is_Reclaimed");

private
   pragma SPARK_Mode (Off);
   type T is record
      OK : Boolean;
   end record;

   function Create return T is (OK => False);

   function Is_Null (V : T) return Boolean is (not V.OK);
end P3;
