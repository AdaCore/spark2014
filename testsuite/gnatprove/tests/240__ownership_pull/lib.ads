package Lib with SPARK_Mode is

   type T is private with
     Annotate => (GNATprove, Ownership, "Needs_Reclamation");

   function Is_Null (Dummy : T) return Boolean is (True) with
     Annotate => (GNATprove, Ownership, "Is_Reclaimed");

private
   pragma SPARK_Mode (Off);
   type T is null record;

end Lib;
