package Ownership with SPARK_Mode is
   type T is private
     with Annotate => (GNATprove, Ownership, "Needs_Reclamation");
   package Leaky is
      function Is_Reclaimed (X : T) return Boolean is (False);
      pragma Annotate (GNATprove, Ownership, "Is_Reclaimed", Is_Reclaimed);
   end Leaky;
   package Garbage_Collected is
      function Is_Reclaimed (X : T) return Boolean is (True);
      pragma Annotate (GNATprove, Ownership, "Is_Reclaimed", Is_Reclaimed);
   end Garbage_Collected;
private
   pragma SPARK_Mode (Off);
   type T is new Integer;
end Ownership;
