package J with SPARK_Mode is
   type T is private with
     Annotate => (GNATprove, Ownership);

   function Is_Valid (X : T) return Boolean;

private
   pragma SPARK_Mode (Off);
   type T is access Integer;

   function Is_Valid (X : T) return Boolean is (X /= null);
end J;
