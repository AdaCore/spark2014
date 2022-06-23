package Transitive
  with SPARK_Mode => On
is
   function Property (X, Y : in Natural) return Boolean
     with Global   => null,
          Annotate => (GNATprove, Always_Return),
          Ghost    => True,
          Import   => True;

   procedure Change (X : in out Natural)
     with Post => Property (X'Old, X);

end Transitive;
