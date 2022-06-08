package Nobody is
   function Divide (X, Y : Integer) return Integer with
     Global   => null,
     Annotate => (GNATprove, Always_Return),
     Pre      => Y /= 0,
     Post     => Divide'Result = X / Y;
end Nobody;
