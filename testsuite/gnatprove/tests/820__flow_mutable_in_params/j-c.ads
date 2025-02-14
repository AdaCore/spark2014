package J.C with SPARK_Mode, Initializes => G is
   G : T;

   procedure P (X : T) with
     Global => (In_Out => G),
     Pre => Is_Valid (X),
     Post => Is_Valid (X);

   pragma Annotate (GNATprove, Mutable_In_Parameters, T);
end J.C;
