package Other with SPARK_Mode is

   procedure Swap_With_Contract (X, Y : in out Integer)
   with Global   => null,
        Annotate => (GNATprove, Always_Return),
        Depends  => (X => Y,
                     Y => X);

   procedure Swap_Without_Contract (X, Y : in out Integer);

end Other;
