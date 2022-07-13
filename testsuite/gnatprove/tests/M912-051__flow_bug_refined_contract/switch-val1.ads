private package Switch.Val1
with SPARK_Mode, Abstract_State => (State with Part_Of => Switch.State)
is
   procedure Read (Value : out Switch.Reading)
   with Global   => State,
        Depends  => (Value => State),
        Annotate => (GNATprove, Always_Return);

end Switch.Val1;
