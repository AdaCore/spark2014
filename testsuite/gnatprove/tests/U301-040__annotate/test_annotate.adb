procedure Test_Annotate with SPARK_Mode is
   X : Positive;
   Y : Float with Import, Address => X'Address;
   pragma Annotate (GNATprove, Intentional, "unsuitable for aliasing via address clause", "I don't care");
begin
   null;
end Test_Annotate;
