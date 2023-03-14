function Mutually_Recursive_Nested_Package return Integer with SPARK_Mode,
  Annotate => (GNATprove, Always_Return) is
   package P is X : Integer := Mutually_Recursive_Nested_Package; end P;
begin
   return 0;
end Mutually_Recursive_Nested_Package;
