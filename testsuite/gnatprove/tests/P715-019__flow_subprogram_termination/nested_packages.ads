package Nested_Packages with Annotate => (GNATprove, Always_Return) is

   procedure Contains_Packages;

   package Nested with Annotate => (GNATprove, Always_Return) is
      procedure Do_Nothing;
      package Nested2 is
         procedure Do_Nothing2;
      end Nested2;
   end Nested;

end Nested_Packages;
