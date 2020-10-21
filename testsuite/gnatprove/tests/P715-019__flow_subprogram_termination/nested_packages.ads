package Nested_Packages with Annotate => (GNATprove, Terminating) is

   procedure Contains_Packages;

   package Nested with Annotate => (GNATprove, Terminating) is
      procedure Do_Nothing;
      package Nested2 is
         procedure Do_Nothing2;
      end Nested2;
   end Nested;

end Nested_Packages;
