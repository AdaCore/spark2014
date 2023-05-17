package Nested_Packages with Always_Terminates is

   procedure Contains_Packages;

   package Nested with Always_Terminates is
      procedure Do_Nothing;
      package Nested2 is
         procedure Do_Nothing2;
      end Nested2;
   end Nested;

end Nested_Packages;
