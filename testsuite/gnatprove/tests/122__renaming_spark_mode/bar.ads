with Foo;

package Bar with SPARK_Mode is
   package Nested is
      function Bar return Integer with Post => Bar'Result = 0;
   private
      pragma SPARK_Mode (Off);
      function Bar return Integer renames Foo;
   end Nested;
end Bar;
