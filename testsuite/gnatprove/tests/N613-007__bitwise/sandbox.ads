
package Sandbox
  with SPARK_Mode
is

   type Size64_Type is mod 2**64;
   type Size32_Type is mod 2**32;

   procedure Split(Whole : in Size64_Type; MSW, LSW : out Size32_Type)
     with
       Global => null,
       Depends => ((MSW, LSW) => Whole);

end Sandbox;
