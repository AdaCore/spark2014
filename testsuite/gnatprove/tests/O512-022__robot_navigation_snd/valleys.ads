with Gaps;

package Valleys is

   pragma Pure;

   use Gaps;

   type Valley is record
      risingGap, otherGap : Gap;
   end record;

   function Create (rG, oG : Gap) return Valley;

end Valleys;
