with Spaces.Angles;

package Gaps is

   pragma Pure;

   use Spaces.Angles;

   --  TODO: iDir should be enum or range {-1,0,+1}.
   subtype iDir_t is Integer range -1 .. +1;

   type Gap is record
      bearing : Angle;
      distance : Float;
      iDir : iDir_t;
   end record;

   function Create return Gap;

   function Create (ang : Angle; d : Float; iD : iDir_t) return Gap;

   function Equal (Left, Right : Gap) return Boolean;

end Gaps;
