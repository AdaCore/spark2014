
with Surfaces;
use type Surfaces.ControlAngle;

package body Scale
is
   subtype Machnumber is Instruments.Machnumber;
   subtype Percent is Integer range 0..100;

   -- Return an inverse curve that is well behaved
   function Inverse(Val      : Scaledata;
                    Flatness : Integer)
                   return Percent
   --# pre (Val >= 0) and (Flatness > 0) and (Flatness <= 100);
   is
      Calc : Integer;
      Ans : Percent;
   begin
      Calc := (100*Flatness) / (Flatness + Val);
      Ans := Calc;
      return Ans;
   end Inverse;


   function Scale_Movement(Mach    : Instruments.Machnumber;
                           Present : Scaledata;
                           Target  : Scaledata;
                           Max     : Surfaces.ControlAngle)
                          return Surfaces.ControlAngle
   is
      Target_Angle : Surfaces.ControlAngle;
      K1, K2, Gap : Integer;
   begin
      if Present = Target then
         Target_Angle := 0;
      else
         -- Get the sign of the answer
         if Present < Target then
            -- Increase rate
            Gap := Target - Present;
         else
            -- Decrease rate
           Gap := Present - Target;
         end if;
         if Gap > 100 then
           Gap := 100;
         end if;
         --# assert (Gap > 0) and (Gap <= 100);
         -- Generate K1, K2 such that:
         --   K1 >= 0,  K2 > 0, K1 <= K2
         --   K1 ~= a.Gap
         --   K2 ~= b.Mach
         K1 := Inverse(Integer(Mach),20); -- tween 0 and 100
         K2 := Inverse(Gap,20); -- tween 0 and 100
         K2 := (1 + K2) + K1;  -- handle the scaling
         -- And use them to scale Target_Angle
         --# assert (K1 in Percent) and (K2 > 0) and (K1 <= K2);
         Target_Angle := Surfaces.ControlAngle((Integer(Max) * K1) / K2);
         if (Present > Target) then
              Target_Angle := -Target_Angle;
         end if;
      end if;
      return Target_Angle;
   end Scale_Movement;

   function Heading_Offset(Present : Instruments.Headdegree;
                           Target  : Instruments.Headdegree)
                          return Instruments.Headdegree
   is
      V : Integer;
      Ans : Instruments.Headdegree;
   begin
      V := (360 + Integer(Target)) - Integer(Present);
      --# assert ((V >= 0) and (V < 720));
      if (V >= 360) then
        V := V - 360;
      end if;
      --# assert ((V >= 0) and (V < 360));
      Ans := Instruments.Headdegree(V);
      return Ans;
   end Heading_Offset;

end Scale;





