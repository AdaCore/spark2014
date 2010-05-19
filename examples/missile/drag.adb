-- Dynamic drag computation
-- $Log: drag.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/12 18:12:48  adi
-- Initial revision
--
--
with constants;
package body Drag
is
   -- Type abbreviations
   subtype integer32 is long_integer;  -- change to systemtypes.integer32

   -- Constants
   lin_quad_boundary : constant pos_meter_per_sec := 100;
   transonic_boundary : constant pos_meter_per_sec := 400;
   postsonic_boundary : constant pos_meter_per_sec := 450;
   drag_at_mach1 : constant integer32 :=
     integer32(constants.mach1_sea * constants.mach1_sea) /
     integer32(lin_quad_boundary);
   transonic_mach1_diff : constant integer32 :=
     integer32(transonic_boundary - constants.mach1_sea);
   drag_at_transonic : constant integer32 :=
     drag_at_mach1 +
       (transonic_mach1_diff * (transonic_mach1_diff * transonic_mach1_diff))
        / 2000;

   subtype percent is integer32 range 0..100;

   function Relative_Drag_At_Altitude(Altitude : in pos_meter) return percent
   --# pre altitude >= 0 and altitude <= 25_000;
   is
      intermediate : integer32;
   begin
      intermediate := (50_000 - integer32(Altitude)) / 250;
      -- intermediate is now between 100 and 200
      if intermediate < 100 then
         intermediate := 100;
      elsif intermediate > 200 then
         intermediate := 200;
      else
         null;
      end if;
      return (intermediate - 100);
   end relative_drag_at_altitude;


   procedure Calc_Drag(Profile  : in Drag_Coefficient;
                       Speed    : in Pos_Meter_Per_Sec;
                       Altitude : in pos_Meter;
                       Drag_force : out measuretypes.newton)
   is
      working : integer32;
      sdiff,ddiff : integer32;
   begin
      if speed < constants.mach1_sea then
         -- Sub-mach1
         if speed < lin_quad_boundary then
            -- linear: ranges from 1 to 100
            working := integer32(speed);
         else
            -- quadratic, ranges from 100 to about 900
            working := (integer32(speed)*integer32(speed)) /
              integer32(lin_quad_boundary);
         end if;
      else
        if speed < transonic_boundary then
            -- Weird transonic drag going on, very steep
            -- ranges from about 900 to about 1350
            sdiff := integer32(speed - constants.mach1_sea);
            working := drag_at_mach1 + (sdiff * (sdiff * sdiff))/2000;
         elsif speed < postsonic_boundary then
            -- Falls off linearly back to quadratic
            sdiff := integer32(postsonic_boundary - transonic_boundary);
            ddiff := drag_at_transonic - drag_at_mach1;
            working := drag_at_mach1 +
              (integer32(postsonic_boundary - speed)*ddiff)/sdiff;
         else
            -- linear again
            sdiff := integer32(speed - postsonic_boundary);
            working := drag_at_mach1 + sdiff;
         end if;
      end if;
      working := (working * relative_drag_at_altitude(altitude)) / 100;
      drag_force := measuretypes.newton((working * integer32(profile))/2);
   end calc_drag;

   procedure Testpoint is separate;
end Drag;
