-- Test keywords
--
-- $Log: test_keywords.ads,v $
-- Revision 1.3  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
-- Revision 1.2  2004/12/17 16:08:53  adi
-- Fixing errors in compass; renamed Angle to Angle_Degrees for clarity
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.15  2003/09/12 20:38:33  adi
-- Added Missile keyword
--
-- Revision 1.14  2003/09/07 20:25:35  adi
-- Added Nav
--
-- Revision 1.13  2003/08/17 12:59:13  adi
-- Added keywords for other components
--
-- Revision 1.12  2003/08/17 12:41:55  adi
-- Added gram_rate
--
-- Revision 1.11  2003/08/12 18:21:45  adi
-- Added Auxiliary keyword
--
-- Revision 1.10  2003/08/11 19:36:55  adi
-- Added Environment keyword
--
-- Revision 1.9  2003/08/10 16:54:34  adi
-- Added extra RTs
--
-- Revision 1.8  2003/08/09 09:23:56  adi
-- Added accel, mass, force
--
-- Revision 1.7  2003/08/05 18:35:56  adi
-- Added Signed16_IO
--
-- Revision 1.6  2003/08/02 19:32:44  adi
-- Changed Angle to import from measuretypes
--
-- Revision 1.5  2003/08/02 19:28:07  adi
-- Added Angle and Compass
--
-- Revision 1.4  2003/02/19 19:11:40  adi
-- Added Bool_Io
--
-- Revision 1.3  2003/02/19 19:01:54  adi
-- Added measuretypes I/O
--
-- Revision 1.2  2003/02/13 00:17:32  adi
-- Added Clock keywords
--
-- Revision 1.1  2003/02/12 23:52:21  adi
-- Initial revision
--
--
with Ada.Text_Io, Clock, Systemtypes;
package Test_Keywords is
   -- Io of common type values
   -- Other types have Io in child packages e.g. Measuretypes.Io;
   package Millisec_Io is new Ada.Text_Io.Integer_Io(Clock.Millisecond);
   package Bool_Io is
      new Ada.Text_Io.Enumeration_Io(Boolean);
   package Signed16_Io is
      new Ada.Text_Io.Integer_Io(Systemtypes.Signed16);

   -- Test harness actions
   type Keyword is (Section,     -- section marker in output
                    Comment,     -- print text as a comment
                    Cycle,       -- one cycle of the system
                    Cycle_Many,  -- multiple cycles of the system
                    Dump,        -- dump raw bus data
                    Check,       -- checking test configuration
                    Log,         -- logging information
                    -- Unit-specific commands
                    Clock,
                    Barometer,
                    If_Barometer,
                    Compass,If_Compass,
                    Airspeed,If_Airspeed,
                    Ins, If_Ins,
                    Fuel,If_Fuel,
                    Fuze,If_Fuze,
                    Radar,If_Radar,
                    Ir,If_Ir,
                    Steer,If_Steer,
                    Motor,If_Motor,
                    Destruct,If_Destruct,
                    Warhead,If_Warhead,
                    Environment,
                    Auxiliary,
                    Nav,
                    Missile,
                    -- All done
                    Done);
   package Keyword_Io is new Ada.Text_Io.Enumeration_Io(Keyword);

end Test_Keywords;
