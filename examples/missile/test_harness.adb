-- Test harness for Missile Simulator
-- (Not really SPARK, just looks like it.)
-- Copyright (C) 2003-2003, Adrian J. Hilton
--
--    This program is free software; you can redistribute it and/or modify
--    it under the terms of the GNU General Public License as published by
--    the Free Software Foundation; either version 2 of the License, or
--    (at your option) any later version.
--
--    This program is distributed in the hope that it will be useful,
--    but WITHOUT ANY WARRANTY; without even the implied warranty of
--    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
--    GNU General Public License for more details.
--
--    You should have received a copy of the GNU General Public License
--    along with this program; if not, write to the Free Software
--    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
--
-- Author contact details:
--   E-mail adi@suslik.org
--   Web:   http://www.suslik.org/
--
-- $Log: test_harness.adb,v $
-- Revision 1.3  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
-- Revision 1.2  2004/01/25 18:09:28  adi
-- Added HTML for system description
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.15  2003/09/13 17:54:18  adi
-- Removed call to Missile.poll for now
--
-- Revision 1.14  2003/09/12 20:52:24  adi
-- Added Missile keyword
--
-- Revision 1.13  2003/09/07 20:25:42  adi
-- Added Nav
--
-- Revision 1.12  2003/09/01 19:08:28  adi
-- Updated for Destruct
--
-- Revision 1.11  2003/09/01 18:25:05  adi
-- Updated with Motor and Warhead
--
-- Revision 1.10  2003/08/31 21:04:20  adi
-- Added motor to live listr
--
-- Revision 1.9  2003/08/27 20:53:05  adi
-- Added Ir use
--
-- Revision 1.8  2003/08/25 20:25:29  adi
-- Added Radar object
--
-- Revision 1.7  2003/08/17 22:07:19  adi
-- Improved dump command
--
-- Revision 1.6  2003/08/17 13:30:11  adi
-- Added fuze
--
-- Revision 1.5  2003/08/17 12:59:33  adi
-- Added Fuel and harness for others
--
-- Revision 1.4  2003/08/12 18:21:22  adi
-- Added Auxiliary testing
--
-- Revision 1.3  2003/08/11 19:36:12  adi
-- Added Environment as an item
--
-- Revision 1.2  2003/08/10 16:55:47  adi
-- Added airspeed and others
--
-- Revision 1.1  2003/02/19 19:12:48  adi
-- Initial revision
--
-- Revision 1.2  2003/02/13 00:01:26  adi
-- Developed to a script-driven test harness
--
-- Revision 1.1  2003/02/11 23:21:12  adi
-- Initial revision
--
--
--
with Logging_Cfg,Logging;
with Ada.Text_Io,Ada.Integer_Text_Io;
with Test_Keywords;
with Barometer, If_Barometer,Ibit;
with Compass, If_Compass;
with Airspeed, If_Airspeed;
with Ins, If_Ins;
with Fuel, If_Fuel;
with Fuze, If_Fuze;
with Radar, If_Radar;
with Ir, If_Ir;
with Steer, If_Steer;
with Motor, If_Motor;
with Warhead, If_Warhead;
with Destruct, If_Destruct;
with Nav,Missile;
with Rt1553,Bc1553,Bus,Clock,environment;
with SystemTypes,MeasureTypes;
with Test,Test.Checking;
use type SystemTypes.Unsigned32;
procedure Test_Harness
is
   -- Measurements
   subtype Meter is Measuretypes.Meter;

   -- Utility types and packages
   subtype Comment_Range is Positive range 1..80;
   Blank : constant String(Comment_Range) := (others => ' ');

   -- Working variables
   S : String(Comment_Range) := Blank;
   N : Natural;
   I : Integer;
   Action : Test_Keywords.Keyword;

   procedure Cycle is
   begin
      -- Transmit info both ways
      Bus.Cycle;
      -- MCU
      If_Barometer.Poll;
      If_Compass.Poll;
      If_Airspeed.Poll;
      If_Ins.Poll;
      If_Fuel.Poll;
      If_Fuze.Poll;
      If_Radar.Poll;
      If_Ir.Poll;
      If_Steer.Poll;
      If_Motor.Poll;
      If_Warhead.Poll;
      If_Destruct.Poll;
      -- Missile
      --Missile.Poll;
      -- RTs
      Barometer.Cycle;
      Compass.Cycle;
      Airspeed.Cycle;
      Ins.cycle;
      Fuel.cycle;
      Fuze.Cycle;
      Radar.Cycle;
      Ir.Cycle;
      Steer.Cycle;
      Motor.Cycle;
      Warhead.Cycle;
      Destruct.Cycle;
      -- Log the data, if logging is active
      Logging.Log;
   end Cycle;

   procedure Dump is
     type Direction is (BC,RT);
     package Direction_Io is new Ada.Text_Io.Enumeration_Io(Direction);

     package Rt_Lru_io is new Ada.Text_Io.Enumeration_Io(Rt1553.Lru_Name);
     package Bc_Lru_io is new Ada.Text_Io.Enumeration_Io(Bc1553.Lru_Name);

     D : Direction;
     Lrt : Rt1553.Lru_Name;
     Lbc : Bc1553.Lru_Name;
   begin
      Direction_Io.Get(D);
      -- Now dump out the info
      -- One word received by the RT:
      case D is
         when Rt =>
            Rt_Lru_Io.Get(Lrt);
            Test.Comment("RT " & Rt1553.Lru_Name'Image(Lrt) & " 1");
            Bus.Show_RT(Subaddress_Idx => 1,
                        Dest => Rt1553.Lru_Number(Lrt));
         when Bc =>
            Bc_Lru_Io.Get(Lbc);
            Test.Comment("BC " & Bc1553.Lru_Name'Image(Lbc) & " 1");
            Bus.Show_BC(Subaddress_Idx => 1,
                        Src => Bc1553.Lru_Number(Lbc));
      end case;
   end Dump;

   procedure Test_Aux is separate;
begin -- Test_Harness
   loop
      Test_Keywords.Keyword_Io.Get(Action);
      case Action is
         when Test_Keywords.Log =>
            Logging.Process_Logging;
         when Test_Keywords.Auxiliary =>
            Test.Section("Simulator auxiliary tests");
            Test_Aux;
         when Test_Keywords.Section =>
            Ada.Text_Io.Get_Line(S,N);
            Test.Section(S);
            S := Blank;
         when Test_Keywords.Comment =>
            Ada.Text_Io.Get_Line(S,N);
            Test.Comment(S);
            S := Blank;
         when Test_Keywords.Cycle =>
            Cycle;
         when Test_Keywords.Cycle_Many =>
            Ada.Integer_Text_Io.Get(I);
            for Iterate in Integer range 1..I loop
               Cycle;
            end loop;
         when Test_Keywords.Dump =>
            Dump;
         when Test_Keywords.Check =>
            --Test.Checking.Command;
            null;
         when Test_Keywords.Clock =>
            Clock.Command;
         when Test_Keywords.Barometer =>
            Barometer.Command;
         when Test_Keywords.If_Barometer =>
            If_Barometer.Command;
         when Test_Keywords.Compass =>
            Compass.Command;
         when Test_Keywords.If_Compass =>
            If_Compass.Command;
         when Test_Keywords.Airspeed =>
            Airspeed.Command;
         when Test_Keywords.If_airspeed =>
            If_airspeed.Command;
         when Test_Keywords.Ins =>
            Ins.Command;
         when Test_Keywords.If_Ins =>
            If_Ins.Command;
         when Test_Keywords.Fuel =>
            Fuel.Command;
         when Test_Keywords.If_Fuel =>
            If_Fuel.Command;
         when Test_Keywords.Fuze =>
            Fuze.Command;
         when Test_Keywords.If_Fuze =>
            If_Fuze.Command;
         when Test_Keywords.radar =>
            radar.Command;
         when Test_Keywords.If_radar =>
            If_radar.Command;
         when Test_Keywords.ir =>
            ir.Command;
         when Test_Keywords.If_ir =>
            If_ir.Command;
         when Test_Keywords.Steer =>
            Steer.Command;
         when Test_Keywords.If_Steer =>
            If_Steer.Command;
         when Test_Keywords.motor =>
            motor.Command;
         when Test_Keywords.If_motor =>
            If_motor.Command;
         when Test_Keywords.Warhead =>
            Warhead.Command;
         when Test_Keywords.If_Warhead =>
            If_Warhead.Command;
         when Test_Keywords.Destruct =>
            Destruct.Command;
         when Test_Keywords.If_Destruct =>
            If_Destruct.Command;
         when Test_Keywords.Environment =>
            Environment.Command;
         when Test_Keywords.Nav =>
            Nav.Command;
         when Test_Keywords.Missile =>
            Missile.Command;
         when Test_Keywords.Done =>
            exit;
      end case;
   end loop;

   -- Finished
   Test.Done;
   Logging.Finish_Logging;
end Test_Harness;
