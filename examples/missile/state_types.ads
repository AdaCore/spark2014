-- Types for component states
--
-- $Log: state_types.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.5  2003/08/27 20:36:09  adi
-- Added IR components
--
-- Revision 1.4  2003/08/22 18:26:19  adi
-- Added Radar action
--
-- Revision 1.3  2003/08/17 22:10:02  adi
-- Made state values more distinctr
--
-- Revision 1.2  2003/08/17 13:52:27  adi
-- Added lookup table and values
--
-- Revision 1.1  2003/08/17 13:34:26  adi
-- Initial revision
--
--
with Systemtypes;
--# inherit systemtypes;
package State_Types is

   subtype Word is Systemtypes.Unsigned16;

   -- Fuze action state
   type Fuze is (Unarmed, Arming, Live, Triggering, Timed_Out);

   type Fuze_To_Word is array(Fuze) of Word;
   Fuze_Values : constant Fuze_To_Word :=
     Fuze_To_Word'(Unarmed    => 16#0003#,
                   Arming     => 16#0006#,
                   Live       => 16#0030#,
                   Triggering => 16#0060#,
                   Timed_Out  => 16#0300#);

   function Fuze_Action(Val : Word) return Fuze;

   -- Radar action state
   type Radar is (Rad_Inactive, Ping, Sweep);

   type Radar_To_Word is array(Radar) of Word;
   Radar_Values : constant Radar_To_Word :=
     Radar_To_Word'(Rad_Inactive  => 16#0005#,
                    Ping  => 16#0006#,
                    Sweep => 16#0050#);

   function Radar_Action(Val : Word) return Radar;

   -- IR action state
   type Infrared is (Ir_Inactive, Ir_Stare, Ir_Sweep);

   type ir_To_Word is array(infrared) of Word;
   ir_Values : constant ir_To_Word :=
     ir_To_Word'(ir_Inactive => 16#0009#,
                 Ir_stare    => 16#0006#,
                 Ir_sweep    => 16#0090#);

   function ir_Action(Val : Word) return infrared;

end State_Types;
