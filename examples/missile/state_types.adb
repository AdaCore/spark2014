-- Lookup functions for component states
--
-- $Log: state_types.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.3  2003/08/27 20:36:01  adi
-- Added IR components
--
-- Revision 1.2  2003/08/22 18:26:12  adi
-- Added Radar action
--
-- Revision 1.1  2003/08/17 13:52:15  adi
-- Initial revision
--
--
package body State_Types is
   function Fuze_Action(Val : Word) return Fuze
   is
      Act : Fuze;
   begin
      if Val = Fuze_Values(Unarmed) then
         Act := Unarmed;
      elsif Val = Fuze_Values(Arming) then
         Act := Arming;
      elsif Val = Fuze_Values(Live) then
         Act := Live;
      elsif Val = Fuze_Values(Triggering) then
         Act := Triggering;
      elsif Val = Fuze_Values(Timed_out) then
         Act := Timed_out;
      else
         -- Default
         Act := Unarmed;
      end if;
      return Act;
   end Fuze_Action;

   function Radar_Action(Val : Word) return radar
   is
      Act : Radar;
   begin
      if Val = Radar_Values(Rad_Inactive) then
         Act := Rad_inactive;
      elsif Val = Radar_Values(Ping) then
         Act := ping;
      elsif Val = Radar_Values(Sweep) then
         Act := Sweep;
      else
         -- Default
         Act := Rad_Inactive;
      end if;
      return Act;
   end radar_Action;

   function ir_Action(Val : Word) return Infrared
   is
      Act : Infrared;
   begin
      if Val = ir_Values(ir_Inactive) then
         Act := ir_inactive;
      elsif Val = ir_Values(Ir_stare) then
         Act := Ir_stare;
      elsif Val = ir_Values(Ir_sweep) then
         Act := Ir_sweep;
      else
         -- Default
         Act := ir_Inactive;
      end if;
      return Act;
   end ir_Action;

end State_Types;
