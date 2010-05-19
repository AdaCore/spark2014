-- Self-destruct configuration body
--
-- $Log: destruct_cfg.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/01 19:13:11  adi
-- Initial revision
--
--
package body Destruct_Cfg
is
   function Code_To_State(C : Systemtypes.Unsigned16)
                         return State
   is
      Ans : State;
   begin
      if C = State_To_Code(Inactive) then
         ans := Inactive;
      elsif C = State_To_Code(Armed) then
         ans := Armed;
      elsif C = State_To_Code(detonated) then
         ans := Detonated;
      else
         Ans := Inactive;
      end if;
      return Ans;
   end Code_To_State;

   function Transition(Old_state : State;
                       New_Code  : Systemtypes.Unsigned16)
                      return State
   is
      Ans : State := inactive;
   begin
      case Old_State is
         when Inactive =>
            if Code_To_State(New_Code) = Armed then
               Ans := Armed;
            end if;
         when armed =>
            if Code_To_State(New_Code) = Detonated then
               Ans := Detonated;
            end if;
         when Detonated =>
            Ans := Inactive;
      end case;
      return Ans;
   end Transition;

end Destruct_Cfg;

