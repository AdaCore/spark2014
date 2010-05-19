-- Warhead configuration body
--
-- $Log: warhead_cfg.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/01 18:26:48  adi
-- Initial revision
--
--
package body Warhead_Cfg
is
   function Code_To_State(C : Systemtypes.Unsigned16)
                         return State
   is
      Ans : State;
   begin
      if C = State_To_Code(Inactive) then
         ans := Inactive;
      elsif C = State_To_Code(Awake) then
         ans := Awake;
      elsif C = State_To_Code(Armed) then
         ans := Armed;
      elsif C = State_To_Code(Final) then
         ans := Final;
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
            if Code_To_State(New_Code) = Awake then
               Ans := Awake;
            end if;
         when Awake =>
            if Code_To_State(New_Code) = Armed then
               Ans := Armed;
            end if;
         when Armed =>
            if Code_To_State(New_Code) = Final then
               Ans := Final;
            end if;
         when Final =>
            if Code_To_State(New_Code) = Detonated then
               Ans := Detonated;
            end if;
         when Detonated =>
            Ans := Inactive;
      end case;
      return Ans;
   end Transition;

end Warhead_Cfg;

