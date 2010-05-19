-- Self-destruct configuration
--
-- $Log: destruct_cfg.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/01 19:13:07  adi
-- Initial revision
--
--
with Systemtypes;
--# inherit systemtypes;
package Destruct_Cfg
is

   type State is (Inactive,Armed,Detonated);

   type State_Code_Table is array (State) of
     Systemtypes.Unsigned16;

   -- Codes to command a change of state
   State_To_Code : constant State_Code_Table :=
     State_Code_Table'(Inactive  => 0,
                       Armed     => 16#39e0#,
                       Detonated => 16#9ab2#);

   function Code_To_State(C : Systemtypes.Unsigned16)
                         return State;

   function Transition(Old_state : State;
                       New_Code  : Systemtypes.Unsigned16)
     return State;

end destruct_Cfg;

