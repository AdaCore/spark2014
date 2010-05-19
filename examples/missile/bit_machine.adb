-- Implementation of a bit machine type package
--
-- $Log: bit_machine.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/09/10 20:03:56  adi
-- Added Machine_Ticks counter
--
--
package body BIT_Machine
is

   procedure Create(Ticks_To_Complete : in SystemTypes.Unsigned16;
                    State : out Machine)
   is begin
      State := Machine'(Current_Phase => IBIT.Off,
                        Ticks => 0,
                        Fail_BIT => False,
                        Ticks_To_Complete => Ticks_To_Complete);
   end Create;

   procedure Change_State(Word : in Bus.Word;
                          State : in out Machine)
   is
   begin
      Ibit.RT_State_Machine(Bus_Data => Word,
                            Current_Phase => State.Current_Phase);
   end Change_State;


   function Phase(State : Machine) return IBIT.Phase
   is begin
      return State.Current_Phase;
   end Phase;

   function Machine_Ticks(State : Machine) return
     Systemtypes.Unsigned16
   is begin
      return State.Ticks;
   end Machine_Ticks;

   procedure Init(State : in out Machine)
   is begin
      State.Current_Phase := Ibit.In_Progress;
      State.Ticks := 0;
   end Init;

   procedure Halt(State : in out Machine)
   is begin
      State.Current_Phase := Ibit.off;
   end Halt;

   procedure Step(State : in out Machine)
   is begin
      case State.Current_Phase is
         when IBIT.Off =>
            -- Do nothing
            null;
         when IBIT.In_Progress =>
            State.Ticks := State.Ticks + 1;
            -- Complete BIT yet?
            if State.Ticks >= State.Ticks_To_Complete then
               -- Bit is complete
               State.Ticks := 0;
               if State.Fail_BIT then
                  State.Current_Phase := IBIT.Fail;
                  State.Fail_BIT := False;
               else
                  State.Current_Phase := IBIT.Pass;
               end if;
            end if;
         when IBIT.Pass | IBIT.Fail =>
            -- Do nothing other than reset ticks
            State.Ticks := 0;
            null;
         when IBIT.Request_Start | IBIT.Request_Stop |
           IBIT.Timeout =>
            State.Ticks := 0;
            -- Should never be here
            null;
      end case;
   end Step;

   -- Fail the next BIT
   procedure Fail_Next(State : in out Machine)
   is begin
      State.Fail_BIT := True;
   end Fail_Next;

   procedure Reset(State : in out Machine)
   is begin
      State.Current_Phase := IBIT.Off;
      State.Ticks := 0;
      State.Fail_BIT := False;
   end Reset;
end BIT_Machine;
