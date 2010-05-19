-- Fuel simulator implementation
--
-- $Log: fuel.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/17 11:57:19  adi
-- Initial revision
--
--
with Clock_Utils,SystemTypes;
with Bus,RT1553,IBIT,Bit_Machine;
package body Fuel
  --# own State is
  --#     Last_Level,
  --#     Last_Rate,
  --#     Last_Time,
  --#     BIT_State;
is
   subtype Kilo is Measuretypes.Kilo;
   subtype Gram_Per_Sec is Measuretypes.Gram_Per_Sec;

   Last_level : Measuretypes.Kilo := 0;
   Last_Rate  : Measuretypes.Gram_Per_Sec := 0;
   Last_Time  : Clock.Millisecond := Clock.Millisecond'First;
   Bit_State  : Bit_Machine.Machine := Bit_Machine.Initial_Machine;

   Bus_Id : constant Rt1553.Lru_Name := Rt1553.Fuel;

   -- Work out the current level.
   procedure Extrapolate_level(Level : out measuretypes.kilo)
     --# global in     Last_level, Last_Rate, Last_Time;
     --#        in out Clock.Time;
     --# derives Clock.Time from * &
     --#         Level from Clock.Time, Last_level,
     --#         Last_Rate, Last_Time;
   is
      Time_Now,T_Delta : Clock.Millisecond;
      Time_Valid : Boolean;

      -- Extrapolate mass loss from burn rate
      procedure Extrapolate_Mass(O : in Kilo;
                                 V : in gram_Per_Sec;
                                 N : out Kilo)
        --# global in t_delta;
        --# derives N from O, V, t_delta;
      is
         M_Delta : Kilo;
         VMS : Clock.Millisecond;
      begin
         if v < 0 then
            VMS := Clock.Millisecond(-v);
            -- Rate in grammes/sec, mass in kilos
            M_Delta := -Kilo((VMS * T_Delta)/1_000_000);
         else
            VMS := Clock.Millisecond(v);
            M_Delta := Kilo((VMS * T_Delta)/1_000_000);
         end if;
         -- Note that mass goes *down* wot
         N := O - M_Delta;
      end Extrapolate_mass;
   begin
      Clock.Read(T => Time_Now,
                 Valid => Time_Valid);
      if not Time_Valid then
        -- Can't extrapolate
         Level := 0;
      else
         -- How many seconds change
         T_Delta := Clock_Utils.Delta_Time(Last_Time,Time_Now);
         Extrapolate_mass(Last_level,
                               Last_Rate,
                               Level);
      end if;
   end Extrapolate_level;

   --------- Public subprograms

   -- Cycle the reading of data from the bus
   -- and writing of data to the bus
   procedure Cycle
     --# global in Last_level, Last_Time, Last_Rate;
     --#        in out BIT_State;
     --#        in out Clock.Time;
     --#        in Bus.Outputs;
     --#        in out Bus.Inputs;
     --# derives
     --#        BIT_State
     --#          from *, Bus.Outputs &
     --#        Bus.Inputs from *, Clock.Time,
     --#        Last_level, Last_Time,
     --#        Last_Rate, BIT_State &
     --#        Clock.Time from *;
   is
      Level : Measuretypes.Kilo;
      Datum : Bus.Word;

      procedure Write_Mass(M : in Kilo;
                           I : in Bus.Word_Index)
        --# global in out Bus.Inputs;
        --# derives Bus.Inputs from
        --#   *, M, I;
      is
      begin
         Rt1553.Write_Word(Data => Bus.Word(M),
                           Idx  => I,
                           Subaddress_Idx => 1,
                           Src => Bus_id);
      end Write_Mass;
   begin
      Extrapolate_level(level);
      -- Write the mass level info to T1 word 1
      Write_Mass(M => Level,
                 I => 1);
      -- Write the BIT phase to T1 word 2
      Rt1553.Write_Word(Data =>
                          IBIT.Phase_Lookup(BIT_Machine.Phase(Bit_State)),
                       Idx => 2,
                       Subaddress_Idx => 1,
                       Src => Bus_id);
      -- Read the BIT info off R1
      Rt1553.Read_Word(Src => Bus_id,
                       Idx => 1,
                       Subaddress_Idx => 1,
                       Data => Datum);
      BIT_Machine.Change_State(Word => Datum,
                               State => Bit_state);
      -- And cycle the BIT
      BIT_Machine.Step(Bit_State);
   end Cycle;

   -- Set the current level
   procedure Set_Level(level : in Measuretypes.Kilo)
   --# global    out Last_level, last_time;
   --#        in out Clock.Time;
   --# derives Clock.Time from * &
   --#         Last_level from level, Clock.Time &
   --#         Last_Time     from Clock.Time;
   is
      Time_Valid : Boolean;
   begin
      Last_level := level;
      Clock.Read(Last_Time,Time_Valid);
      if not Time_Valid then
         Last_level := 0;
      end if;
   end Set_level;

   -- Set the current burn rate
   procedure Set_rate(rate : in Measuretypes.gram_Per_Sec)
   --# global    out last_time, last_rate;
   --#        in out Clock.Time;
   --# derives Clock.Time from * &
   --#         Last_Time     from Clock.Time &
   --#         Last_rate from rate, Clock.Time;
   is
      Time_Valid : Boolean;
   begin
      Last_Rate := Rate;
      Clock.Read(Last_Time,Time_Valid);
      if not Time_Valid then
         Last_rate := 0;
      end if;
   end Set_rate;

   -- Read the current level
   procedure Read_Level(Level : out Measuretypes.kilo)
     --# global in     Last_level, Last_Time, Last_rate;
     --#        in out Clock.Time;
     --# derives Clock.Time from * &
     --#         level from last_level, Last_Time, last_rate,
     --#         Clock.Time;
   is
   begin
      Extrapolate_level(level);
   end Read_Level;

   procedure Fail_Next_Bit
     --# global in out BIT_State;
     --# derives BIT_State from *;
   is begin
      BIT_Machine.Fail_Next(Bit_State);
   end Fail_Next_Bit;

   procedure Init
     --# global out Last_level, Last_Time, Last_Rate, BIT_State;
     --#        in out Bus.Inputs;
     --# derives Last_level, Last_Time, last_rate, BIT_State from &
     --#        Bus.Inputs from *;
   is begin
      -- Initialise the bus message 1T
      RT1553.Set_Message_Valid(Subaddress_Idx => 1,
                               Src => Bus_id);
      -- Initialise the variables
      Last_level := 0;
      Last_Time     := Clock.Millisecond'First;
      Last_Rate := 0;
      BIT_Machine.Create(Ticks_To_Complete => 25,
                         State => Bit_State);
   end Init;

   procedure Command is separate;
end Fuel;
