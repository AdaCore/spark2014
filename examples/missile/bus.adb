--
-- $Id: bus.adb,v 1.1.1.1 2004/01/12 19:29:12 adi Exp $
--
-- $Log: bus.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.9  2003/06/25 20:26:51  adi
-- Added checks to improve VCs
--
-- Revision 1.8  2003/02/12 23:39:51  adi
-- Fixed preservation of valid input
--
-- Revision 1.7  2003/02/12 23:26:29  adi
-- Corrected to handle bus message becoming valid
--
-- Revision 1.6  2003/02/12 21:20:28  adi
-- Added Show_X and Set_X_Message_Valid subprograms
--
-- Revision 1.5  2003/02/11 20:12:56  adi
-- Added valid and fresh checking fns
--
-- Revision 1.4  2003/02/05 22:41:55  adi
-- Improved clarity and simplified proof of RTCs
--
-- Revision 1.3  2003/02/03 23:14:54  adi
-- Added Acknowledge function
--
-- Revision 1.2  2003/02/03 19:47:38  adi
-- Made the message distribution uniform over LRUs
--
-- Revision 1.1  2003/02/03 18:13:25  adi
-- Initial revision
--
--
package body Bus
  --# own Inputs  is Shadow_Inputs,  Real_Inputs &
  --#     Outputs is shadow_outputs, Real_Outputs;
is
   type Raw_Messages is array(Valid_Msg_Index) of Message;
   -- Messages from RTs to BC
   Shadow_Inputs, Real_Inputs : Raw_Messages
     := Raw_Messages'(others=>Null_Message);
   -- Messages from BC to RTs
   Shadow_Outputs, Real_Outputs : Raw_Messages
     := Raw_Messages'(others=>Null_Message);

   -- Mapping each LRU to the right place in the message index

   -- Maximum number of subaddresses for a given LRU
   subtype Lru_Start_Index is All_Msg_Index
     range All_Msg_Index'First .. (All_Msg_Index'Last - Max_Lru_Subaddress);
   type Lru_Message_Record is record
      Initial   : Lru_Start_Index; -- 0 indicates invalid
      Msg_Count : Lru_Subaddress_Index; -- number of messages
   end record;
   type Bc_RT_Table is array(Lru_Index) of Lru_Message_Record;
   -- Temporary: 2 messages per LRU each way
   BC_To_RT : constant BC_RT_Table :=
     Bc_Rt_Table'(1 => Lru_Message_Record'(1,2),
                  2 => Lru_Message_Record'(3,2),
                  3 => Lru_Message_Record'(5,2),
                  4 => Lru_Message_Record'(7,2),
                  5 => Lru_Message_Record'(9,2),
                  6 => Lru_Message_Record'(11,2),
                  7 => Lru_Message_Record'(13,2),
                  8 => Lru_Message_Record'(15,2),
                  9 => Lru_Message_Record'(17,2),
                  10 => Lru_Message_Record'(19,2),
                  11 => Lru_Message_Record'(21,2),
                  12 => Lru_Message_Record'(23,2));

   RT_To_BC : constant BC_RT_Table :=
     Bc_Rt_Table'(1 => Lru_Message_Record'(1,2),
                  2 => Lru_Message_Record'(3,2),
                  3 => Lru_Message_Record'(5,2),
                  4 => Lru_Message_Record'(7,2),
                  5 => Lru_Message_Record'(9,2),
                  6 => Lru_Message_Record'(11,2),
                  7 => Lru_Message_Record'(13,2),
                  8 => Lru_Message_Record'(15,2),
                  9 => Lru_Message_Record'(17,2),
                  10 => Lru_Message_Record'(19,2),
                  11 => Lru_Message_Record'(21,2),
                  12 => Lru_Message_Record'(23,2));

   -- Make an RT-dest message valid
   procedure Set_RT_Message_Valid(Subaddress_Idx : in Lru_Subaddress_Index;
                                  Dest : in LRU_Index)
     --# global in out shadow_outputs;
     --# derives shadow_outputs from *, Subaddress_Idx, dest;
   is
      Placing : Lru_Message_record;
      Actual_Subaddress_Idx : Valid_Msg_Index;
   begin
      placing := Bc_To_Rt(Dest);
      if Placing.initial not in Valid_Msg_Index then
         -- Invalid write; no messages in this direction
         null;
      elsif Subaddress_Idx > Placing.Msg_Count then
         -- This message isn't valid
         null;
         else
            -- Work out which outputs message this is
            if Placing.Initial <= Lru_Start_Index'Last then
               -- We won't overflow
               Actual_Subaddress_Idx := Placing.Initial + (Subaddress_Idx - 1);
               -- Just write the data
               Shadow_Outputs(Actual_Subaddress_Idx).Valid := True;
            else
               -- Invalid write -- fell off the end
               null;
            end if;
      end if;
   end Set_RT_Message_Valid;

   -- Write out a word of data to the RT

   procedure Write_RT_Word(Data    : in Word;
                           Idx     : in Word_Index;
                           Subaddress_Idx : in Lru_Subaddress_Index;
                           Dest    : in LRU_Index)
     --# global in out shadow_outputs;
     --# derives shadow_outputs from *, data, idx, Subaddress_Idx, dest;
   is
      Placing : Lru_Message_record;
      Actual_Subaddress_Idx : Valid_Msg_Index;
   begin
      placing := Bc_To_Rt(Dest);
      if Placing.initial not in Valid_Msg_Index then
         -- Invalid write; no messages in this direction
         null;
      elsif Subaddress_Idx > Placing.Msg_Count then
         -- This message isn't valid
         null;
      else
         if Placing.Initial <= Lru_Start_Index'Last then
            -- Work out which outputs message this is
            Actual_Subaddress_Idx := Placing.Initial + (Subaddress_Idx - 1);
            -- Just write the data
            Shadow_Outputs(Actual_Subaddress_Idx).Data(Idx) := Data;
            Shadow_Outputs(Actual_Subaddress_Idx).Fresh := True;
         else
            -- Falls off the end
            null;
         end if;
      end if;
   end Write_RT_Word;


   procedure Write_RT_Message(Data    : in Message;
                              Subaddress_Idx : in Lru_Subaddress_Index;
                              Dest    : in LRU_Index)
     --# global in out shadow_outputs;
     --# derives shadow_outputs from *, data, Subaddress_Idx,dest;
   is
      Placing : Lru_Message_record;
      Actual_Subaddress_Idx : Valid_Msg_Index;
   begin
      Placing := Bc_To_Rt(Dest);
      if Placing.initial not in Valid_Msg_Index then
         -- Invalid write
         null;
      elsif Subaddress_Idx > Placing.Msg_Count then
         -- No such message number, too high
         null;
      else
         -- Work out which outputs message this is
         if Placing.Initial <= Lru_Start_Index'Last then
            Actual_Subaddress_Idx := Placing.Initial + (Subaddress_Idx - 1);
            -- Just write the data
            Shadow_Outputs(Actual_Subaddress_Idx) := Data;
            Shadow_Outputs(Actual_Subaddress_Idx).Fresh := True;
         else
            -- Fell off the end
            null;
         end if;
      end if;
   end Write_Rt_Message;


   procedure Set_BC_Message_Valid(Subaddress_Idx : in Lru_Subaddress_Index;
                                  Src     : in LRU_Index)
     --# global in out shadow_inputs;
     --# derives shadow_inputs from
     --#  *, Subaddress_Idx, src;
   is
      Placing : Lru_Message_record;
      Actual_Subaddress_Idx : Valid_Msg_Index;
   begin
      placing := Rt_to_bc(src);
      if Placing.initial not in Valid_Msg_Index then
         -- Invalid write
         null;
      elsif Subaddress_Idx > Placing.Msg_Count then
         -- Invalid message number
         null;
      else
         if Placing.Initial <= Lru_Start_Index'Last then
            -- Work out which outputs message this is
            Actual_Subaddress_Idx := Placing.Initial + (Subaddress_Idx - 1);
            -- Just write the data
            Shadow_Inputs(Actual_Subaddress_Idx).Valid := True;
         else
            -- Fell off the end
            null;
         end if;
      end if;
   end Set_BC_Message_Valid;

   -- Write out data to send to the BC destination

   procedure Write_BC_Word(Data    : in Word;
                           Idx     : in Word_Index;
                           Subaddress_Idx : in Lru_Subaddress_Index;
                           Src     : in LRU_Index)
     --# global in out shadow_inputs;
     --# derives shadow_inputs from
     --#  *, data, idx, Subaddress_Idx, src;
      is
      Placing : Lru_Message_record;
      Actual_Subaddress_Idx : Valid_Msg_Index;
   begin
      placing := Rt_to_bc(src);
      if Placing.initial not in Valid_Msg_Index then
         -- Invalid write
         null;
      elsif Subaddress_Idx > Placing.Msg_Count then
         -- Invalid message number
         null;
      elsif Placing.Initial > Lru_Start_Index'Last then
         -- Invalid write
         null;
      else
         -- Work out which outputs message this is
         Actual_Subaddress_Idx := Placing.Initial + (Subaddress_Idx - 1);
         -- Just write the data
         Shadow_Inputs(Actual_Subaddress_Idx).Data(Idx) := Data;
         Shadow_Inputs(Actual_Subaddress_Idx).Fresh := True;
      end if;
   end Write_Bc_Word;


   procedure Write_BC_Message(Data    : in Message;
                              Subaddress_Idx : in Lru_Subaddress_Index;
                              Src     : in LRU_Index)
     --# global in out shadow_inputs;
     --# derives shadow_inputs from
     --#  *, data, Subaddress_Idx, src;
   is
      Placing : Lru_Message_record;
      Actual_Subaddress_Idx : Valid_Msg_Index;
   begin
      Placing := Rt_To_Bc(src);
      if Placing.initial not in Valid_Msg_Index then
         -- Invalid write
         null;
      elsif Subaddress_Idx > Placing.Msg_Count then
         -- Invalid message number
         null;
      elsif Placing.Initial > Lru_Start_Index'Last then
         -- fall off end
         null;
      else
         -- Work out which outputs message this is
         Actual_Subaddress_Idx := Placing.Initial + (Subaddress_Idx - 1);
         -- Just write the data
         Shadow_Inputs(Actual_Subaddress_Idx) := Data;
         Shadow_Inputs(Actual_Subaddress_Idx).Fresh := True;
      end if;
   end Write_Bc_Message;


   -- Read data sent to an RT

   function Is_RT_Fresh(Dest : LRU_Index;
                        Subaddress_Idx : Lru_Subaddress_Index)
                       return Boolean
     --# global real_Outputs;
   is
      Placing : Lru_Message_record;
      Actual_Subaddress_Idx : Valid_Msg_Index;
      Result : Boolean;
   begin
      Placing := BC_To_RT(Dest);
      if Placing.Initial not in Valid_Msg_Index then
         Result := False;
      elsif Subaddress_Idx > Placing.Msg_Count then
         -- Invalid message
         Result := False;
      elsif Placing.Initial > Lru_Start_Index'Last then
         -- Fell off end
         Result := False;
      else
         Actual_Subaddress_Idx := Placing.Initial + (Subaddress_Idx - 1);
         Result := Real_Outputs(Actual_Subaddress_Idx).Fresh;
      end if;
      return Result;
   end Is_RT_Fresh;

   function Is_RT_Valid(Dest : LRU_Index;
                        Subaddress_Idx : Lru_Subaddress_Index)
                       return Boolean
     --# global real_outputs;
   is
      Placing : Lru_Message_record;
      Actual_Subaddress_Idx : Valid_Msg_Index;
      Result : Boolean;
   begin
      Placing := BC_To_RT(Dest);
      if Placing.Initial not in Valid_Msg_Index then
         Result := False;
      elsif Subaddress_Idx > Placing.Msg_Count then
         -- Invalid message
         Result := False;
      elsif Placing.Initial > Lru_Start_Index'Last then
         -- Fell off end
         Result := False;
      else
         Actual_Subaddress_Idx := Placing.Initial + (Subaddress_Idx - 1);
         Result := Real_Outputs(Actual_Subaddress_Idx).valid;
      end if;
      return Result;
   end Is_RT_valid;

   procedure Read_RT_Word(Dest    : in LRU_Index;
                          Idx     : in Word_Index;
                          Subaddress_Idx : in Lru_Subaddress_Index;
                          Data    : out Word)
     --# global in real_outputs;
     --# derives data from dest, idx, Subaddress_Idx, real_outputs;
   is
      Placing : Lru_Message_record;
      Actual_Subaddress_Idx : Valid_Msg_Index;
   begin
      Placing := Bc_To_Rt(Dest);
      if Placing.Initial not in Valid_Msg_Index then
         Data := 0;
      elsif Subaddress_Idx > Placing.Msg_Count then
         -- Invalid message
         Data := 0;
      elsif Placing.Initial > Lru_Start_Index'Last then
         -- Fell off end
         Data := 0;
      else
         Actual_Subaddress_Idx := Placing.Initial + (Subaddress_Idx - 1);
         Data := Real_Outputs(Actual_Subaddress_Idx).Data(Idx);
      end if;
   end Read_Rt_Word;

   procedure Read_RT_Message(Dest    : in LRU_Index;
                             Subaddress_Idx : in Lru_Subaddress_Index;
                             Data    : out Message)
     --# global in real_outputs;
     --# derives data from dest, Subaddress_Idx, real_outputs;
   is
      Placing : Lru_Message_record;
      Actual_Subaddress_Idx : Valid_Msg_Index;
   begin
      Placing := Bc_To_Rt(Dest);
      if Placing.Initial not in Valid_Msg_Index then
         Data := Null_Message;
      elsif Subaddress_Idx > Placing.Msg_Count then
         -- Invalid message
         Data := Null_Message;
      elsif Placing.Initial > Lru_Start_Index'Last then
         -- Fell off end
         Data := Null_Message;
      else
         Actual_Subaddress_Idx := Placing.Initial + (Subaddress_Idx - 1);
         Data := Real_Outputs(Actual_Subaddress_Idx);
      end if;
   end Read_Rt_Message;

   -- Acknowledge a message as fresh
   procedure Acknowledge_RT_Message(Dest    : in LRU_Index;
                                    Subaddress_Idx : in Lru_Subaddress_Index)
     --# global in out real_outputs;
     --# derives real_outputs from *, dest, Subaddress_Idx;
   is
      Placing : Lru_Message_record;
      Actual_Subaddress_Idx : Valid_Msg_Index;
   begin
      Placing := Bc_To_Rt(Dest);
      if Placing.Initial in Valid_Msg_Index
        and then Placing.Initial in Lru_Start_Index
        and then Subaddress_Idx <= Placing.Msg_Count then
         --# assert Placing.Initial >= Valid_Msg_Index'First and
         --#        Placing.Initial <= Lru_Start_Index'Last;
         Actual_Subaddress_Idx := Placing.Initial + (Subaddress_Idx - 1);
         Real_Outputs(Actual_Subaddress_Idx).Fresh := False;
      else
         -- Invalid message
         null;
      end if;
   end Acknowledge_Rt_Message;


   -- Read data sent to the BC

   function Is_BC_Fresh(Src : LRU_Index;
                        Subaddress_Idx : Lru_Subaddress_Index)
                       return Boolean
     --# global real_inputs;
   is
      Placing : Lru_Message_record;
      Actual_Subaddress_Idx : Valid_Msg_Index;
      Result : Boolean;
   begin
      Placing := Rt_To_Bc(Src);
      if Placing.Initial not in Valid_Msg_Index then
         Result := False;
      elsif Subaddress_Idx > Placing.Msg_Count then
         -- Invalid message
         Result := False;
      elsif Placing.Initial > Lru_Start_Index'Last then
         -- Fell off end
         Result := False;
      else
         Actual_Subaddress_Idx := Placing.Initial + (Subaddress_Idx - 1);
         Result := Real_Inputs(Actual_Subaddress_Idx).fresh;
      end if;
      return Result;
   end Is_Bc_Fresh;

   function Is_BC_valid(Src : LRU_Index;
                        Subaddress_Idx : Lru_Subaddress_Index)
                       return Boolean
     --# global real_inputs;
   is
      Placing : Lru_Message_record;
      Actual_Subaddress_Idx : Valid_Msg_Index;
      Result : Boolean;
   begin
      Placing := Rt_To_Bc(Src);
      if Placing.Initial not in Valid_Msg_Index then
         Result := False;
      elsif Subaddress_Idx > Placing.Msg_Count then
         -- Invalid message
         Result := False;
      elsif Placing.Initial > Lru_Start_Index'Last then
         -- Fell off end
         Result := False;
      else
         Actual_Subaddress_Idx := Placing.Initial + (Subaddress_Idx - 1);
         Result := Real_Inputs(Actual_Subaddress_Idx).valid;
      end if;
      return Result;
   end Is_Bc_valid;


   procedure Read_BC_Word(Src     : in LRU_Index;
                          Idx     : in Word_Index;
                          Subaddress_Idx : in Lru_Subaddress_Index;
                          Data    : out Word)
     --# global in real_inputs;
     --# derives data from real_inputs, src, idx, Subaddress_Idx;
   is
      Placing : Lru_Message_record;
      Actual_Subaddress_Idx : Valid_Msg_Index;
   begin
      Placing := Rt_To_Bc(Src);
      if Placing.Initial not in Valid_Msg_Index then
         Data := 0;
      elsif Subaddress_Idx > Placing.Msg_Count then
         -- Invalid message
         Data := 0;
      elsif Placing.Initial > Lru_Start_Index'Last then
         -- Fell off end
         Data := 0;
      else
         Actual_Subaddress_Idx := Placing.Initial + (Subaddress_Idx - 1);
         Data := Real_Inputs(Actual_Subaddress_Idx).Data(Idx);
      end if;
   end Read_Bc_Word;

   procedure Read_BC_Message(Src     : in LRU_Index;
                             Subaddress_Idx : in Lru_Subaddress_Index;
                             Data    : out Message)
     --# global in real_inputs;
     --# derives data from real_inputs, src, Subaddress_Idx;
   is
      Placing : Lru_Message_record;
      Actual_Subaddress_Idx : Valid_Msg_Index;
   begin
      Placing := Rt_To_Bc(Src);
      if Placing.Initial not in Valid_Msg_Index then
         Data := Null_Message;
      elsif Subaddress_Idx > Placing.Msg_Count then
         -- invalid message
         Data := Null_message;
      elsif Placing.Initial > Lru_Start_Index'last then
         -- fell off end
         Data := Null_Message;
      else
         Actual_Subaddress_Idx := Placing.Initial + (Subaddress_Idx - 1);
         Data := Real_Inputs(Actual_Subaddress_Idx);
      end if;
   end Read_Bc_Message;

   procedure Acknowledge_BC_Message(Src     : in LRU_Index;
                                    Subaddress_Idx : in Lru_Subaddress_Index)
     --# global in out real_inputs;
     --# derives real_inputs from *, src, Subaddress_Idx;
   is
      Placing : Lru_Message_record;
      Actual_Subaddress_Idx : Valid_Msg_Index;
   begin
      Placing := Rt_To_Bc(Src);
      if Placing.Initial in Valid_Msg_Index
        and then Placing.Initial in Lru_Start_Index
        and then Subaddress_Idx <= Placing.Msg_Count then
         --# assert Placing.Initial <= Lru_Start_Index'Last and
         --#        Placing.Initial >= Valid_Msg_Index'First;
         Actual_Subaddress_Idx := Placing.Initial + (Subaddress_Idx - 1);
         Real_Inputs(Actual_Subaddress_Idx).Fresh := False;
      else
         -- invalid message
         null;
      end if;
   end Acknowledge_Bc_Message;

   -- Run a cycle of the bus
   procedure Cycle
     --# global in out real_inputs, shadow_inputs,
     --#               real_outputs, shadow_outputs;
     --# derives
     --#   real_inputs from *, shadow_inputs &
     --#   shadow_inputs from *, real_inputs &
     --#   real_outputs from *, shadow_outputs &
     --#   shadow_outputs from *, real_outputs
     --# ;
   is
   begin
      -- Go through the shadow inputs, updating real inputs
      -- where needed.
      for I in Valid_Msg_Index loop
         --# assert I >= valid_msg_index'first and
         --#        I <= valid_msg_index'last;
         if Shadow_Inputs(I).Fresh or else
           (Shadow_Inputs(I).Valid and not
            Real_Inputs(I).Valid) then
            -- Need to update this
            Real_Inputs(I) := Shadow_Inputs(I);
            -- Ensure that we reset our data
            Shadow_Inputs(I) := Null_Message;
            -- Data tends to remain valid
            Shadow_Inputs(I).Valid := Real_Inputs(I).Valid;
         end if;
         --# assert I >= valid_msg_index'first and
         --#        I <= valid_msg_index'last;
         if Shadow_Outputs(I).Fresh or else
           (Shadow_Outputs(I).Valid and not
            Real_Outputs(I).Valid) then
            -- Need to update this
            Real_Outputs(I) := Shadow_Outputs(I);
            -- Ensure that we reset our data
            Shadow_Outputs(I) := Null_Message;
            Shadow_Outputs(I).Valid := Real_Outputs(I).Valid;
         end if;
      end loop;
   end Cycle;

   procedure Dump(M : in out Message)
     --# derives M from *;
      is separate;

   -- Auxiliary debugging routines
   procedure Show_RT(Subaddress_Idx : in Lru_Subaddress_Index;
                     Dest : in LRU_Index)
   --# global in out real_Outputs;
   --# derives real_Outputs from *, Subaddress_Idx, Dest;
   is
      --# hide Show_RT;
      Msg : Message;
   begin
      Read_RT_Message(Dest => Dest,
                      Subaddress_Idx => Subaddress_Idx,
                      Data => Msg);
      Dump(Msg);
   end Show_RT; -- not SPARK, just sim aid

   procedure Show_BC(Subaddress_Idx : in Lru_Subaddress_Index;
                     Src : in LRU_Index)
   --# global in out real_Inputs;
   --# derives Real_Inputs from *, Subaddress_Idx, Src;
   is
      --# hide Show_BC;
      Msg : Message;
   begin
      Read_BC_Message(Src => Src,
                      Subaddress_Idx => Subaddress_Idx,
                      Data => Msg);
      Dump(Msg);
   end Show_BC; -- not SPARK, just sim aid

end Bus;

