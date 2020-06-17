------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--         P O L Y O R B _ H I . U N P R O T E C T E D _ Q U E U E          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                   Copyright (C) 2014-2015 ESA & ISAE.                    --
--                                                                          --
-- PolyORB-HI is free software; you can redistribute it and/or modify under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion. PolyORB-HI is distributed in the hope that it will be useful, but  --
-- WITHOUT ANY WARRANTY; without even the implied warranty of               --
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                     --
--                                                                          --
-- As a special exception under Section 7 of GPL version 3, you are granted --
-- additional permissions described in the GCC Runtime Library Exception,   --
-- version 3.1, as published by the Free Software Foundation.               --
--                                                                          --
-- You should have received a copy of the GNU General Public License and    --
-- a copy of the GCC Runtime Library Exception along with this program;     --
-- see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see    --
-- <http://www.gnu.org/licenses/>.                                          --
--                                                                          --
--              PolyORB-HI/Ada is maintained by the TASTE project           --
--                      (taste-users@lists.tuxfamily.org)                   --
--                                                                          --
------------------------------------------------------------------------------

with PolyORB_HI.Output;

package body PolyORB_HI.Unprotected_Queue
  with Refined_State => (Elaborated_Variables =>
                           (Global_Data_Queue,Firsts, Lasts, Empties,
                            Global_Data_History, GH_First, GH_Last,
                            Time_Stamps, Initialized,
                            Most_Recent_Values, Value_Put, N_Empties))
is

   Global_Data_Queue : Big_Port_Stream_Array
     := (others => Null_Port_Stream_Entry);
   --  The structure of the buffer is as follows:

   --  ----------------------------------------------------------------
   --  |   Q1   |     Q2      |       Q3        |  ... |      Qn      |
   --  ----------------------------------------------------------------
   --  O1       O2            O3                O4 ... On

   --  'On' is the offset associated to IN [event] [data] port n,
   --  given from the generic formal, Thread_FIFO_Offsets. This
   --  guarantees an O(1) access and storage time of a given
   --  element in the global queue. Intrinsically, the global table
   --  is a concatenation of circular arrays each one corresponding
   --  to a port queue.

   Firsts : Port_Index_Array := (Port_Type'Range => Default_Index_Value);
   Lasts  : Port_Index_Array := (Port_Type'Range => 0);
   --  Used for IN [event] [data] ports to navigate in the global
   --  queue. For IN DATA ports, in case of immediate connection
   --  only the 'Lasts' value is relevant and it is 0 or 1, in case
   --  of a delayed connection both values are relevant.

   Empties : Boolean_Array := (Port_Type'Range => True);
   --  Indicates whether each port-FIFO is empty or not

   Global_Data_History : Big_Port_Type_Array := (others => Port_Type'First);
   --  Note: this initialization should be useless

   GH_First            : Big_Port_Index_Type := Default_Index_Value;
   GH_Last             : Big_Port_Index_Type := 0;
   --  This contains, in an increasing chronological order the IN
   --  EVENT ports that have a pending event. Example (P_1, P_3,
   --  P_1, P_2, P_3) means that the oldest pending message is
   --  received on P_1 then on P_3, then on P_1 again and so on...

   --  FIXME: Add N_Ports to the array size to handle the case the
   --  thread has an IN event [data] port with a FIFO size equal to
   --  zero which is not supported yet.

   Most_Recent_Values : Port_Stream_Array
     := (Port_Type'Range => Null_Port_Stream_Entry);
   Time_Stamps        : Time_Array := (Port_Type'Range => Time_First);

   Initialized : Boolean_Array := (Port_Type'Range => False);
   --  To indicate whether the port ever received a data (or an
   --  event).

   Value_Put : Boolean_Array := (Port_Type'Range => False);
   --  To indicate whether the OUT port values have been set in
   --  order to be sent.

   N_Empties : Integer := N_Ports;
   --  Number of empty partial queues. At the beginning, all the
   --  queues are empty.

   use PolyORB_HI.Port_Kinds;
   use PolyORB_HI.Output;

   ----------------
   -- Read_Event --
   ----------------

   procedure Read_Event
     (P : out Port_Type;
      Valid : out Boolean;
      Not_Empty : Boolean)
   is
   begin
      Valid := Not_Empty;

      if Valid then
         P := Global_Data_History (GH_First);

         pragma Debug (Put_Line
                         (Verbose,
                          CE
                            + ": Read_Event: read valid event [data] on "
                            + Thread_Port_Images (P)));
      else
         P := Port_Type'First; -- It is assumed by construction that
                               --  this is an invalid port
      end if;
   end Read_Event;

   -------------
   -- Dequeue --
   -------------

   procedure Dequeue
     (T : Port_Type;
      P : out Port_Stream_Entry;
      Not_Empty : out Boolean)
   is
      Is_Empty  : Boolean renames Empties (T);
      First     : Big_Port_Index_Type renames Firsts (T);
      Last      : Big_Port_Index_Type renames Lasts (T);
      FIFO_Size : Integer renames Thread_FIFO_Sizes (T);
      P_Kind    : Port_Kind renames Thread_Port_Kinds (T);
      Offset    : Integer renames Thread_FIFO_Offsets (T);
   begin
      --  This subprogram is called only when the thread has IN
      --  ports.

      pragma Assert (Is_In (P_Kind));

      if Is_Empty then
         --  If the FIFO is empty, return the latest received value
         --  during the previous dispatches.

         pragma Debug (Put_Line
                         (Verbose,
                          CE
                            + ": Dequeue: Empty queue for "
                            + Thread_Port_Images (T)));

         P := Get_Most_Recent_Value (T);

      elsif FIFO_Size = 0 then
         --  If the FIFO is empty or non-existent, return the
         --  latest received value during the previous dispatches.

         pragma Debug (Put_Line
                         (Verbose,
                          CE
                            + ": Dequeue: NO FIFO for "
                            + Thread_Port_Images (T)));

         P := Get_Most_Recent_Value (T);

      else
         pragma Debug (Put_Line
                         (Verbose,
                          CE
                            + ": Dequeue: dequeuing "
                            + Thread_Port_Images (T)));

         if First = Last then
            --  Update the value of N_Empties only when this is the
            --  first time we mark the partial queue as empty.

            if not Is_Empty and then Is_Event (P_Kind) then
               N_Empties := N_Empties + 1;
            end if;

            Is_Empty := True;
         end if;

         P := Global_Data_Queue (First + Offset - 1);

         if First = FIFO_Size then
            First := Default_Index_Value;
         elsif Global_Data_Queue_Size > 0
           and then FIFO_Size > 1 then
            First := Big_Port_Index_Type'Succ (First);
         end if;

         --  Shift the First index of the global history queue

         H_Increment_First (GH_First);
      end if;

      --  Update the barrier

      Not_Empty := N_Empties < N_Ports;
   end Dequeue;

   -------------
   -- Read_In --
   -------------

   function Read_In (T : Port_Type) return Port_Stream_Entry is
      P         : Port_Stream_Entry;
      Is_Empty  : Boolean renames Empties (T);
      First     : Integer renames Firsts (T);
      FIFO_Size : Integer renames Thread_FIFO_Sizes (T);
      Offset    : Integer renames Thread_FIFO_Offsets (T);
      P_Kind    : Port_Kind renames Thread_Port_Kinds (T);
   begin
      --  This subprogram is called only when the thread has IN
      --  ports.

      pragma Assert (Is_In (P_Kind));

      if Is_Empty or else FIFO_Size = 0 then
         --  If the FIFO is empty or non-existent return the
         --  latest received value during the previous dispatches.

         pragma Debug (Put_Line
                         (Verbose,
                          CE
                            + ": Read_In: Empty queue for port "
                            + Thread_Port_Images (T)
                            + ". Reading the last stored value."));
         P := Get_Most_Recent_Value (T);
      else
         pragma Debug (Put_Line
                         (Verbose,
                          CE
                            + ": Read_In: Reading the oldest element in the"
                            + " queue of port  "
                            + Thread_Port_Images (T)));

         P := Global_Data_Queue (First + Offset - 1);
         pragma Debug (Put_Line
                         (Verbose,
                          CE
                            + ": Read_In: Global reading position: "
                            + Integer'Image (First + Offset - 1)));
      end if;

      pragma Debug (Put_Line
                      (Verbose,
                       CE
                         + ": Read_In: Value read from port "
                         + Thread_Port_Images (T)));
      return P;
   end Read_In;

   --------------
   -- Read_Out --
   --------------

   function Read_Out (T : Port_Type) return Port_Stream_Entry is
   begin
      --  There is no need here to go through the Get_ routine
      --  since we are sending, not receiving.

      pragma Debug (Put_Line
                      (Verbose,
                       CE
                         + ": Read_Out: Value read from port "
                         + Thread_Port_Images (T)));

      return Most_Recent_Values (T);
   end Read_Out;

   ----------------
   -- Is_Invalid --
   ----------------

   function Is_Invalid (T : Port_Type) return Boolean is
   begin
      return not (Value_Put (T));
   end Is_Invalid;

   -----------------
   -- Set_Invalid --
   -----------------

   procedure Set_Invalid (T : Port_Type) is
   begin
      pragma Debug (Put_Line
                      (Verbose,
                       CE
                         + ": Set_Invalid: Setting INVALID for sending: port "
                         + Thread_Port_Images (T)));

      Value_Put (T) := False;
   end Set_Invalid;

   --------------
   -- Store_In --
   --------------

   procedure Store_In (P : Port_Stream_Entry; T : Time; Not_Empty : out Boolean) is
      Thread_Interface : constant Thread_Interface_Type
        := Stream_To_Interface (P.Payload);
      PT                : Port_Type renames Thread_Interface.Port;
      Is_Empty          : Boolean   renames Empties (PT);
      First             : Integer   renames Firsts (PT);
      Last              : Integer   renames Lasts (PT);
      P_Kind            : Port_Kind renames Thread_Port_Kinds (PT);
      FIFO_Size         : Integer   renames Thread_FIFO_Sizes (PT);
      Offset            : Integer   renames Thread_FIFO_Offsets (PT);
      Urgency           : Integer   renames Urgencies (PT);
      Overflow_Protocol : Overflow_Handling_Protocol
        renames Thread_Overflow_Protocols (PT);
      Replace           : Boolean := False;
   begin
      --  This subprogram is called only when the thread has IN
      --  ports.

      pragma Assert (Is_In (P_Kind));

      --  Set PT as initialized

      Initialized (PT) := True;

      if Is_Event (P_Kind) then
         if Has_Event_Ports then
            --  If the FIFO is full apply the overflow-policy
            --  indicated by the user.

            if FIFO_Size > 0 then
               if not Is_Empty
                 and then (Last = First - 1
                             or else (First = 1 and then Last = FIFO_Size))
               then
                  declare
                     Frst : Integer;
                     GDH : Big_Port_Type_Array renames Global_Data_History;
                  begin
                     case Overflow_Protocol is
                        when DropOldest =>
                           --  Drop the oldest element in the FIFO

                           Global_Data_Queue (First + Offset - 1) := P;
                           pragma Debug
                             (Put_Line
                                (Verbose,
                                 CE
                                   + ": Store_In: FIFO is full."
                                   + " Dropping oldest element."
                                   + " Global storage position: "
                                   + Integer'Image (First + Offset - 1)));

                           Last := First;

                           if First = FIFO_Size then
                              First := Default_Index_Value;
                           elsif Global_Data_Queue_Size > 0
                             and then FIFO_Size > 1
                           then
                              First := Big_Port_Index_Type'Succ (First);
                           end if;

                           --  Search the oldest element in the history

                           Frst := GH_First;
                           loop
                              if GDH (Frst) = PT then
                                 exit;
                              end if;
                              Frst := Frst + 1;
                              if Frst > Global_Data_Queue_Size then
                                 exit;
                              end if;
                           end loop;

                           if Frst > Global_Data_Queue_Size then
                              --  Second configuration, We have only
                              --  searched from GH_First to Queue_Size,
                              --  continue from the beginning to GH_Last.

                              --  ---------------------------------------------
                              --  |xxxxxxxxx|x|               |x|xxxxxxxxxxxxx|
                              --  ---------------------------------------------
                              --   1         GH_Last          GH_First    Queue_Size
                              Frst := 1;
                              loop
                                 exit when GDH (Frst) = PT;
                                 Frst := Frst + 1;
                              end loop;
                           end if;

                        when DropNewest =>
                           --  Drop the newest element in the FIFO

                           Global_Data_Queue (Last + Offset - 1) := P;
                           pragma Debug
                             (Put_Line
                                (Verbose,
                                 CE
                                   + ": Store_In: FIFO is full."
                                   + " Dropping newest element"
                                   + " Global storage position: "
                                   + Integer'Image (Last + Offset - 1)));

                           --  Search the newest element in the history

                           Frst := GH_Last;
                           loop
                              if GDH (Frst) = PT then
                                 exit;
                              end if;
                              Frst := Frst - 1;
                              if Frst < 1 then
                                 exit;
                              end if;
                           end loop;

                           if Frst < 1 then
                              --  Continue the search from the end
                              Frst := Global_Data_Queue_Size;
                              loop
                                 exit when GDH (Frst) = PT;
                                 Frst := Frst - 1;
                              end loop;
                           end if;

                        when Error =>
                           Put_Line (Verbose,
                                     CE + ": Store_In: FIFO is full");
                           --  XXX SHould raise an exception there !
                           raise Program_Error;
                     end case;

                     --  Remove event in the history and shift
                     --  others with the same urgency

                     pragma Debug
                       (Put_Line
                          (Verbose,
                           CE
                             + ": Store_In: FIFO is full."
                             + " Removed element in history at"
                             + Integer'Image (Frst)));

                     loop
                        exit when Frst = Global_Data_Queue_Size
                          or else Urgencies (GDH (Frst)) < Urgency;
                        GDH (Frst) := GDH (Frst + 1);
                        Frst := Frst + 1;
                     end loop;

                     if Frst = Global_Data_Queue_Size
                       and then Urgencies (GDH (Frst)) < Urgency then
                        --  Continue suppressing from the beginning
                        Frst := 1;
                        GDH (Global_Data_Queue_Size) := GDH (Frst);
                        loop
                           exit when Urgencies (GDH (Frst)) < Urgency;
                           GDH (Frst) := GDH (Frst + 1);
                           Frst := Frst + 1;
                        end loop;
                     end if;
                  end;
                  Replace := True;
               else
                  --  Update the value of N_Empties only when this is the
                  --  first time we mark the partial queue as NOT empty.

                  if Is_Empty then
                     N_Empties := N_Empties - 1;
                  end if;

                  Is_Empty := False;

                  if Last = FIFO_Size then
                     Last := Default_Index_Value;
                  elsif Global_Data_Queue_Size  > 0 then
                     Last := Big_Port_Index_Type'Succ (Last);
                  end if;

                  Global_Data_Queue (Last + Offset - 1) := P;
                  pragma Debug (Put_Line
                                  (Verbose,
                                   CE
                                     + ": Store_In: Global storage position: "
                                     + Integer'Image (Last + Offset - 1)));

               end if;

               --  Update the oldest updated port value
               declare
                  Frst : Integer := GH_Last;
                  Lst  : constant Integer := GH_Last;
                  GDH  : Big_Port_Type_Array renames Global_Data_History;
               begin

                  --  Add an entry in the history
                  if not Replace then
                     H_Increment_Last (GH_Last);
                  end if;

                  if GH_First /= GH_Last then
                     --  Search the first entry with a higher urgency
                     --  and shift other entries
                     if Frst = Global_Data_Queue_Size
                       and then Urgencies (GDH (Frst)) < Urgency then
                        GDH (GH_Last) := GDH (Frst);
                        Frst := Frst - 1;
                     end if;
                     loop
                        if Urgencies (GDH (Frst)) >= Urgency then
                           exit;
                        end if;
                        GDH (Frst + 1) := GDH (Frst);
                        Frst := Frst - 1;
                        exit when (GH_First <= Lst
                                     and then Frst < GH_First)
                          or else Frst < 1;
                     end loop;

                     if Frst < 1 and then GH_First > Lst then
                        --  Continue the search from the end
                        Frst := Global_Data_Queue_Size;
                        if Urgencies (GDH (Frst)) < Urgency then
                           GDH (1 mod GDH'Length) := GDH (Frst);
                           Frst := Frst - 1;
                           loop
                              if Urgencies (GDH (Frst)) >= Urgency then
                                 exit;
                              end if;
                              GDH (Frst + 1) := GDH (Frst);
                              Frst := Frst - 1;
                              exit when Frst < GH_First;
                           end loop;
                        end if;
                     end if;
                  end if;

                  --  Insert the port of the event
                  if Frst = Global_Data_Queue_Size then
                     GDH (1 mod GDH'Size) := PT;
                     --  The modulo avoids warning when accessing
                     --  GDH (1) while Queue_Size = 0
                     pragma Debug (Put_Line
                                     (Verbose,
                                      CE
                                        + ": Store_In: Insert event"
                                        + " in history at: "
                                      + Integer'Image (1)));
                  else
                     GDH (Frst + 1) := PT;
                     pragma Debug (Put_Line
                                     (Verbose,
                                      CE
                                        + ": Store_In: Insert event"
                                        + " in history at: "
                                        + Integer'Image (Frst + 1)));
                  end if;
               end;

            end if;

            --  Update the most recent value corresponding to port PT

            Set_Most_Recent_Value (PT, P, T);

            pragma Debug (Put_Line
                            (Verbose,
                             CE
                               + ": Store_In: Enqueued Event [Data] message"
                               + " for port "
                               + Thread_Port_Images (PT)));

            --  Update the barrier

            Not_Empty := True;
         else
            Not_Empty := False; --  No need to update the barrier
         end if;

      else
         --  If this is a data port, we only override the
         --  Most_Recent_Value corresponding to the port.

         pragma Debug (Put_Line
                       (Verbose,
                        CE
                          + ": Store_In: Storing Data message in DATA port "
                          + Thread_Port_Images (PT)));

         Set_Most_Recent_Value (PT, P, T);

         pragma Debug (Put_Line
                       (Verbose,
                        CE
                          + ": Store_In: Stored Data message in DATA port "
                          + Thread_Port_Images (PT)));

         Not_Empty := False; --  No need to update the barrier
      end if;
   end Store_In;

   ---------------
   -- Store_Out --
   ---------------

   procedure Store_Out (P : Port_Stream_Entry; T : Time) is
    Thread_Interface : constant Thread_Interface_Type
      := Stream_To_Interface (P.Payload);
      PT               : Port_Type  := Port_Type'First;
        --renames Thread_Interface.Port;
   begin
      pragma Debug (Put_Line
                      (Verbose,
                       CE
                         + ": Store_Out: Storing value for sending: port "
                         + Thread_Port_Images (PT)));

      --  Mark as valid for sending

      Value_Put (PT) := True;

      pragma Debug (Put_Line
                      (Verbose,
                       CE
                         + ": Store_Out: Value stored for sending: port "
                         + Thread_Port_Images (PT)));

      --  No need to go through the Set_ routine since we are
      --  sending, not receiving.

      Most_Recent_Values (PT) := P;
      Time_Stamps (PT) := T; -- overwritten below
                             --  Maxime workaround for backdoor accesses
                             --      Time_Stamps (PT) := Ada.Real_time.clock;
   end Store_Out;

   -----------
   -- Count --
   -----------

   function Count (T : Port_Type) return Integer is
      Is_Empty  : Boolean renames Empties (T);
      First     : Integer renames Firsts (T);
      Last      : Integer renames Lasts (T);
      P_Kind    : Port_Kind renames Thread_Port_Kinds (T);
      FIFO_Size : Integer renames Thread_FIFO_Sizes (T);
   begin
      --  This subprogram is called only when the thread has IN
      --  ports.

      pragma Assert (Is_In (P_Kind));

      if not Initialized (T) then
         pragma Debug (Put_Line
                         (Verbose,
                          CE
                            + ": Count: Not initialized port: "
                            + Thread_Port_Images (T)));

         return -1;

      elsif Is_Empty then
         pragma Debug (Put_Line
                         (Verbose,
                          CE
                            + ": Count: Empty FIFO for port "
                            + Thread_Port_Images (T)));

         return 0;

      elsif FIFO_Size = 0 then
         pragma Debug (Put_Line
                         (Verbose,
                          CE
                            + ": Count: No FIFO for port "
                            + Thread_Port_Images (T)));

         return 0;

      else
         pragma Debug (Put_Line
                         (Verbose,
                          CE
                            + ": Count: FIFO exists for port "
                            + Thread_Port_Images (T)));

         if Last >= First then
            --  First configuration

            --  -------------------------------------------------------
            --  |         |x|xxxxxxxxxxxxxxxxxxxxxxxxx|x|             |
            --  -------------------------------------------------------
            --            First                       Last

            return (Last - First) + 1;

         else
            --  Second configuration

            --  -------------------------------------------------------
            --  |xxxxxxxxx|x|                         |x|xxxxxxxxxxxxx|
            --  -------------------------------------------------------
            --            Last                        First

            return FIFO_Size - First + Last + 1;
         end if;
      end if;
   end Count;

   ---------------------------
   -- Get_Most_Recent_Value --
   ---------------------------

   function Get_Most_Recent_Value
     (P : Port_Type)
     return Port_Stream_Entry
   is
      --      pragma SPARK_Mode (Off);
      First     : Integer renames Firsts (P);
      Last      : Integer renames Lasts (P);
      P_Kind    : Port_Kind renames Thread_Port_Kinds (P);
      FIFO_Size : Integer renames Thread_FIFO_Sizes (P);
      Offset    : Integer renames Thread_FIFO_Offsets (P);
      T         : constant Time := Time_First; -- Clock;
      --  XXX Actually, T should be decided depending on the freezing
      --  time of the port value

      S         : Port_Stream_Entry;
   begin
      if Is_Event (P_Kind)
        and then Has_Event_Ports
      then
         pragma Debug
           (Put_Line
            (Verbose,
             CE
               + ": Get_Most_Recent_Value: event [data] port "
               + Thread_Port_Images (P)));

         S := Most_Recent_Values (P);
      else
         if FIFO_Size = 1 then
            --  Immediate connection

            pragma Debug
              (Put_Line
                 (Verbose,
                  CE
                    + ": Get_Most_Recent_Value: data port "
                    + Thread_Port_Images (P)
                    + ". Immediate connection"));
            pragma Debug
              (Put_Line
                 (Verbose,
                  CE
                    + ": Get_Most_Recent_Value: First  ="
                    + Integer'Image (First)));
            pragma Debug
              (Put_Line
                 (Verbose,
                  CE
                    + ": Get_Most_Recent_Value: Last  = "
                    + Integer'Image (Last)));
            pragma Debug
              (Put_Line
                 (Verbose,
                  CE
                    + ": Get_Most_Recent_Value: Offset = "
                    + Integer'Image (Offset)));
            pragma Debug
              (Put_Line
                 (Verbose,
                  CE
                    + ": Get_Most_Recent_Value: Global_Data_Queue_Size = "
                    + Integer'Image (Global_Data_Queue_Size)));

            S :=  Global_Data_Queue (First + Offset - 1);

            pragma Debug
              (Put_Line
                 (Verbose,
                  CE
                    + ": Get_Most_Recent_Value: Most recent value for"
                    + " data port "
                    + Thread_Port_Images (P)
                    + " got. Immediate connection"));
         else
            --  Delayed connection: The element indexed by First is
            --  the oldest element and the element indexed by Last
            --  is the most recent element.

            pragma Debug
              (Put_Line
                 (Verbose,
                  CE
                    + ": Get_Most_Recent_Value: data port "
                    + Thread_Port_Images (P)
                    + ". Delayed connection"));
            pragma Debug
              (Put_Line
                 (Verbose,
                  CE
                    + ": Get_Most_Recent_Value: First  = "
                    + Integer'Image (First)));
            pragma Debug
              (Put_Line
                 (Verbose,
                  CE
                    + ": Get_Most_Recent_Value: Last  = "
                    + Integer'Image (Last)));
            pragma Debug
              (Put_Line
                 (Verbose,
                  " Offset = " + Integer'Image (Offset)));
            pragma Debug
              (Put_Line
                 (Verbose,
                  CE
                    + ": Get_Most_Recent_Value: Global_Data_Queue_Size = "
                    + Integer'Image (Global_Data_Queue_Size)));

            if Time_Stamps (P) <= T then
               pragma Debug
                 (Put_Line
                    (Verbose,
                     CE + ": Get_Most_Recent_Value: Getting NEW value"));

               S := Global_Data_Queue (Last + Offset - 1);
            else
               pragma Debug
                 (Put_Line
                    (Verbose,
                     CE + ": Get_Most_Recent_Value: Getting OLD value"));

               S := Global_Data_Queue (First + Offset - 1);
            end if;

            pragma Debug
              (Put_Line
                 (Verbose,
                  CE
                    + ": Get_Most_Recent_Value: Most recent value"
                    + " for data port "
                    + Thread_Port_Images (P)
                    + " got. Delayed connection"));
         end if;
      end if;

      return S;
   end Get_Most_Recent_Value;

   ---------------------------
   -- Set_Most_Recent_Value --
   ---------------------------

   procedure Set_Most_Recent_Value
     (P : Port_Type;
      S : Port_Stream_Entry;
      T : Time)
   is
      First     : Big_Port_Index_Type renames Firsts (P);
      Last      : Big_Port_Index_Type renames Lasts (P);
      P_Kind    : Port_Kind renames Thread_Port_Kinds (P);
      FIFO_Size : Integer renames Thread_FIFO_Sizes (P);
      Offset    : Integer renames Thread_FIFO_Offsets (P);
   begin
      if Global_Data_Queue_Size = 0 then
         --  XXX Actually, if the queue has a null size, this
         --  function is never called, hence we can exit
         --  immediatly. This should be captured with a proper
         --  pre-condition. We need this trap to avoid GNATprove
         --  attempting to prove the code below in this particular
         --  case.
         return;
      end if;

      if Has_Event_Ports then
         if Is_Event (P_Kind) then
            pragma Debug (Put_Line
                            (Verbose,
                             CE
                               + ": Set_Most_Recent_Value: event [data] port "
                               + Thread_Port_Images (P)));

            Most_Recent_Values (P) := S;

            pragma Debug (Put_Line
                            (Verbose,
                             CE
                               + ": Set_Most_Recent_Value: event [data] port "
                               + Thread_Port_Images (P)
                               + ". Done."));
         end if;
      end if;
      if not Is_Event (P_Kind) then
         Time_Stamps (P) := T;

         if FIFO_Size = 1 then
            --  Immediate connection

            pragma Debug
              (Put_Line
                 (Verbose,
                  CE
                    + ": Set_Most_Recent_Value: data port "
                    + Thread_Port_Images (P)
                    + ". Immediate connection"));
            pragma Debug
              (Put_Line
                 (Verbose,
                  CE
                    + ": Set_Most_Recent_Value: First  ="
                    + Integer'Image (First)));
            pragma Debug
              (Put_Line
                 (Verbose,
                  CE
                    + ": Set_Most_Recent_Value: Last  = "
                    + Integer'Image (Last)));
            pragma Debug
              (Put_Line
                 (Verbose,
                  CE
                    + ": Set_Most_Recent_Value: Offset = "
                    + Integer'Image (Offset)));
            pragma Debug
              (Put_Line
                 (Verbose,
                  CE
                    + ": Set_Most_Recent_Value: Global_Data_Queue_Size = "
                    + Integer'Image (Global_Data_Queue_Size)));

            Global_Data_Queue (First + Offset - 1) := S;

            pragma Debug
              (Put_Line
                 (Verbose,
                  CE
                    + ": Set_Most_Recent_Value: Most recent value"
                    + " for data port "
                    + Thread_Port_Images (P)
                    + " set. Immediate connection"));
         else
            --  Delayed connection: The element indexed by First must be
            --  the oldest element and the element indexed by Last
            --  is the most recent element.
            --  XXX JH: why?

            pragma Debug
              (Put_Line
                 (Verbose,
                  CE
                    + ": Set_Most_Recent_Value: data port "
                    + Thread_Port_Images (P)
                    + ". Delayed connection"));
            pragma Debug
              (Put_Line
                 (Verbose,
                  CE
                    + ": Set_Most_Recent_Value: First  = "
                    + Integer'Image (First)));
            pragma Debug
              (Put_Line
                 (Verbose,
                  CE
                    + ": Set_Most_Recent_Value: Last  = "
                    + Integer'Image (Last)));
            pragma Debug
              (Put_Line
                 (Verbose,
                  " Offset = " + Integer'Image (Offset)));
            pragma Debug
              (Put_Line
                 (Verbose,
                  CE
                    + ": Set_Most_Recent_Value: Global_Data_Queue_Size = "
                    + Integer'Image (Global_Data_Queue_Size)));

            Global_Data_Queue (First + Offset - 1) :=
              Global_Data_Queue (Last + Offset - 1);
            Global_Data_Queue (Last + Offset - 1)  := S;

            pragma Debug
              (Put_Line
                 (Verbose,
                  CE
                    + ": Set_Most_Recent_Value: Most recent value"
                    + " for data port "
                    + Thread_Port_Images (P)
                    + " set. Delayed connection"));
         end if;
      end if;
   end Set_Most_Recent_Value;

   --------------------
   -- Get_Time_Stamp --
   --------------------

   function Get_Time_Stamp (P : Port_Type) return Time is
   begin
      pragma Debug (Put_Line
                      (Verbose,
                       CE
                         + ": Get_Time_Stamp: port "
                         + Thread_Port_Images (P)));

      return Time_Stamps (P);
   end Get_Time_Stamp;

   -----------------------
   -- H_Increment_First --
   -----------------------

   procedure H_Increment_First (F : in out Big_Port_Index_Type) is
   begin
      if Big_Port_Index_Type'Last > 0 then
         if F < Big_Port_Index_Type'Last then
            F := Big_Port_Index_Type'Succ (F);
         else
            F := Default_Index_Value;
         end if;

         pragma Debug (Put_Line
                         (Verbose,
                          CE
                            + ": H_Increment_First: F ="
                            + Integer'Image (F)));
      end if;
   end H_Increment_First;

   ----------------------
   -- H_Increment_Last --
   ----------------------

   procedure H_Increment_Last (L : in out Big_Port_Index_Type) is
   begin
      if Big_Port_Index_Type'Last > 0 then
         if L < Big_Port_Index_Type'Last then
            L := Big_Port_Index_Type'Succ (L);
         else
            L := Default_Index_Value;
         end if;

      pragma Debug (Put_Line
                    (Verbose,
                     CE
                     + ": H_Increment_Last: L ="
                     + Integer'Image (L)));
      end if;
   end H_Increment_Last;

   --------
   -- CE --
   --------

   function CE return String is
   begin
      return Entity_Image (Current_Entity);
   end CE;

end PolyORB_HI.Unprotected_Queue;
