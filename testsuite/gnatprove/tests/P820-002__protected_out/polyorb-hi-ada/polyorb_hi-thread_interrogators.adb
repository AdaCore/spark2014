------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--      P O L Y O R B _ H I . T H R E A D _ I N T E R R O G A T O R S       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--    Copyright (C) 2007-2009 Telecom ParisTech, 2010-2016 ESA & ISAE.      --
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

with Ada.Unchecked_Conversion;

with PolyORB_HI.Output;
with PolyORB_HI.Protocols;
with PolyORB_HI.Port_Type_Marshallers;
with PolyORB_HI.Streams;
with PolyORB_HI.Time_Marshallers;
with POlyORB_HI.Utils;
with PolyORB_HI.Unprotected_Queue;

package body PolyORB_HI.Thread_Interrogators
  with Refined_State => (Elaborated_Variables => (Global_Queue),
                         UQ_S => (UQ.Elaborated_Variables))

is

   use type PolyORB_HI.Streams.Stream_Element_Offset;
   use PolyORB_HI.Port_Kinds;
   use Ada.Real_Time;
   use PolyORB_HI_Generated.Deployment;
   use PolyORB_HI.Output;
   use PolyORB_HI.Utils;

   --------
   -- UQ --
   --------

   package UQ is new PolyORB_HI.Unprotected_Queue
     (Port_Type,
      Integer_Array,
      Port_Kind_Array,
      Port_Image_Array,
--      Address_Array,
      Overflow_Protocol_Array,
      Thread_Interface_Type,
      Current_Entity,
      Thread_Port_Kinds,
      Has_Event_Ports,
      Thread_Port_Images,
      Thread_Fifo_Sizes,
      Thread_Fifo_Offsets,
      Thread_Overflow_Protocols,
      Urgencies,
      Global_Data_Queue_Size);--,
--      N_Destinations,
--      Destinations,
--      Marshall,
--      Next_Deadline);
   use UQ;

   ------------------
   -- Global_Queue --
   ------------------

   --  The protected object below handles all the received events or
   --  data on IN ports.
   --
   --  Finally, the protected object contains a second array to store
   --  the number of received values for each IN EVENT [DATA] (0 .. n)
   --  and IN DATA (0 .. 1) port.

   protected Global_Queue is
      pragma Priority (System.Priority'Last);

      entry Wait_Event (P : out Port_Type);
      --  Blocks until the thread receives a new event. Return the
      --  corresponding Port that received the event.

      procedure Read_Event (P : out Port_Type; Valid : out Boolean);
      --  Same as 'Wait_Event' but without blocking. Valid is set to
      --  False if there is nothing to receive.

      procedure Dequeue (T : Port_Type);
      --  Dequeue a value from the partial FIFO of port T. If there is
      --  no enqueued value, return the latest dequeued value.

      function Read_In (T : Port_Type) return Port_Stream_Entry;
      --  Read the oldest queued value on the partial FIFO of IN port
      --  T without dequeuing it. If there is no queued value, return
      --  the latest dequeued value.

      function Read_Out (T : Port_Type) return Port_Stream_Entry;
      --  Return the value put for OUT port T.

      function Is_Invalid (T : Port_Type) return Boolean;
      --  Return True if no Put_Value has been called for this port
      --  since the last Set_Invalid call.

      procedure Set_Invalid (T : Port_Type);
      --  Set the value stored for OUT port T as invalid to impede its
      --  future sending without calling Put_Value. This procedure is
      --  generally called just after Read_Out. However we cannot
      --  combine them in one routine because we need Read_Out to be a
      --  function and functions cannot modify protected object
      --  states.

      procedure Store_In (P : Port_Stream_Entry; T : Time);
      --  Stores a new incoming message in its corresponding
      --  position. If this is an event [data] incoming message, then
      --  stores it in the queue, updates its most recent value and
      --  unblock the barrier. Otherwise, it only overrides the most
      --  recent value. T is the time stamp associated to the port
      --  P. In case of data ports with delayed connections, it
      --  indicates the instant from which the data of P becomes
      --  deliverable.

      procedure Store_Out (P : Port_Stream_Entry; T : Time);
      --  Store a value of an OUT port to be sent at the next call to
      --  Send_Output and mark the value as valid.

      function Count (T : Port_Type) return Integer;
      --  Return the number of pending messages on IN port T.

      function Get_Time_Stamp (P : Port_Type) return Time;
      --  Return the time stamp associated to port T

   private

      Not_Empty : Boolean := False;
      --  The protected object barrier. True when there is at least
      --  one pending event [data].

   end Global_Queue;

   protected body Global_Queue is

      ----------------
      -- Wait_Event --
      ----------------

      entry Wait_Event (P : out Port_Type) when Not_Empty is
         Valid : Boolean;

      begin
         UQ.Read_Event (P, Valid, Not_Empty);

         pragma Debug (Put_Line
                       (Verbose,
                        CE
                        + ": Wait_Event: oldest unread event port = "
                        + Thread_Port_Images (P)));
      end Wait_Event;

      ----------------
      -- Read_Event --
      ----------------

      procedure Read_Event (P : out Port_Type; Valid : out Boolean) is
      begin
         UQ.Read_Event (P, Valid, Not_Empty);
      end Read_Event;

      -------------
      -- Dequeue --
      -------------

      procedure Dequeue (T : Port_Type) is
         P : Port_Stream_Entry;

      begin
         UQ.Dequeue (T, P, Not_Empty);
      end Dequeue;

      -------------
      -- Read_In --
      -------------

      function Read_In (T : Port_Type) return Port_Stream_Entry is
      begin
         return UQ.Read_In (T);
      end Read_In;

      --------------
      -- Read_Out --
      --------------

      function Read_Out (T : Port_Type) return Port_Stream_Entry is
      begin
         return UQ.Read_Out (T);
      end Read_Out;

      ----------------
      -- Is_Invalid --
      ----------------

      function Is_Invalid (T : Port_Type) return Boolean is
      begin
         return UQ.Is_Invalid (T);
      end Is_Invalid;

      -----------------
      -- Set_Invalid --
      -----------------

      procedure Set_Invalid (T : Port_Type) is
      begin
         UQ.Set_Invalid (T);
      end Set_Invalid;

      --------------
      -- Store_In --
      --------------

      procedure Store_In (P : Port_Stream_Entry; T : Time) is
      begin
         UQ.Store_In (P, T, Not_Empty);
      end Store_In;

      ---------------
      -- Store_Out --
      ---------------

      procedure Store_Out (P : Port_Stream_Entry; T : Time) is
      begin
         UQ.Store_Out (P, T);
      end Store_Out;

      -----------
      -- Count --
      -----------

      function Count (T : Port_Type) return Integer is
      begin
         return UQ.Count (T);
      end Count;

      --------------------
      -- Get_Time_Stamp --
      --------------------

      function Get_Time_Stamp (P : Port_Type) return Time is
      begin
         return UQ.Get_Time_Stamp (P);
      end Get_Time_Stamp;

   end Global_Queue;

   -----------------
   -- Send_Output --
   -----------------

   function Send_Output (Port : Port_Type) return Error_Kind is
      pragma SPARK_Mode (Off);

      type Port_Type_Array is array (Positive)
        of PolyORB_HI_Generated.Deployment.Port_Type;
      type Port_Type_Array_Access is access Port_Type_Array;

      function To_Pointer is new Ada.Unchecked_Conversion
        (System.Address, Port_Type_Array_Access);

      Dst       : constant Port_Type_Array_Access :=
        To_Pointer (Destinations (Port));
      N_Dst     : Integer renames N_Destinations (Port);
      P_Kind    : Port_Kind renames Thread_Port_Kinds (Port);

      Message   : aliased PolyORB_HI.Messages.Message_Type;
      Value     : constant Thread_Interface_Type := Stream_To_Interface
        (Global_Queue.Read_Out (Port).Payload);

      Error : Error_Kind := Error_None;
   begin
      pragma Debug (Put_Line (Verbose,
                              CE
                              + ": Send_Output: port "
                              + Thread_Port_Images (Port)));

      --  If no valid value is to be sent, quit

      if Global_Queue.Is_Invalid (Port) then
         pragma Debug (Put_Line (Verbose,
                                 CE
                                 + ": Send_Output: Invalid value in port "
                                 + Thread_Port_Images (Port)));

      else
         --  Mark the port value as invalid to impede future sendings

         Global_Queue.Set_Invalid (Port);

         --  Begin the sending to all destinations

         for To in 1 .. N_Dst loop
            --  First, we marshall the destination

            Port_Type_Marshallers.Marshall
              (Internal_Code (Dst (To)), Message);

            --  Then marshall the time stamp in case of a data port

            if not Is_Event (P_Kind) then
               Time_Marshallers.Marshall
                 (Global_Queue.Get_Time_Stamp (Port),
                  Message);
            end if;

            --  Then we marshall the value corresponding to the port

            Marshall (Value, Message);

            pragma Debug
              (Put_Line
               (Verbose,
                CE
                + ": Send_Output: to port "
                + PolyORB_HI_Generated.Deployment.Port_Image (Dst (To))
                + " of "
                + Entity_Image (Port_Table (Dst (To)))));

            Error := Protocols.Send (Current_Entity,
                                     Port_Table (Dst (To)),
                                     Message);

            PolyORB_HI.Messages.Reallocate (Message);

            if Error /= Error_None then
               return Error;
            end if;
         end loop;

         pragma Debug (Put_Line (Verbose,
                                 CE
                                 + ": Send_Output: port "
                                 + Thread_Port_Images (Port)
                                 + ". End."));
      end if;

      return Error;
   end Send_Output;

   ---------------
   -- Put_Value --
   ---------------

   procedure Put_Value (Thread_Interface : Thread_Interface_Type) is
   begin
    pragma Debug (Put_Line (Verbose, CE + ": Put_Value"));

      Global_Queue.Store_Out
        ((Current_Entity, Interface_To_Stream (Thread_Interface)),
         Next_Deadline);
   end Put_Value;

   -------------------
   -- Receive_Input --
   -------------------

   procedure Receive_Input (Port : Port_Type) is
      pragma Unreferenced (Port);
   begin
      --  raise Program_Error with CE + ": Receive_Input: Not implemented yet";
      null;
   end Receive_Input;

   ---------------
   -- Get_Value --
   ---------------

   procedure Get_Value (Port : Port_Type; T_Port : out Thread_Interface_Type) is
      Stream : constant Port_Stream := Global_Queue.Read_In (Port).Payload;

   begin
      T_Port := Stream_To_Interface (Stream);
      pragma Debug (Put_Line
                    (Verbose,
                     CE
                     + ": Get_Value: Value of port "
                     + Thread_Port_Images (Port)
                     + " got"));
   end Get_Value;

   ----------------
   -- Get_Sender --
   ----------------

   procedure Get_Sender (Port : Port_Type; Sender : out Entity_Type) is
   begin
      Sender := Global_Queue.Read_In (Port).From;
      pragma Debug (Put_Line
                    (Verbose,
                     CE
                     + ": Get_Sender: Value of sender to port "
                     + Thread_Port_Images (Port)
                     + " = "
                     + Entity_Image (Sender)));
   end Get_Sender;

   ---------------
   -- Get_Count --
   ---------------

   procedure Get_Count (Port : Port_Type; Count : out Integer) is
   begin
      Count := Global_Queue.Count (Port);
      pragma Debug (Put_Line (Verbose,
                              CE
                              + ": Get_Count: port "
                              + Thread_Port_Images (Port)
                              + " ="
                              + Integer'Image (Count)));

   end Get_Count;

   ----------------
   -- Next_Value --
   ----------------

   procedure Next_Value (Port : Port_Type) is
   begin
      pragma Debug (Put_Line (Verbose,
                              CE
                              + ": Next_Value for port "
                              + Thread_Port_Images (Port)));

      Global_Queue.Dequeue (Port);
   end Next_Value;

   ------------------------------
   -- Wait_For_Incoming_Events --
   ------------------------------

   procedure Wait_For_Incoming_Events (Port : out Port_Type) is
   begin
    pragma Debug (Put_Line (Verbose, CE + ": Wait_For_Incoming_Events"));

      Global_Queue.Wait_Event (Port);

      pragma Debug (Put_Line
                    (Verbose,
                     CE
                     + ": Wait_For_Incoming_Events: reception of"
                     + " event [Data] message on port "
                     + Thread_Port_Images (Port)));
   end Wait_For_Incoming_Events;

   --------------------
   -- Get_Next_Event --
   --------------------

   procedure Get_Next_Event (Port : out Port_Type; Valid : out Boolean) is
   begin
      Global_Queue.Read_Event (Port, Valid);

      if Valid then
         pragma Debug (Put_Line
                       (Verbose,
                        CE
                        + ": Get_Next_Event: read event [data] message"
                        + " for port "
                        + Thread_Port_Images (Port)));
      else
         pragma Debug (Put_Line
                       (Verbose,
                        CE
                        + ": Get_Next_Event: Nothing to read."));

      end if;
   end Get_Next_Event;

   ----------------------------
   -- Store_Received_Message --
   ----------------------------

   procedure Store_Received_Message
     (Thread_Interface : Thread_Interface_Type;
      From             : Entity_Type;
      Time_Stamp       : Ada.Real_Time.Time    := Ada.Real_Time.Clock)
   is
   begin
    pragma Debug (Put_Line (Verbose, CE + ": Store_Received_Message"));

      Global_Queue.Store_In
        ((From, Interface_To_Stream (Thread_Interface)), Time_Stamp);
   end Store_Received_Message;

   --------------------
   -- Get_Time_Stamp --
   --------------------

   function Get_Time_Stamp (P : Port_Type) return Time is
      pragma SPARK_Mode (Off);
   begin
      return Global_Queue.Get_Time_Stamp (P);
   end Get_Time_Stamp;

end PolyORB_HI.Thread_Interrogators;
