------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--         P O L Y O R B _ H I . U N P R O T E C T E D _ Q U E U E          --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                   Copyright (C) 2014-2016 ESA & ISAE.                    --
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

with Ada.Real_Time;
with Ada.Unchecked_Conversion;

with PolyORB_HI_Generated.Deployment;

with PolyORB_HI.Port_Kinds;
with PolyORB_HI.Streams;

generic

   type Port_Type is (<>);
   --  This should be an enumeration type that represent the port list
   --  of a given thread.

   type Integer_Array is array (Port_Type) of Integer;
   --  An array type to specify the port FIFO sizes and urgencies.

   type Port_Kind_Array is array (Port_Type) of Port_Kinds.Port_Kind;
   --  An array type to specify the kind of each port.

   type Port_Image_Array is array (Port_Type) of
    PolyORB_HI_Generated.Deployment.Port_Sized_String;
   --  An array type to specify the image of each port.

   type Overflow_Protocol_Array is array (Port_Type) of
     Port_Kinds.Overflow_Handling_Protocol;
   --  An array to specify the overflow_handling_protocol of each port

   type Thread_Interface_Type (Port : Port_Type) is private;
   --  This is a discriminated record type that represents a thread
   --  port. The discriminant of this type must have a default value
   --  so that the type size can be computed at compile time.

   Current_Entity : in PolyORB_HI_Generated.Deployment.Entity_Type;
   --  Indicate the thread for which this package has been
   --  instantiated.

   Thread_Port_Kinds : in Port_Kind_Array;
   --  For each port, a value indicates the kind and the orientation
   --  of the port.

   Has_Event_Ports : in Boolean;
   --  True if Thread_Port_Kinds contains Event or Event Data ports

   Thread_Port_Images : in Port_Image_Array;
   --  For each port, a string indicates the image of the port.

   Thread_Fifo_Sizes : in Integer_Array;
   --  This array gives for each port the FIFO size (depending on the
   --  port nature or on an AADL property associated to the port. FIFO
   --  size for IN DATA ports is either 1 (immediate connection) or 2
   --  (delayed connection). In this case (data ports), the value must
   --  not be interpreted as a FIFO size but rather a way to support
   --  delayed connections. By convention, FIFO size for all OUT ports
   --  must be set to -1 by the code generator.

   Thread_Fifo_Offsets : in Integer_Array;
   --  This array holds an incremental value of the queue size for
   --  each IN [event] [data] port. For each IN [event] [data] port, the
   --  corresponding offset value is 1 + the sum of all queue sized of
   --  the ports declared before it. For other port kinds, the value
   --  must be 0. We give this array as a generic formal instead of
   --  computing it in this package to guarantee an O(1) access time
   --  for queue elements.

   Thread_Overflow_Protocols : in Overflow_Protocol_array;
   --  This array gives for each port the Overflow_Handling_Protocol
   --  depending on the AADL property associated to the port.

   Urgencies : in Integer_Array;
   --  This array gives for each port the Urgency depending on the
   --  AADL property associated to the port.

   Global_Data_Queue_Size : in Integer;
   --  The sum of all IN [event] [data] port queue sizes. Giving this
   --  value as a generic formal in spite of the possibility of
   --  deducing it from Thread_Fifo_Sizes is done to guarantee static
   --  allocation of the global message queue of the thread.

package PolyORB_HI.Unprotected_Queue
  with Abstract_State => (Elaborated_Variables),
       Initializes => Elaborated_Variables

is

   use Ada.Real_Time;
   use PolyORB_HI_Generated.Deployment;
   use PolyORB_HI.Streams;

   --  The types and the routines below give a flexible way to handle
   --  Thread_Interface_Type variables and to store them in arrays.

   type Port_Stream is
     new PolyORB_HI.Streams.Stream_Element_Array
     (1 .. Thread_Interface_Type'Size / 8);

   Null_Port_Stream : constant Port_Stream := (others => 0);

   type Port_Stream_Entry is record
      From    : Entity_Type;
      Payload : Port_Stream;
   end record;
   --  A couple of a message and its sender

   Null_Port_Stream_Entry : constant Port_Stream_Entry
     := (Entity_Type'First, Null_Port_Stream);

   N_Ports : constant Integer :=
     Port_Type'Pos (Port_Type'Last) - Port_Type'Pos (Port_Type'First) + 1;
   --  Number of ports in the thread

   function Interface_To_Stream is
      new Ada.Unchecked_Conversion (Thread_Interface_Type, Port_Stream);
   function Stream_To_Interface is
      new Ada.Unchecked_Conversion (Port_Stream, Thread_Interface_Type);

   function CE return String;
   pragma Inline (CE);
   --  Shortcut to Entity_Image (Current_Entity)

   type Port_Stream_Array is array (Port_Type) of Port_Stream_Entry;

   subtype Big_Port_Index_Type is Integer range 0 .. Global_Data_Queue_Size;

   Default_Index_Value : constant Big_Port_Index_Type
     := (if Global_Data_Queue_Size > 0 then 1 else 0);

   type Big_Port_Stream_Array is
     array (Big_Port_Index_Type) of Port_Stream_Entry;
   type Big_Port_Type_Array is array (Big_Port_Index_Type) of Port_Type;
   --  FIXME: We begin by 0 although the 0 position is unused. We do
   --  this to avoid compile time warning. After this package is
   --  deeply tested, begin by 1 and disable Index_Check and
   --  Range_Check for the Big_Port_Stream_Array type.

   type Port_Index_Array is array (Port_Type) of Big_Port_Index_Type;
   --  An array type to specify the port FIFO sizes and urgencies.

   procedure H_Increment_First (F : in out Big_Port_Index_Type);
   procedure H_Increment_Last  (L : in out Big_Port_Index_Type);
   pragma Inline (H_Increment_First);
   pragma Inline (H_Increment_Last);
   --  Cyclic incrementation and decrementation of F or L within the
   --  1..Global_Data_Queue_Size range.

   type Boolean_Array is array (Port_Type) of Boolean;
   type Time_Array is array (Port_Type) of Time;

   procedure Read_Event
     (P         : out Port_Type;
      Valid     : out Boolean;
      Not_Empty :     Boolean);
   --  Same as 'Wait_Event' but without blocking. Valid is set to
   --  False if there is nothing to receive.

   procedure Dequeue
     (T : Port_Type; P : out Port_Stream_Entry; Not_Empty : out Boolean);
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
   --  generally called just after Read_Out. However we cannot combine
   --  them in one routine because we need Read_Out to be a function
   --  and functions cannot modify protected object states.

   procedure Store_In
     (P : Port_Stream_Entry; T : Time; Not_Empty : out Boolean);
   --  Stores a new incoming message in its corresponding position. If
   --  this is an event [data] incoming message, then stores it in the
   --  queue, updates its most recent value and unblock the
   --  barrier. Otherwise, it only overrides the most recent value. T
   --  is the time stamp associated to the port P. In case of data
   --  ports with delayed connections, it indicates the instant from
   --  which the data of P becomes deliverable.

   procedure Store_Out (P : Port_Stream_Entry; T : Time);
   --  Store a value of an OUT port to be sent at the next call to
   --  Send_Output and mark the value as valid.

   function Count (T : Port_Type) return Integer;
   --  Return the number of pending messages on IN port T.

   function Get_Time_Stamp (P : Port_Type) return Time;
   --  Return the time stamp associated to port T

   --  The following are accessors to some internal data of the event queue

   function Get_Most_Recent_Value (P : Port_Type) return Port_Stream_Entry;
   procedure Set_Most_Recent_Value
     (P : Port_Type;
      S : Port_Stream_Entry;
      T : Time);
   --  The protected object contains also an array to store the values
   --  of received IN DATA ports as well as the most recent value of
   --  IN EVENT DATA. For OUT port, the value is the message to be
   --  send when Send_Output is called.
   --
   --  In case of an event data port, we do not use the 2 elements of
   --  the array to store most recent values because there is no
   --  delayed connections for event data ports.

end PolyORB_HI.Unprotected_Queue;
