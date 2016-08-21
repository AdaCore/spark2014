------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--      P O L Y O R B _ H I . T H R E A D _ I N T E R R O G A T O R S       --
--                                                                          --
--                                 S p e c                                  --
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

--  This package contains a generic definition of the interrogation
--  functions that the AADL standard requires for thread ports.

with Ada.Real_Time;

with System;

with PolyORB_HI_Generated.Deployment; use PolyORB_HI_Generated.Deployment;
with PolyORB_HI.Errors; use PolyORB_HI.Errors;
with PolyORB_HI.Messages; use PolyORB_HI.Messages;
with PolyORB_HI.Port_Kinds;

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

   type Address_Array is array (Port_Type) of System.Address;
   --  An array to specify a list of arrays of various sizes.

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

   N_Destinations : in Integer_Array;
   --  For each OUT port, we give the number of destinations. This
   --  will be used to know the length of each element of the array
   --  below.

   Destinations : in Address_Array;
   --  For each OUT port, we give the address of an constant
   --  Entity_Type array containing the list of all the destination of
   --  the port. For IN ports, we give Null_Address.

   with procedure Marshall
     (R :        Thread_Interface_Type;
      M : in out PolyORB_Hi.Messages.Message_Type);
   --  A procedure that marshalls a Thread port content into a message.

   with function Send
     (From    : Entity_Type;
      Entity  : Entity_Type;
      Message : Message_Type) return Error_Kind;
   --  Send Message to the application node corresponding to the given
   --  entity.

   with function Next_Deadline return Ada.Real_Time.Time;
   --  To indicate when the next deadline of the thread occurs (in
   --  absolute time).

package PolyORB_HI.Thread_Interrogators
  with Abstract_State => ((Elaborated_Variables with Synchronous, External),
                          UQ_S),
       Initializes => (Elaborated_Variables, UQ_S)
is

   function Send_Output (Port : Port_Type) return Error_Kind
     with Global => (Input => Elaborated_Variables), Volatile_Function;
   --  Explicitly cause events, event data, or data to be transmitted
   --  through outgoing ports to receiver ports.

   procedure Put_Value (Thread_Interface : Thread_Interface_Type)
     with Global => (In_Out => (Elaborated_Variables, UQ_S));
   --  Supply a data value to a port variable. This data value will
   --  be transmitted at the next Send call in the source text or by
   --  the runtime system at completion time or deadline.

   procedure Receive_Input (Port : Port_Type);
   --  Explicitly request port input to be frozen. Newly arriving data
   --  is queued, but does not affect the input that thread has access
   --  during the current dispatch. The parameter of the function has
   --  the only utility to allow having one Receive_Input per thread.

   procedure Get_Value (Port : Port_Type; T_Port : out Thread_Interface_Type)
     with Global => (In_Out => (Elaborated_Variables), Input => UQ_S);
   --  Return the value corresponding to a given port. A second call to
   --  Get_Value returns always the same value unless Next_Value has
   --  been called. If no new values have come, return the latest
   --  received value.

   procedure Get_Sender (Port : Port_Type; Sender : out Entity_Type)
     with Global => (In_Out => (Elaborated_Variables), Input => UQ_S);
   --  Return the sender entity of value corresponding to the given port.
   --  A second call to Get_Sender returns always the same sender unless
   --  Next_Value has been called. If no new values have come, return
   --  the latest received value sender entity.

   procedure Get_Count (Port : Port_Type; Count : out Integer)
     with Global => (In_Out => (Elaborated_Variables), Input => UQ_S);
   --  Return the number of event [data] that have been queued in an
   --  IN port. A special value of -1 is returned if the Port never
   --  received a value since the beginning of the application.

   procedure Next_Value (Port : Port_Type)
     with Global => (In_Out => (Elaborated_Variables, UQ_S));
   --  Dequeue one value from the IN port queue.

   procedure Wait_For_Incoming_Events (Port : out Port_Type)
     with Global => (In_Out => (Elaborated_Variables),
                     Input => (UQ_S));
   --  Blocks until an event arrives. The port on which the event
   --  arrived is returned.

   procedure Get_Next_Event (Port : out Port_Type; Valid : out Boolean)
     with Global => (In_Out => (Elaborated_Variables),
                     Input => (UQ_S));
   --  Like 'Wait_For_Incoming_Events' but not blocking. Valid is set
   --  to False if no event has been received.

   procedure Store_Received_Message
     (Thread_Interface : Thread_Interface_Type;
      From             : PolyORB_HI_Generated.Deployment.Entity_Type;
      Time_Stamp       : Ada.Real_Time.Time    := Ada.Real_Time.Clock)
     with Global => (In_Out => (Elaborated_Variables, UQ_S));
   --  This subprogram is usually called by the transport layer to
   --  store new incoming messages. Time_Stamp indicates from which
   --  instant a data port with a delayed connection becomes
   --  deliverable. For other kinds of ports, this parameter value is
   --  set to the message reception time.

   function Get_Time_Stamp (P : Port_Type) return Ada.Real_Time.Time
     with Global => (Input => Elaborated_Variables), Volatile_Function;
   --  Return the timestamp of the latest value received on data port  P

end PolyORB_HI.Thread_Interrogators;
