-- Copyright 2015,2016,2017 Steven Stewart-Gallus
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
-- implied.  See the License for the specific language governing
-- permissions and limitations under the License.
with Linted.Channels;
with Linted.Queue;

package body Linted.IO_Pool with
     Spark_Mode,
  Refined_State => (Command_Queue => (My_Command_Queue.State),
		    Event_Queue => (Read_Future_Channels,
				    Write_Future_Channels,
				    Poll_Future_Channels),
		    Various => Worker_Tasks,
		    Future_Pool => (Spare_Write_Futures.State,
				    Spare_Read_Futures.State,
				    Spare_Poll_Futures.State))
is
   Max_Read_Futures : constant := 32;
   Max_Write_Futures : constant := 32;
   Max_Poll_Futures : constant := 32;
   Max_Command_Queue_Capacity : constant := 32;

   package C renames Interfaces.C;

   use type C.size_t;
   use type Interfaces.C.unsigned;

   type Write_Command is record
      Object : KOs.KO;
      Buf : System.Address := System.Null_Address;
      Count : C.size_t := 0;
      Replier : Write_Future;
      Signaller : Triggers.Signaller;
   end record;

   type Read_Command is record
      Object : KOs.KO;
      Buf : System.Address := System.Null_Address;
      Count : C.size_t := 0;
      Replier : Read_Future;
      Signaller : Triggers.Signaller;
   end record;

   type Poller_Command is record
      Object : KOs.KO;
      Events : Poller_Event_Set :=
        (Poller_Event_Type'First .. Poller_Event_Type'Last => False);
      Replier : Poll_Future;
      Signaller : Triggers.Signaller;
   end record;

   type Command_Type is (Invalid_Type, Write_Type, Read_Type, Poll_Type);

   type Command (T : Command_Type := Invalid_Type) is record
      case T is
         when Invalid_Type =>
            null;
         when Write_Type =>
            Write_Object : Write_Command;
         when Read_Type =>
            Read_Object : Read_Command;
         when Poll_Type =>
            Poll_Object : Poller_Command;
      end case;
   end record;

   package Spare_Read_Futures is new Queue (Read_Future, Max_Read_Futures);
   package Spare_Write_Futures is new Queue (Write_Future, Max_Write_Futures);
   package Spare_Poll_Futures is new Queue (Poll_Future, Max_Poll_Futures);
   package My_Command_Queue is new Queue (Command, Max_Command_Queue_Capacity);

   task type Worker_Task with Global => (In_Out => (My_Command_Queue.State,
						    Read_Future_Channels,
						    Write_Future_Channels,
						    Poll_Future_Channels
						   )),
     Depends => (My_Command_Queue.State => (My_Command_Queue.State),
		 Read_Future_Channels => (Read_Future_Channels, My_Command_Queue.State),
		 Write_Future_Channels => (Write_Future_Channels, My_Command_Queue.State),
		 Poll_Future_Channels => (Poll_Future_Channels, My_Command_Queue.State)
		);

   Worker_Tasks : array (1 .. 16) of Worker_Task;

   package Writer_Event_Channels is new Channels (Writer_Event);
   package Reader_Event_Channels is new Channels (Reader_Event);
   package Poller_Event_Channels is new Channels (Poller_Event);

   type Read_Future_Channels_Array is
     array (Read_Future range <>) of Reader_Event_Channels.Channel;
   type Write_Future_Channels_Array is
     array (Write_Future range <>) of Writer_Event_Channels.Channel;
   type Poller_Future_Channels_Array is
     array (Poll_Future range <>) of Poller_Event_Channels.Channel;

   Read_Future_Channels : Read_Future_Channels_Array (1 .. Max_Read_Futures);
   Write_Future_Channels : Write_Future_Channels_Array (1 .. Max_Write_Futures);
   Poll_Future_Channels : Poller_Future_Channels_Array (1 .. Max_Poll_Futures);

   procedure Do_Write (W : Write_Command) with
      Global => (In_Out => Write_Future_Channels),
      Depends => (Write_Future_Channels => (W, Write_Future_Channels));
   procedure Do_Read (R : Read_Command) with
      Global => (In_Out => Read_Future_Channels),
      Depends => (Read_Future_Channels => (R, Read_Future_Channels));
   procedure Do_Poll (P : Poller_Command) with
      Global => (In_Out => Poll_Future_Channels),
      Depends => (Poll_Future_Channels => (P, Poll_Future_Channels));

   procedure Read
     (Object : KOs.KO;
      Buf : System.Address;
      Count : Interfaces.C.size_t;
      Signaller : Triggers.Signaller;
      Future : out Read_Future)
   is
   begin
      Spare_Read_Futures.Dequeue (Future);
      My_Command_Queue.Enqueue ((Read_Type,
				 (Object,
				  Buf,
				  Count,
				  Future,
				  Signaller)));
   end Read;

   procedure Read_Wait
     (Future : in out Read_Future;
      Event : out Reader_Event)
   is
   begin
      Reader_Event_Channels.Pop (Read_Future_Channels (Future), Event);
      Spare_Read_Futures.Enqueue (Future);
      Future := 0;
   end Read_Wait;

   procedure Read_Poll
     (Future : in out Read_Future;
      Event : out Reader_Event;
      Init : out Boolean)
   is
   begin
      Reader_Event_Channels.Poll (Read_Future_Channels (Future), Event, Init);
      if Init then
	 Spare_Read_Futures.Enqueue (Future);
         Future := 0;
      end if;
   end Read_Poll;

   procedure Write
     (Object : KOs.KO;
      Buf : System.Address;
      Count : Interfaces.C.size_t;
      Signaller : Triggers.Signaller;
      Future : out Write_Future)
   is
   begin
      Spare_Write_Futures.Dequeue (Future);
      My_Command_Queue.Enqueue ((Write_Type, (Object, Buf, Count, Future, Signaller)));
   end Write;

   procedure Write_Wait
     (Future : in out Write_Future;
      Event : out Writer_Event)
   is
   begin
      Writer_Event_Channels.Pop (Write_Future_Channels (Future), Event);
      Spare_Write_Futures.Enqueue (Future);
      Future := 0;
   end Write_Wait;

   procedure Write_Poll
     (Future : in out Write_Future;
      Event : out Writer_Event;
      Init : out Boolean)
   is
   begin
      Writer_Event_Channels.Poll (Write_Future_Channels (Future), Event, Init);
      if Init then
	 Spare_Write_Futures.Enqueue (Future);
         Future := 0;
      end if;
   end Write_Poll;

   procedure Poll
     (Object : KOs.KO;
      Events : Poller_Event_Set;
      Signaller : Triggers.Signaller;
      Future : out Poll_Future)
   is
   begin
      Spare_Poll_Futures.Dequeue (Future);
      My_Command_Queue.Enqueue ((Poll_Type, (Object, Events, Future, Signaller)));
   end Poll;

   procedure Poll_Wait
     (Future : in out Poll_Future;
      Event : out Poller_Event)
   is
   begin
      Poller_Event_Channels.Pop (Poll_Future_Channels (Future), Event);
      Spare_Poll_Futures.Enqueue (Future);
      Future := 0;
   end Poll_Wait;

   procedure Poll_Poll
     (Future : in out Poll_Future;
      Event : out Poller_Event;
      Init : out Boolean)
   is
   begin
      Poller_Event_Channels.Poll (Poll_Future_Channels (Future), Event, Init);
      if Init then
	 Spare_Poll_Futures.Enqueue (Future);
         Future := 0;
      end if;
   end Poll_Poll;

   procedure Do_Write (W : Write_Command) is
      Err : C.int;
      Bytes_Written : C.size_t := 0;

      Object : constant KOs.KO := W.Object;
      Buf : constant System.Address := W.Buf;
      Count : constant C.size_t := W.Count;
      Replier : constant Write_Future := W.Replier;
      Signaller : constant Triggers.Signaller := W.Signaller;
   begin
      null;
   end Do_Write;

   procedure Do_Read (R : Read_Command) with
      Spark_Mode => Off is
      Err : C.int;
      Bytes_Read : C.size_t := 0;

      Object : constant KOs.KO := R.Object;
      Buf : constant System.Address := R.Buf;
      Count : constant C.size_t := R.Count;
      Replier : constant Read_Future := R.Replier;
      Signaller : constant Triggers.Signaller := R.Signaller;

   begin
      null;
   end Do_Read;

   procedure Do_Poll (P : Poller_Command) with
      Spark_Mode => Off is
      Err : C.int;

      Object : constant KOs.KO := P.Object;
      Listen_Events : constant Poller_Event_Set := P.Events;
      Heard_Events : Poller_Event_Set :=
        (Poller_Event_Type'First .. Poller_Event_Type'Last => False);
      Replier : constant Poll_Future := P.Replier;
      Signaller : constant Triggers.Signaller := P.Signaller;

      Nfds : C.int;
   begin
      null;
   end Do_Poll;

   task body Worker_Task is
      New_Command : Command;
   begin
      loop
	 My_Command_Queue.Dequeue (New_Command);

         case New_Command.T is
            when Invalid_Type =>
               raise Program_Error;

            when Write_Type =>
               Do_Write (New_Command.Write_Object);
            when Read_Type =>
               Do_Read (New_Command.Read_Object);
            when Poll_Type =>
               Do_Poll (New_Command.Poll_Object);
         end case;
      end loop;
   end Worker_Task;

   function Read_Future_Is_Live
     (Future : Read_Future) return Boolean is
     (Future /= 0);
   function Write_Future_Is_Live
     (Future : Write_Future) return Boolean is
     (Future /= 0);
   function Poll_Future_Is_Live
     (Future : Poll_Future) return Boolean is
     (Future /= 0);

begin
   for II in 1 .. Max_Read_Futures loop
      Spare_Read_Futures.Enqueue (Read_Future (II));
   end loop;

   for II in 1 .. Max_Write_Futures loop
      Spare_Write_Futures.Enqueue (Write_Future (II));
   end loop;

   for II in 1 .. Max_Poll_Futures loop
      Spare_Poll_Futures.Enqueue (Poll_Future (II));
   end loop;
end Linted.IO_Pool;
