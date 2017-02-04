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
with Interfaces.C;
with System;

with Linted.Errors;
with Linted.KOs;
with Linted.Triggers;

package Linted.IO_Pool with
     Spark_Mode,
     Initializes => Future_Pool,
     Abstract_State =>
     ((Command_Queue with External),
      (Event_Queue with External),
      (Various with External),
      (Future_Pool with External))
is
   pragma Elaborate_Body;
   use type Interfaces.C.int;

   type Writer_Event is record
      Bytes_Written : Interfaces.C.size_t := 0;
      Err : Errors.Error;
   end record;

   type Reader_Event is record
      Bytes_Read : Interfaces.C.size_t := 0;
      Err : Errors.Error;
   end record;

   type Poller_Event_Type is (Readable, Writable);
   type Poller_Event_Set is array (Poller_Event_Type) of Boolean with
        Pack;
   type Poller_Event is record
      Events : Poller_Event_Set :=
        (Poller_Event_Type'First .. Poller_Event_Type'Last => False);
      Err : Errors.Error;
   end record;

   type Read_Future is limited private;

   function Read_Future_Is_Live (Future : Read_Future) return Boolean with
      Ghost,
      Global => null,
      Depends => (Read_Future_Is_Live'Result => Future);

   procedure Read
     (Object : KOs.KO;
      Buf : System.Address;
      Count : Interfaces.C.size_t;
      Signaller : Triggers.Signaller;
      Future : out Read_Future) with
      Global => (In_Out => (Command_Queue, Future_Pool)),
      Depends =>
      (Future => Future_Pool,
       Command_Queue =>
         (Buf, Count, Object, Signaller, Future_Pool, Command_Queue),
       Future_Pool => Future_Pool),
      Post => Read_Future_Is_Live (Future);

   procedure Read_Wait
     (Future : in out Read_Future;
      Event : out Reader_Event) with
      Global => (In_Out => (Event_Queue, Future_Pool)),
      Depends =>
      (Future => null,
       Event => (Event_Queue, Future),
       Event_Queue => (Future, Event_Queue),
       Future_Pool => (Future, Future_Pool)),
      Pre => Read_Future_Is_Live (Future),
      Post => not Read_Future_Is_Live (Future);

   procedure Read_Poll
     (Future : in out Read_Future;
      Event : out Reader_Event;
      Init : out Boolean) with
      Global => (In_Out => (Event_Queue, Future_Pool)),
      Depends =>
      (Future => (Event_Queue, Future),
       Event => (Event_Queue, Future),
       Init => (Event_Queue, Future),
       Event_Queue => (Future, Event_Queue),
       Future_Pool => (Future, Event_Queue, Future_Pool)),
      Pre => Read_Future_Is_Live (Future),
      Post =>
      (if Init then not Read_Future_Is_Live (Future)
       else Read_Future_Is_Live (Future));

   type Write_Future is limited private;

   function Write_Future_Is_Live (Future : Write_Future) return Boolean with
      Ghost,
      Global => null,
      Depends => (Write_Future_Is_Live'Result => Future);

   procedure Write
     (Object : KOs.KO;
      Buf : System.Address;
      Count : Interfaces.C.size_t;
      Signaller : Triggers.Signaller;
      Future : out Write_Future) with
      Global => (In_Out => (Command_Queue, Future_Pool)),
      Depends =>
      (Future => (Future_Pool),
       Command_Queue =>
         (Buf, Count, Future_Pool, Object, Signaller, Command_Queue),
       Future_Pool => Future_Pool),
      Post => Write_Future_Is_Live (Future);

   procedure Write_Wait
     (Future : in out Write_Future;
      Event : out Writer_Event) with
      Global => (In_Out => (Event_Queue, Future_Pool)),
      Depends =>
      (Future => null,
       Event => (Event_Queue, Future),
       Event_Queue => (Future, Event_Queue),
       Future_Pool => (Future, Future_Pool)),
      Pre => Write_Future_Is_Live (Future),
      Post => not Write_Future_Is_Live (Future);

   procedure Write_Poll
     (Future : in out Write_Future;
      Event : out Writer_Event;
      Init : out Boolean) with
      Global => (In_Out => (Event_Queue, Future_Pool)),
      Depends =>
      (Future => (Event_Queue, Future),
       Event => (Event_Queue, Future),
       Init => (Event_Queue, Future),
       Event_Queue => (Future, Event_Queue),
       Future_Pool => (Future, Event_Queue, Future_Pool)),
      Pre => Write_Future_Is_Live (Future),
      Post =>
      (if Init then not Write_Future_Is_Live (Future)
       else Write_Future_Is_Live (Future));

   type Poll_Future is limited private;

   function Poll_Future_Is_Live (Future : Poll_Future) return Boolean with
      Ghost,
      Global => null,
      Depends => (Poll_Future_Is_Live'Result => Future);

   procedure Poll
     (Object : KOs.KO;
      Events : Poller_Event_Set;
      Signaller : Triggers.Signaller;
      Future : out Poll_Future) with
      Global => (In_Out => (Command_Queue, Future_Pool)),
      Depends =>
      (Future => (Future_Pool),
       Command_Queue =>
         (Events, Future_Pool, Object, Signaller, Command_Queue),
       Future_Pool => (Future_Pool)),
      Post => Poll_Future_Is_Live (Future);

   procedure Poll_Wait
     (Future : in out Poll_Future;
      Event : out Poller_Event) with
      Global => (In_Out => (Event_Queue, Future_Pool)),
      Depends =>
      (Future => null,
       Event => (Event_Queue, Future),
       Event_Queue => (Future, Event_Queue),
       Future_Pool => (Future, Future_Pool)),
      Pre => Poll_Future_Is_Live (Future),
      Post => not Poll_Future_Is_Live (Future);

   procedure Poll_Poll
     (Future : in out Poll_Future;
      Event : out Poller_Event;
      Init : out Boolean) with
      Global => (In_Out => (Event_Queue, Future_Pool)),
      Depends =>
      (Future => (Event_Queue, Future),
       Event => (Event_Queue, Future),
       Init => (Event_Queue, Future),
       Event_Queue => (Future, Event_Queue),
       Future_Pool => (Future, Event_Queue, Future_Pool)),
      Pre => Poll_Future_Is_Live (Future),
      Post =>
      (if Init then not Poll_Future_Is_Live (Future)
       else Poll_Future_Is_Live (Future));
private
   type Read_Future is new Natural with
        Default_Value => 0;
   type Write_Future is new Natural with
        Default_Value => 0;
   type Poll_Future is new Natural with
        Default_Value => 0;
end Linted.IO_Pool;
