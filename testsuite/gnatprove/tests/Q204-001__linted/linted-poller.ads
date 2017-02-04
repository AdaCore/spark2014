-- Copyright 2016,2017 Steven Stewart-Gallus
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
with Linted.IO_Pool;
with Linted.KOs;
with Linted.Triggers;

package Linted.Poller is
   subtype Event is Linted.IO_Pool.Poller_Event;
   subtype Event_Type is Linted.IO_Pool.Poller_Event_Type;
   subtype Event_Set is Linted.IO_Pool.Poller_Event_Set;

   Readable : Event_Type renames Linted.IO_Pool.Readable;
   Writable : Event_Type renames Linted.IO_Pool.Writable;

   subtype Future is Linted.IO_Pool.Poll_Future;

   function Future_Is_Live
     (F : Future) return Boolean renames
     IO_Pool.Poll_Future_Is_Live;

   procedure Poll
     (Object : Linted.KOs.KO;
      Events : Event_Set;
      Signaller : Triggers.Signaller;
      F : out Future) renames
     IO_Pool.Poll;

   procedure Poll_Wait
     (F : in out Future;
      E : out Event) renames
     IO_Pool.Poll_Wait;

   procedure Poll_Poll
     (F : in out Future;
      E : out Event;
      Init : out Boolean) renames
     IO_Pool.Poll_Poll;
end Linted.Poller;
