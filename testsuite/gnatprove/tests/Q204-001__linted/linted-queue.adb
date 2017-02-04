-- Copyright 2017 Steven Stewart-Gallus
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
with Linted.Circ_Bufs;
with Linted.Wait_Lists;

package body Linted.Queue with
     Refined_State => (State => (Buf, Buf_Has_Free_Space, Buf_Has_Contents)) is
   package Bufs is new Circ_Bufs (Element_T, Max_Nodes);

   Buf : Bufs.Circ_Buf;
   Buf_Has_Free_Space : Wait_Lists.Wait_List;
   Buf_Has_Contents : Wait_Lists.Wait_List;

   procedure Enqueue (Element : Element_T) is
      Init : Boolean;
   begin
      loop
         Bufs.Try_Enqueue (Buf, Element, Init);
         exit when Init;
         Wait_Lists.Wait (Buf_Has_Free_Space);
      end loop;
      Wait_Lists.Signal (Buf_Has_Contents);
   end Enqueue;

   procedure Dequeue (Element : out Element_T) is
      Init : Boolean;
   begin
      loop
         Bufs.Try_Dequeue (Buf, Element, Init);
         exit when Init;
         Wait_Lists.Wait (Buf_Has_Contents);
      end loop;
      Wait_Lists.Signal (Buf_Has_Free_Space);
   end Dequeue;

end Linted.Queue;
