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
package body Linted.Circ_Bufs is

   protected body Circ_Buf is
      procedure Try_Enqueue (Element : Element_T; Success : out Boolean) is
      begin
         if Last = First and Full then
            Success := False;
         else
            Elements (Last) := Element;
            Last := (Last + 1) mod (Max_Nodes + 1);
	    if Last = First then
	       Full := True;
	    end if;
            Success := True;
         end if;
      end Try_Enqueue;

      procedure Try_Dequeue (Element : out Element_T; Success : out Boolean) is
      begin
         if First = Last and not Full then
            declare
               Dummy : Element_T;
            begin
               Element := Dummy;
            end;
            Success := False;
         else
            Element := Elements (First);
            First := (First + 1) mod (Max_Nodes + 1);
	    Full := False;
            Success := True;
         end if;
      end Try_Dequeue;
   end Circ_Buf;

   procedure Try_Enqueue
     (Buf : in out Circ_Buf;
      Element : Element_T;
      Success : out Boolean)
   is
   begin
      Buf.Try_Enqueue (Element, Success);
   end Try_Enqueue;

   procedure Try_Dequeue
     (Buf : in out Circ_Buf;
      Element : out Element_T;
      Success : out Boolean)
   is
   begin
      Buf.Try_Dequeue (Element, Success);
   end Try_Dequeue;

end Linted.Circ_Bufs;
