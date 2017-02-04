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
package body Linted.Channels is
   procedure Push (This : in out Channel; Element : Element_T) is
   begin
      This.Push (Element);
   end Push;

   procedure Pop (This : in out Channel; Element : out Element_T) is
   begin
      This.Pop_Impl (Element);
   end Pop;

   procedure Poll
     (This : in out Channel;
      Element : out Element_T;
      Success : out Boolean)
   is
   begin
      This.Poll (Element, Success);
   end Poll;

   protected body Channel is
      procedure Push (Element : Element_T) is
      begin
         Current := Element;
         Full := True;
      end Push;

      entry Pop_Impl (Element : out Element_T) when Full is
      begin
         Element := Current;
         Full := False;
      end Pop_Impl;

      procedure Poll (Element : out Element_T; Success : out Boolean) is
      begin
         if Full then
            Full := False;
            Element := Current;
            Success := True;
         else
            declare
               Dummy : Element_T;
            begin
               Element := Dummy;
            end;
            Success := False;
         end if;
      end Poll;
   end Channel;
end Linted.Channels;
