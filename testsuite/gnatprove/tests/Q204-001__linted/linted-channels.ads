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
generic
   type Element_T is private;
package Linted.Channels is
   pragma Pure;

   protected type Channel is
      --  Overwrites old values
      procedure Push (Element : Element_T) with
         Global => null,
         Depends => (Channel => (Element, Channel));
      entry Pop_Impl (Element : out Element_T) with
         Global => null,
         Depends => (Element => Channel, Channel => Channel);
      procedure Poll (Element : out Element_T; Success : out Boolean) with
         Global => null,
         Depends =>
         (Element => Channel,
          Channel => Channel,
          Success => Channel);

   private
      Current : Element_T;
      Full : Boolean := False;
   end Channel;

   procedure Push (This : in out Channel; Element : Element_T) with
      Global => null,
      Depends => (This => (Element, This));
   procedure Pop (This : in out Channel; Element : out Element_T) with
      Global => null,
      Depends => (Element => This, This => This);
   procedure Poll
     (This : in out Channel;
      Element : out Element_T;
      Success : out Boolean) with
      Global => null,
      Depends => ((Element, Success) => This, This => This);

private
end Linted.Channels;
