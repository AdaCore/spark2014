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
with Linted.Options;

generic
   type Element_T is private;
package Linted.MVars with
   Abstract_State => null is
   pragma Pure;

   protected type MVar is
      procedure Poll (D : out Element_T; Init : out Boolean);
      procedure Set (D : Element_T) with
         Global => null,
         Depends => (MVar => (D, MVar));

   private
      Current : Element_T;
      Full : Boolean;
   end MVar;

   package Option_Element_Ts is new Linted.Options (Element_T);

   procedure Poll
     (This : in out MVar;
      Option : out Option_Element_Ts.Option) with
      Global => null,
      Depends => (Option => This, This => This);
   procedure Set (This : in out MVar; D : Element_T) with
      Global => null,
      Depends => (This => (D, This));
end Linted.MVars;
