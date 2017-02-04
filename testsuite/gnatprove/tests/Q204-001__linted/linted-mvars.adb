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
package body Linted.MVars is
   procedure Poll
     (This : in out MVar;
      Option : out Option_Element_Ts.Option)
   is
      D : Element_T;
      Init : Boolean;
   begin
      This.Poll (D, Init);
      if Init then
	 Option := (Empty => False, Data => D);
      else
	 Option := (Empty => True);
      end if;
   end Poll;

   procedure Set (This : in out MVar; D : Element_T) is
   begin
      This.Set (D);
   end Set;

   protected body MVar is
      procedure Poll (D : out Element_T; Init : out Boolean) is
      begin
	 if Full then
	    Full := False;
	    D := Current;
	    Init := True;
	 else
	    Init := False;
	 end if;
      end Poll;

      procedure Set (D : Element_T) is
      begin
         Current := D;
	 Full := True;
      end Set;
   end MVar;
end Linted.MVars;
