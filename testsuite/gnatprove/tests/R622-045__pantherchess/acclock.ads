--  PantherChess - based on AdaChess Copyright (C) 2017-2018 Bill Zuercher
--
--  AdaChess - Cool Chess Engine
--
--  Copyright (C) 2013-2017 - Alessandro Iavicoli
--  Email: adachess@gmail.com - Web Page: http://www.adachess.com
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.
--
--  This program is distributed in the hope that it will be useful,
--  but WITHOUT ANY WARRANTY; without even the implied warranty of
--  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
--  GNU General Public License for more details.
--
--  You should have received a copy of the GNU General Public License
--  along with this program.  If not, see <http://www.gnu.org/licenses/>.



with Ada.Calendar;
with Ada.Dispatching;


package ACClock is

   procedure Yield renames Ada.Dispatching.Yield;


   Tick : constant Duration := 0.25; -- a small gap for grant extra time

   task type Chess_Clock_Task_Type is
      entry Start;
   end Chess_Clock_Task_Type;

   type Chess_Clock_Task_Access is access Chess_Clock_Task_Type;


   procedure Start_Clock with Inline => True;
   procedure Force_Stop_Clock;

   function Time_Has_Up return Boolean with Inline => True;


   -------------------
   -- Timer entries --
   -------------------

   procedure Update_Residual_Time_Per_Game (Amount : Duration);
   procedure Set_Fixed_Time_Per_Move (Milliseconds : Duration);
   function Get_Thinked_Time return Duration;
   function Get_Allocated_Time_Per_Move return Duration;

   procedure Allocate_Extra_Time (Amount : Duration);
   procedure Reset_Extra_Time;
   function Get_Extra_Time return Duration;

   --------------------------
   -- Time_Management_Type --
   --------------------------

   type Time_Management_Type is
     (Fixed_Time_Per_Move, Blitz, Tournament, Fixed_Search_Depth);

   -- Raised when thinking time has expired
   Thinking_Time_Exceeded : exception;


   ---------------------------
   -- Opponent time tracker --
   ---------------------------

   Opponent_Time          : Duration;


private

   -- This is the clock to keep track of the
   -- amount of time available for thinking/pondering
   -- and other stuffs that needs a clock/timer
   Clock : Chess_Clock_Task_Access := null;

   ---------------
   -- Time data --
   ---------------

   Start_Time : Ada.Calendar.Time;
   Stop_Time : Ada.Calendar.Time;

   Thinked_Time : Duration;
   Residual_Time : Duration;
   Extra_Time_Amount : Duration;

   Residual_Time_Per_Game : Duration := 0.0;

   Time_Expired : Boolean;


   -- Fixed amount of thinking time per move
   Time_Per_Move : Duration := 5.0;

   --------------------------
   -- Time_Management_Type --
   --------------------------

   Time_Management : Time_Management_Type := Fixed_Time_Per_Move;


end ACClock;
