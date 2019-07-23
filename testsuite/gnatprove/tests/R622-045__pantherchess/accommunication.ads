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


-- This packages holds data to work
-- with external GUI or console

package ACCommunication is

   -- Chess can be printed to screen/console using many different
   -- notations. Here we set the notations that we can manage.
   -- Please consider that some notations type are are communication
   -- protocol instead of "notations", like Winboard or UCI.
   type Notation_Type is
     (Algebraic, -- e4 Nf6 O-O Qxc3+ ...
      Long_Algebraic, -- e2-e4 Ng8-f6 O-O Qa5xc3+ ...
      Winboard) -- e2e4 g8f6 e1c1 a5c3
   with Size => 2;

   -- Supported communication protocols
   type Communication_Protocol_Type is
     (No_Gui_Connection, Winboard, UCI) with Size => 2;


   -- Change current output notation
   procedure Set_Output_Notation
     (Notation : in Notation_Type);

   -- Return the current notation in use
   function Notation return Notation_Type;

   -- Set the Gui Communication protocol
   -- to use to exchange data from and to
   -- external gui (or console)
   procedure Set_GUI_Communication_Protocol
     (Protocol : Communication_Protocol_Type);

   -- Retrieve current communication protocol
   function Protocol return Communication_Protocol_Type;


private

   -----------------------------
   -- Communication Protocols --
   -----------------------------

   -- Output mode for GUI connection.
   Engine_Output_Notation     : Notation_Type := Algebraic;

   -- Holds the communication protocol in use
   Communication_Protocol     : Communication_Protocol_Type := No_Gui_Connection;

end ACCommunication;
