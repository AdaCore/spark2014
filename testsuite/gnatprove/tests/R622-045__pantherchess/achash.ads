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


with Ada.Numerics.Discrete_Random;


package ACHash is

   type Hash_Type is mod 2 ** 64 with Size => 64;

   package Hash_Random is new Ada.Numerics.Discrete_Random(Hash_Type);
   use Hash_Random;

   Seed : Hash_Random.Generator;

   procedure Reset (Seed : Generator) renames Hash_Random.Reset;
   function Random (Seed : Generator) return Hash_Type renames Hash_Random.Random;

end ACHash;
