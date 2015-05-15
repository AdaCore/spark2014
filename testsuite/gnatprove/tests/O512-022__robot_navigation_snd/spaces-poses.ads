--  Smooth ND driver for Player/Stage
--
--  SND Authors:  Joey Durham (algorithm),
--                Luca Invernizzi (driver implementation),
--                Piotr Trojanek (code Cleanup, Ada translation)
--
--  Implemented on top of Player - One Hell of a Robot Server
--  Copyright (C) 2003  (Brian Gerkey, Andrew Howard)
--
--
--  This program is free software; you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation; either version 2 of the License, or
--  (at your option) any later version.
--
--  This program is distributed in the hope that it will be useful,
--  but WITHOUT ANY WARRANTY; without even the implied warranty of
--  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
--  GNU General Public License for more details.
--
--  You should have received a copy of the GNU General Public License
--  along with this program; if not, write to the Free Software
--  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA.

--  \author Antonio Franchi
--  \brief Represents (x,y,ori) in SE(2)
--  \todo Implementare le composizioni di pose.
--  \todo   Implementare le inversioni di pose.

with Spaces.Angles;
with Spaces.Positions;

package Spaces.Poses is

   pragma Pure;

   use Spaces.Angles;
   use Spaces.Positions;

   type Pose is private;

   --  \brief  double constructor.
   function Create (X, Y : Float; Theta : Angle) return Pose;

   --  \brief  Position,Angle constructor.
   function Create (pos : Position; ori : Angle) return Pose;

   --  \brief  binary arithmetic operator +.
   function "+" (This, Other : Pose) return Pose;

   --  \brief  binary arithmetic operator -.
   function "-" (This, Other : Pose) return Pose;

   --  \brief binary arithmetic operator product by a Position (rototranslation).
   --  \note the Position scalar must be on the right side of the product
   function "*" (This : Pose; P : Position) return Position;

   --  \brief  Compound operator ==.
   function "=" (This, Other : Pose) return Boolean;

   --  \brief Position.
   function pos (This : Pose) return Position;

   --  \brief Orientation.
   function ori (This : Pose) return Angle;

   --  \brief Set x.
   procedure setX (This : in out Pose; X : Float);

   --  \brief Set x.
   procedure setY (This : in out Pose; Y : Float);

   --  \brief Set orientation.
   procedure setOri (This : in out Pose; ori : Angle);

   --  \brief Print.
   --  TODO: add precision parameter
   --  TODO: rewrite to 'Image attribute
   function print (This : Pose) return String;

private

   type Pose is record
      pos : Position;
      ori : Angle;
   end record;

end Spaces.Poses;
