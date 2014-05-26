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

--  Angle class borrowed from Multi-robot Integrated Platform
--  \author Antonio Franchi

with Ada.Numerics;

package Spaces.Angles is

   pragma Pure;

   Pi : constant := Ada.Numerics.Pi;

   type Angle is private;

   --  \brief Default constructor.
   function Create return Angle;

   --  \brief Float constructor
   function Create (t : Float) return Angle;

   --  \brief Binary arithmetic operator +.
   function "+" (This, Other : Angle) return Angle;

   --  \brief Binary arithmetic operator -.
   function "-" (This, Other : Angle) return Angle;

   --  \brief Binary arithmetic operator * with scalar.
   function "*" (This : Angle; d : Float) return Angle;

   --  \brief Explicit casting to double in (-M_PI, M_PI].
   function dCast (This : Angle) return Float;

   --  \brief Explicit casting to double in (-M_PI, M_PI].
   function dCastPi (This : Angle) return Float;

   --  \brief Explicit casting to double, in degrees [0, 360.0).
   function dCastDeg (This : Angle) return Float;

   --  \brief Algebric difference (in ]-PI,PI]).
   --  \details i.e, other - this in [0,2*PI[.
   --  \param[in] other The Angle respect to it is computed the algebric distance.
   --  \return The algebric distance respect to an angle, it is in [-PI,PI].
   function alDiff (This, Other : Angle) return Float
   with
     Post => alDiff'Result > -Pi and then alDiff'Result <= Pi;

   --  \brief Counter-clock-wise difference (in [0,2*PI[).
   --  \details i.e, other - this in in [0,2*PI[.
   --  \param[in] other The other angle.
   --  \return A double in [0,2*PI[.
   function ccwDiff (This, Other : Angle) return Float;

   --  \brief Clock-wise difference (in ]-2*PI,0]).
   --  \details i.e, other - this in in ]-2*PI,0].
   --  \param other The other angle.
   --  \return A double in ]-2*PI,0].
   function cwDiff (This, Other : Angle) return Float;

   --  \brief Equal condition with a tollerance.
   --  \param[in] A The Angle to be confronted with.
   --  \param[in] toll The acceppted tollerance (rad).
   --  \return \b true if difference betwen Angle is less than the tollerance, \b false otherwise.
   function almostEqual (This, Other : Angle; toll : Float) return Boolean;

   --  \brief Counter-clock-wise mean, i.e, mean angle in ]this, other].
   --  \details If this == other, it is by definition this + M_PI.
   --  \param[in] other The other angle.
   --  \return Mean angle in ]this, other].
   function ccwMean (This, Other : Angle) return Angle;

   --  \brief Clock-wise mean, i.e, mean angle in ]other, this].
   --  \details if this == other, it is by definition this.
   --  \param[in] other The other angle.
   --  \return Mean angle in ]other, this].
   function cwMean (This, Other : Angle) return Angle;

   --  \brief Print function.
   --  \param[in] precision The number of doubles (default is 2).
   --  \return A printable string with the value printed on it.
   --  TODO: add precision parameter
   --  TODO: rewrite to 'Image attribute
   function Print (This : Angle) return String;

private

   subtype normalized2Pi is Float range 0.0 .. 2.0 * Pi;

   type Angle is record
      Theta : normalized2Pi;
   end record;

   --  \brief Returns a value in [0, 2*M_PI).
   function norm2Pi (x : Float) return Float
   with
     Post => norm2Pi'Result >= 0.0 and then norm2Pi'Result < 2.0 * Pi;

   --  \brief Returns a value in (-M_PI, M_PI].
   function normPi (x : Float) return Float
   with
     Post => normPi'Result > -Pi and then normPi'Result <= Pi;

end Spaces.Angles;
