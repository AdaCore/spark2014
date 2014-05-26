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

--  Position class borrowed from Multi-robot Integrated Platform
--  \author Antonio Franchi
--  \brief Represents (x,y) in R^2.

with Spaces.Angles;

package Spaces.Positions is

   pragma Pure;

   use Spaces.Angles;

   type Position is private;

   Zero_Position : constant Position;

   --  \brief default constructor */
   function Create return Position;

   --  \brief x y constructor */
   function Create (x_in, y_in : Float) return Position;

   --  \brief theta constructor (gives sin() and cos() of theta)*/
   function Create (theta : Angle) return Position;

   --  \brief d theta constructor */
   function Create (d : Float; theta : Angle) return Position
   with
     Post => (if d /= 0.0 then Create'Result /= Zero_Position);

   --  \brief  Sets x coordinate.
   procedure setX (This : in out Position; x : Float);

   --  \brief  Sets y coordinate.
   procedure setY (This : in out Position; y : Float);

   --  \brief  binary arithmetic operator + */
   function "+"(This : Position; other : Float) return Position
   with
     Pre => This /= Zero_Position;

   --  \brief  binary arithmetic operator - */
   function "-"(This : Position; other : Float) return Position
   with
     Pre => This /= Zero_Position;

   --  \brief  binary arithmetic operator + */
   function "+"(This : Position; other : Angle) return Position
   with
     Pre => This /= Zero_Position;

   --  \brief  binary arithmetic operator - */
   function "-"(This : Position; other : Angle) return Position
   with
     Pre => This /= Zero_Position;

   --  \brief  binary arithmetic operator + */
   function "+"(This : Position; other : Position) return Position;

   --  \brief  binary arithmetic operator - */
   function "-"(This : Position; other : Position) return Position;

   --  \brief  \brief binary arithmetic operator product by a scalar
   --  \note the scalar must be on the right side of the product
   function "*"(This : Position; scalar : Float) return Position;

   --  \brief  \brief binary arithmetic operator division by a scalar
   --  \note the scalar must be on the right side of the product
   function "/"(This : Position; scalar : Float) return Position
   with
     Pre => scalar /= 0.0;

   --  \brief  compound operator == */
   function "=" (This, Other : Position) return Boolean;

   --  \brief minimum with another position
   function minimum (This, P : Position) return Position;

   --  \brief maximum with another position
   function maximum (This, P : Position) return Position;

   --  \brief  x coordinate
   function X (This : Position) return Float;

   --  \brief  y coordinate
   function Y (This : Position) return Float;

   --  \brief Norm of the vector.
   --  \return the norm of the position vector
   function norm (This : Position) return Float
   with
     Post => norm'Result >= 0.0 and then
     (if norm'Result > 0.0 then This /= Zero_Position);

   --  \brief Gets the square of the norm of the vector.
   --  \return The square norm of the position vector
   function squareNorm (This : Position) return Float;

   --  \brief Distance between two vectors.
   --  \param p Position in respect to which compute the distance
   --  \return the norm of the difference between "this" and another passed Position
   function dist (This, Other : Position) return Float;

   --  \brief Anomaly in polar coordinates
   --  \return the bearing (phase or anomaly) of the position vector
   function bearing (This : Position) return Angle
   with
     Pre => This /= Zero_Position;

   --  \brief Scalar product.
   --  \return The scalar product between *this and the input Position
   --  \param[in]&p The other position.
   function scalar (This, P : Position) return Float;

   --  \brief  print
   --  TODO: add precision parameter
   --  TODO: rewrite to 'Image attribute
   function print (This : Position) return String;

private

   type Position is record
      x, y : Float;
   end record;

   Zero_Position : constant Position := (x => 0.0, y => 0.0);

end Spaces.Positions;
