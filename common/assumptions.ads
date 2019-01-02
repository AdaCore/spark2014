------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                           A S S U M P T I O N S                          --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                     Copyright (C) 2010-2019, AdaCore                     --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Containers;                     use Ada.Containers;
with Ada.Containers.Doubly_Linked_Lists;
with Ada.Containers.Ordered_Sets;

with Assumption_Types;      use Assumption_Types;

with GNATCOLL.JSON;         use GNATCOLL.JSON;

package Assumptions is

   type Claim_Kind is
     (Claim_Init,
      Claim_Pre,
      Claim_Post,
      Claim_Effects,
      Claim_AoRTE);

   type Token is record
      Predicate : Claim_Kind;
      Arg       : Subp_Type;
   end record;

   function Hash_Token (X : Token) return Ada.Containers.Hash_Type;

   function Hash_Token (X : Token) return Ada.Containers.Hash_Type is
     (Ada.Containers.Hash_Type (Claim_Kind'Pos (X.Predicate)) +
          3 * Hash (X.Arg));

   function "<" (Left, Right : Token) return Boolean is
     (Left.Predicate < Right.Predicate or else
        (Left.Predicate = Right.Predicate and then
         Left.Arg < Right.Arg));

   package Token_Sets is new Ada.Containers.Ordered_Sets
     (Element_Type        => Token,
      "<"                 => "<",
      "="                 => "=");

   type Rule is record
      Claim       : Token;
      Assumptions : Token_Sets.Set;
   end record;

   package Rule_Lists is new Ada.Containers.Doubly_Linked_Lists
     (Element_Type => Rule,
      "="          => "=");

   function To_String (T : Token) return String;
   --  return a human-readable presentation of the assumption/claim

   function From_JSON (S : String) return Rule_Lists.List;
   function From_JSON (S : JSON_Array) return Rule_Lists.List;
   function To_JSON (L : Rule_Lists.List) return JSON_Value;

end Assumptions;
