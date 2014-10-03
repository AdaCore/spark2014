------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    G N A T 2 W H Y - A S S U M P T I O N S               --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2014, AdaCore                   --
--                       Copyright (C) 2014, Altran UK Limited              --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------
with Ada.Containers;   use Ada.Containers;
with Ada.Containers.Hashed_Sets;
with Assumption_Types; use Assumption_Types;
with Assumptions;      use Assumptions;
with GNATCOLL.JSON;
with Types;            use Types;

package Gnat2Why.Assumptions is

   type Claim is record
      Kind : Claim_Kind;
      E    : Entity_Id;
   end record;

   function Hash_Claim (C : Claim) return Ada.Containers.Hash_Type;

   function Hash_Claim (C : Claim) return Ada.Containers.Hash_Type is
     (Hash_Type (Claim_Kind'Pos (C.Kind)) + 4 * Hash_Type (C.E));

   package Claim_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Claim,
      Hash                => Hash_Claim,
      Equivalent_Elements => "=",
      "="                 => "=");

   procedure Register_Claim (C : Claim);
   --  This registers that the claim [C] has been established.

   procedure Assume_For_Claim
     (C      : Claim;
      Assume : Claim);

   procedure Assume_For_Claim
     (C      : Claim;
      Assume : Claim_Sets.Set);
   --  Both procedures register that the claim C depends on the assumption(s)
   --  provided. Calling these procedures does not mean that claim C has been
   --  established.

   procedure Register_Assumptions_For_Call (Caller, Callee : Entity_Id);
   --  For the call (caller -> callee), register the assumptions

   procedure Register_Proof_Claims (E : Entity_Id);
   --  For the entity E, all VCs have been proved, emit the appropriate claims

   function Get_Assume_JSON return GNATCOLL.JSON.JSON_Value;
   --  Save assumptions output to file "unit.assum"

   function Entity_To_Subp (E : Entity_Id) return Subp_Type;
   --  transform an entity into the triple (name, file, line)

end Gnat2Why.Assumptions;
