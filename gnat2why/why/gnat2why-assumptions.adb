------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    G N A T 2 W H Y - A S S U M P T I O N S               --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2017, AdaCore                   --
--                       Copyright (C) 2014-2017, Altran UK Limited         --
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

with Ada.Containers.Hashed_Maps;
with Atree;                      use Atree;
with Einfo;                      use Einfo;
with Sinput;                     use Sinput;
with Snames;                     use Snames;
with SPARK_Util;                 use SPARK_Util;
with SPARK_Util.Subprograms;     use SPARK_Util.Subprograms;

package body Gnat2Why.Assumptions is

   package Claim_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Claim,
      Element_Type    => Claim_Sets.Set,
      Hash            => Hash_Claim,
      Equivalent_Keys => "=",
      "="             => Claim_Sets."=");

   function Claim_To_Token (C : Claim) return Token;
   --  Build an assumption token from a gnat2why claim

   function Loc_To_Assume_Sloc (Loc : Source_Ptr) return My_Sloc
   with Pre => Loc /= No_Location;

   Claim_Assumptions : Claim_Maps.Map := Claim_Maps.Empty_Map;
   --  Assumptions of a claim, whether that claim has been established or not

   Claims : Claim_Sets.Set := Claim_Sets.Empty_Set;
   --  All established claims

   ----------------------
   -- Assume_For_Claim --
   ----------------------

   procedure Assume_For_Claim
     (C      : Claim;
      Assume : Claim)
   is
      Position : Claim_Maps.Cursor;
      Dummy    : Boolean;

   begin
      --  Attempt to insert an empty set and then put the assumption there
      Claim_Assumptions.Insert (Key      => C,
                                Position => Position,
                                Inserted => Dummy);

      Claim_Assumptions (Position).Include (Assume);
   end Assume_For_Claim;

   procedure Assume_For_Claim
     (C      : Claim;
      Assume : Claim_Lists.List)
   is
      Position : Claim_Maps.Cursor;
      Dummy    : Boolean;

   begin
      --  Attempt to insert an empty set and then put the assumption there
      Claim_Assumptions.Insert (Key      => C,
                                Position => Position,
                                Inserted => Dummy);

      for A of Assume loop
         Claim_Assumptions (Position).Include (A);
      end loop;
   end Assume_For_Claim;

   --------------------
   -- Claim_To_Token --
   --------------------

   function Claim_To_Token (C : Claim) return Token is
   begin
      return (Predicate => C.Kind,
              Arg       => Entity_To_Subp (C.E));
   end Claim_To_Token;

   --------------------
   -- Entity_To_Subp --
   --------------------

   function Entity_To_Subp (E : Entity_Id) return Subp_Type is
   begin
      return Mk_Subp (Name => Subprogram_Full_Source_Name (E),
                      Sloc => Loc_To_Assume_Sloc (Sloc (E)));
   end Entity_To_Subp;

   ---------------------
   -- Get_Assume_JSON --
   ---------------------

   function Get_Assume_JSON return GNATCOLL.JSON.JSON_Value is
      Rules : Rule_Lists.List := Rule_Lists.Empty_List;
   begin
      for C of Claims loop
         declare
            S : Token_Sets.Set := Token_Sets.Empty_Set;
            Cu : constant Claim_Maps.Cursor := Claim_Assumptions.Find (C);
            use Claim_Maps;
         begin
            if Claim_Maps.Has_Element (Cu) then
               for A of Claim_Assumptions (Cu) loop
                  S.Include (Claim_To_Token (A));
               end loop;
            end if;
            Rules.Append ((Claim       => Claim_To_Token (C),
                           Assumptions => S));
         end;
      end loop;

      return To_JSON (Rules);
   end Get_Assume_JSON;

   ------------------------
   -- Loc_To_Assume_Sloc --
   ------------------------

   function Loc_To_Assume_Sloc (Loc : Source_Ptr) return My_Sloc is
      Sloc : My_Sloc := Sloc_Lists.Empty_List;
      Slc  : Source_Ptr := Loc;
   begin
      loop
         declare
            File : constant String := File_Name (Slc);
            Line : constant Positive :=
              Positive (Get_Physical_Line_Number (Slc));
         begin
            Sloc.Append (Mk_Base_Sloc (File => File, Line => Line));
         end;
         Slc := Instantiation_Location (Slc);

         exit when Slc = No_Location;
      end loop;
      return Sloc;
   end Loc_To_Assume_Sloc;

   --------------------
   -- Register_Claim --
   --------------------

   procedure Register_Claim (C : Claim) renames Claims.Include;

   -----------------------------------
   -- Register_Assumptions_For_Call --
   -----------------------------------

   procedure Register_Assumptions_For_Call (Caller, Callee : Entity_Id)
   is
      Assumptions : Claim_Lists.List;
   begin
      Assumptions.Append ((Kind => Claim_Effects, E => Callee));

      Assume_For_Claim (C      => (Kind => Claim_Effects, E => Caller),
                        Assume => Assumptions);

      if Has_Contracts (Callee, Pragma_Postcondition) then
         Assumptions.Append ((Kind => Claim_Post, E => Callee));
      end if;

      Assumptions.Append ((Kind => Claim_AoRTE, E => Callee));

      Assume_For_Claim (C      => (Kind => Claim_Post, E => Caller),
                        Assume => Assumptions);
      Assume_For_Claim (C      => (Kind => Claim_AoRTE, E => Caller),
                        Assume => Assumptions);
   end Register_Assumptions_For_Call;

   ---------------------------
   -- Register_Proof_Claims --
   ---------------------------

   procedure Register_Proof_Claims (E : Entity_Id) is
   begin
      Register_Claim ((E => E, Kind => Claim_AoRTE));

      --  ??? Add proper handling of Initial_Condition
      --  (for E whose Ekind = E_Package), currently ignored.

      if Ekind (E) in E_Function
                    | E_Procedure
                    | Entry_Kind
        and then Has_Contracts (E, Pragma_Postcondition)
      then
         Register_Claim ((E => E, Kind => Claim_Post));
      end if;
   end Register_Proof_Claims;

end Gnat2Why.Assumptions;
