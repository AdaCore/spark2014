------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    G N A T 2 W H Y - A S S U M P T I O N S               --
--                                                                          --
--                                 B o d y                                  --
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

with Ada.Containers.Hashed_Maps;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Atree;                 use Atree;
with Gnat2Why.Nodes;        use Gnat2Why.Nodes;
with Sinput;                use Sinput;
with Snames;                use Snames;
with SPARK_Util;            use SPARK_Util;

package body Gnat2Why.Assumptions is

   package Claim_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Claim,
      Element_Type    => Claim_Sets.Set,
      Hash            => Hash_Claim,
      Equivalent_Keys => "=",
      "="             => Claim_Sets."=");

   function Claim_To_Token (C : Claim) return Token;
   --  Build an assumption token from a gnat2why claim

   function Loc_To_Assume_Sloc (Loc : Source_Ptr) return My_Sloc;

   Claim_Assumptions : Claim_Maps.Map := Claim_Maps.Empty_Map;
   --  contains the assumptions of a claim, whether that claim has been
   --  established or not

   Claims  : Claim_Sets.Set := Claim_Sets.Empty_Set;
   --  contains all established claims

   ----------------------
   -- Assume_For_Claim --
   ----------------------

   procedure Assume_For_Claim
     (C      : Claim;
      Assume : Claim) is
      use Claim_Maps;

      procedure Process (C : Claim; S : in out Claim_Sets.Set);

      -------------
      -- Process --
      -------------

      procedure Process (C : Claim; S : in out Claim_Sets.Set) is
         pragma Unreferenced (C);
      begin
         S.Include (Assume);
      end Process;

      Cu : constant Cursor := Claim_Assumptions.Find (C);
   begin
      if Cu = No_Element then
         Claim_Assumptions.Include (C, Claim_Sets.To_Set (Assume));
      else
         Claim_Assumptions.Update_Element (Cu, Process'Access);
      end if;
   end Assume_For_Claim;

   procedure Assume_For_Claim
     (C      : Claim;
      Assume : Claim_Sets.Set) is
   begin
      for A of Assume loop
         Assume_For_Claim (C, A);
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

   function Entity_To_Subp (E : Entity_Id) return Subp_Type
   is
      Loc  : constant Source_Ptr :=
        Translate_Location (Sloc (E));
   begin
      return Mk_Subp (Name => Subprogram_Full_Source_Name (E),
                      Sloc => Loc_To_Assume_Sloc (Loc));
   end Entity_To_Subp;

   ---------------------
   -- Get_Assume_JSON --
   ---------------------

   function Get_Assume_JSON return GNATCOLL.JSON.JSON_Value is
      Rules    : Rule_Lists.List := Rule_Lists.Empty_List;
   begin
      for C of Claims loop
         declare
            S : Token_Sets.Set := Token_Sets.Empty_Set;
            Cu : constant Claim_Maps.Cursor := Claim_Assumptions.Find (C);
            use Claim_Maps;
         begin
            if Cu /= Claim_Maps.No_Element then
               for A of Element (Cu) loop
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
      while Slc /= No_Location loop
         declare
            File : constant String := File_Name (Slc);
            Line : constant Integer :=
              Integer (Get_Physical_Line_Number (Slc));
         begin
            Sloc.Append (Mk_Base_Sloc (File => File, Line => Line));
         end;
         Slc := Instantiation_Location (Slc);
      end loop;
      return Sloc;
   end Loc_To_Assume_Sloc;

   --------------------
   -- Register_Claim --
   --------------------

   procedure Register_Claim (C : Claim) is
   begin
      Claims.Include (C);
   end Register_Claim;

   -----------------------------------------
   -- Register_Proof_Assumptions_For_Call --
   -----------------------------------------

   procedure Register_Assumptions_For_Call (Caller, Callee : Entity_Id)
   is
      S : Claim_Sets.Set := Claim_Sets.Empty_Set;
   begin
      S.Include ((Kind => Claim_Effects, E => Callee));
      Assume_For_Claim (C => (Kind => Claim_Effects, E => Caller),
                        Assume => S);
      if Has_Contracts (Callee, Name_Postcondition) then
         S.Include ((Kind => Claim_Post, E => Callee));
      end if;
      S.Include ((Kind => Claim_AoRTE, E => Callee));
      Assume_For_Claim (C => (Kind => Claim_Post, E => Caller), Assume => S);
      Assume_For_Claim (C => (Kind => Claim_AoRTE, E => Caller), Assume => S);
   end Register_Assumptions_For_Call;

   ---------------------------
   -- Register_Proof_Claims --
   ---------------------------

   procedure Register_Proof_Claims (E : Entity_Id) is
   begin
      Register_Claim ((E => E, Kind => Claim_AoRTE));
      if Has_Contracts (E, Name_Postcondition) then
         Register_Claim ((E => E, Kind => Claim_Post));
      end if;
   end Register_Proof_Claims;

end Gnat2Why.Assumptions;
