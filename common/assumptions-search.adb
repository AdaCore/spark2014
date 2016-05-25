------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                     A S S U M P T I O N S . S E A R C H                  --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2016, AdaCore                   --
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

with Ada.Containers.Hashed_Maps;

package body Assumptions.Search is

   package Goal_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Token,
      Element_Type    => Token_Sets.Set,
      Hash            => Hash_Token,
      Equivalent_Keys => "=",
      "="             => Token_Sets."=");

   Map : Goal_Maps.Map := Goal_Maps.Empty_Map;

   ------------
   -- Import --
   ------------

   procedure Import (L : Rule_Lists.List) is
   begin
      for Elt of L loop
         Map.Insert (Key      => Elt.Claim,
                     New_Item => Elt.Assumptions);
      end loop;
   end Import;

   ----------------------
   -- Claim_Depends_On --
   ----------------------

   function Claim_Depends_On (C : Token) return Token_Sets.Set is

      use Goal_Maps;

      Needed_Claims     : Token_Sets.Set := Token_Sets.To_Set (C);
      Unverified_Claims : Token_Sets.Set := Token_Sets.Empty_Set;
      Seen              : Token_Sets.Set := Token_Sets.Empty_Set;

      Cur_Token : Token;
      Map_Cur   : Goal_Maps.Cursor;

      Unused   : Token_Sets.Cursor;
      Inserted : Boolean;

   begin
      while not Needed_Claims.Is_Empty loop
         Cur_Token := Needed_Claims (Needed_Claims.First);

         Map_Cur := Map.Find (Cur_Token);

         if Map_Cur = Goal_Maps.No_Element then
            Unverified_Claims.Insert (Cur_Token);

         else
            Seen.Insert (New_Item => Cur_Token,
                         Position => Unused,
                         Inserted => Inserted);

            if Inserted then
               for Tok of Map (Map_Cur) loop
                  Needed_Claims.Include (Tok);
               end loop;
            end if;

         end if;

         Needed_Claims.Delete (Cur_Token);

      end loop;

      return Unverified_Claims;
   end Claim_Depends_On;

   --------------------
   -- Get_All_Claims --
   --------------------

   function Get_All_Claims return Token_Sets.Set is
      S : Token_Sets.Set := Token_Sets.Empty_Set;
   begin
      for Cursor in Map.Iterate loop
         S.Insert (Goal_Maps.Key (Cursor));
      end loop;
      return S;
   end Get_All_Claims;

end Assumptions.Search;
