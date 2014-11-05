------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                       F L O W _ C L A S S W I D E                        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                    Copyright (C) 2014, Altran UK Limited                 --
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
------------------------------------------------------------------------------

--  with Output;              use Output;
--  with Treepr;              use Treepr;

with Flow_Error_Messages; use Flow_Error_Messages;
with Flow_Refinement;     use Flow_Refinement;
with Flow_Types;          use Flow_Types;
with Flow_Utility;        use Flow_Utility;

--  with Flow_Debug;          use Flow_Debug;

package body Flow_Classwide is

   function Has_Controlling_Formal_Or_Result (E : Entity_Id) return Boolean
   with Pre => Nkind (E) in N_Entity and then
               Ekind (E) in Subprogram_Kind;
   --  Checks if the given subprogram is primitive with either a
   --  controlling formal parameter or a result (for functions).

   procedure Check_Classwide_Global (E     : Entity_Id;
                                     Scope : Flow_Scope;
                                     Valid : in out Boolean)
   with Pre => Nkind (E) in N_Entity and then
               Ekind (E) in Subprogram_Kind and then
               Has_Controlling_Formal_Or_Result (E);
   --  Enforce the rules of SRM 6.1.6

   --------------------------------------
   -- Has_Controlling_Formal_Or_Result --
   --------------------------------------

   function Has_Controlling_Formal_Or_Result (E : Entity_Id) return Boolean
   is
      Ptr : Node_Id;
   begin
      if not Is_Primitive (E) then
         return False;
      end if;

      if Ekind (E) = E_Function and then Has_Controlling_Result (E) then
         return True;
      end if;

      Ptr := First_Formal (E);
      while Present (Ptr) loop
         if Is_Controlling_Formal (Ptr) then
            return True;
         end if;
         Next_Formal (Ptr);
      end loop;

      return False;
   end Has_Controlling_Formal_Or_Result;

   ----------------------------
   -- Check_Classwide_Global --
   ----------------------------

   procedure Check_Classwide_Global (E     : Entity_Id;
                                     Scope : Flow_Scope;
                                     Valid : in out Boolean)
   is
      pragma Unreferenced (Valid);

      Anc_Proof : Flow_Id_Sets.Set;
      Anc_Reads : Flow_Id_Sets.Set;
      Anc_Write : Flow_Id_Sets.Set;

      My_Proof : Flow_Id_Sets.Set;
      My_Reads : Flow_Id_Sets.Set;
      My_Write : Flow_Id_Sets.Set;

      Unused : Boolean;

      Ancestor : Flow_Id;

      function Mode (F : Flow_Id) return String;
      --  Given F, check if its a proof_in, input, in_out or output.

      function Mode (F : Flow_Id) return String
      is
         subtype Valid_Param_Mode is Param_Mode range Mode_Proof .. Mode_Out;

         F_In  : constant Flow_Id := Change_Variant (F, In_View);
         F_Out : constant Flow_Id := Change_Variant (F, Out_View);

         M : Param_Mode := Mode_Invalid;
      begin
         if My_Proof.Contains (F_In) then
            M := Mode_Proof;
         elsif My_Reads.Contains (F_In) then
            if My_Write.Contains (F_Out) then
               M := Mode_In_Out;
            else
               M := Mode_In;
            end if;
         elsif My_Write.Contains (F_Out) then
            M := Mode_Out;
         end if;

         case Valid_Param_Mode (M) is
            when Mode_Proof  => return "proof_in";
            when Mode_In     => return "input";
            when Mode_In_Out => return "in_out";
            when Mode_Out    => return "output";
         end case;
      end Mode;

   begin
      if No (Overridden_Operation (E)) then
         --  This subprogram is not overriding, hence there can't be a
         --  problem currently. (Since we assume Global'Class = Global.)
         return;
      end if;

      Ancestor := Direct_Mapping_Id (Overridden_Operation (E));

      Get_Globals (Subprogram => Overridden_Operation (E),
                   Scope      => Scope,
                   Classwide  => True,
                   Proof_Ins  => Anc_Proof,
                   Reads      => Anc_Reads,
                   Writes     => Anc_Write);

      Get_Globals (Subprogram => E,
                   Scope      => Scope,
                   Classwide  => True,
                   Proof_Ins  => My_Proof,
                   Reads      => My_Reads,
                   Writes     => My_Write);

      --  A Global or Global’Class aspect specification G2 is said to be a
      --  valid overriding of another such specification, G1, if the
      --  following conditions are met:

      --  each Input-mode item of G2 is an Input-mode or an In_Out-mode item
      --  of G1 or a direct or indirect constituent thereof; and
      for F of My_Proof loop
         if not (Anc_Proof.Contains (F) or Anc_Reads.Contains (F)) then
            Error_Msg_Flow
              (E          => E,
               Msg        =>
                 "class-wide proof_in & must also be a " &
                 "class-wide (proof) input " &
                 "of overridden subprogram #",
               Kind       => Error_Kind,
               N          => E,
               Suppressed => Unused,
               F1         => F,
               F2         => Ancestor,
               SRM_Ref    => "6.1.6");
         end if;
      end loop;

      for F of My_Reads loop
         if not Anc_Reads.Contains (F) then
            Error_Msg_Flow
              (E          => E,
               Msg        =>
                 "class-wide " & Mode (F) & " & must also be a " &
                 "class-wide input " &
                 "of overridden subprogram #",
               Kind       => Error_Kind,
               N          => E,
               Suppressed => Unused,
               F1         => F,
               F2         => Ancestor,
               SRM_Ref    => "6.1.6");
         end if;
      end loop;

      --  each Output-mode item of G2 is an Output-mode or In_Out-mode item
      --  of G1 or a direct or indirect constituent therof; and
      for F of My_Write loop
         if not Anc_Write.Contains (F) then
            Error_Msg_Flow
              (E          => E,
               Msg        =>
                 "class-wide " & Mode (F) & " & must also be a " &
                 "class-wide output " &
                 "of overridden subprogram #",
               Kind       => Error_Kind,
               N          => E,
               Suppressed => Unused,
               F1         => F,
               F2         => Ancestor,
               SRM_Ref    => "6.1.6");
         end if;
      end loop;

      --  each In_Out-mode item of G2 is an In_Out-mode item of G1 or a
      --  direct or indirect constituent thereof; and

      --  The above two checks imply this one since in and out aspects are
      --  dealt with separately.

      --  each Output-mode item of G1 which is not a state abstraction whose
      --  refinment is visible at the point of G2 is an Output-mode item of
      --  G2; and

      --  for each Output-mode item of G1 which is a state abstraction whose
      --  refinment is visible at the point of G2, each direct or indirect
      --  constituent thereof is an Output-mode item of G2.
      for F_Out of Anc_Write loop
         declare
            F_In : constant Flow_Id := Change_Variant (F_Out, In_View);
         begin
            if not (Anc_Reads.Contains (F_In) or Anc_Proof.Contains (F_In))
              and then (My_Reads.Contains (F_In) or My_Proof.Contains (F_In))
            then
               Error_Msg_Flow
                 (E          => E,
                  Msg        =>
                    "class-wide output & of overridden subprogram # " &
                    "must also be a " &
                    "class-wide output here",
                  Kind       => Error_Kind,
                  N          => E,
                  Suppressed => Unused,
                  F1         => F_Out,
                  F2         => Ancestor,
                  SRM_Ref    => "6.1.6");
            end if;
         end;
      end loop;

   end Check_Classwide_Global;

   -------------------------------
   -- Check_Classwide_Contracts --
   -------------------------------

   procedure Check_Classwide_Contracts (E     : Entity_Id;
                                        Valid : out Boolean)
   is
      Scope : constant Flow_Scope := Get_Flow_Scope (E);
   begin
      Valid := True;
      if Has_Controlling_Formal_Or_Result (E) then
         Check_Classwide_Global (E, Scope, Valid);
      end if;
   end Check_Classwide_Contracts;

end Flow_Classwide;
