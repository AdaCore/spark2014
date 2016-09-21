------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                       F L O W _ C L A S S W I D E                        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                    Copyright (C) 2014-2016, Altran UK Limited            --
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

with Flow_Dependency_Maps; use Flow_Dependency_Maps;
with Flow_Error_Messages;  use Flow_Error_Messages;
with Flow_Refinement;      use Flow_Refinement;
with Flow_Types;           use Flow_Types;
with Flow_Utility;         use Flow_Utility;
with Sem_Util;             use Sem_Util;
with Snames;               use Snames;

package body Flow_Classwide is

   function Has_Controlling_Formal_Or_Result (E : Entity_Id) return Boolean
   with Pre => Is_Subprogram (E);
   --  Checks if the given subprogram is primitive with either a
   --  controlling formal parameter or a result (for functions).

   procedure Check_Classwide_Global (E     : Entity_Id;
                                     Scope : Flow_Scope;
                                     Valid : in out Boolean)
   with Pre => Is_Subprogram (E) and then
               Has_Controlling_Formal_Or_Result (E);
   --  Enforce the rules of SRM 6.1.6

   procedure Check_Classwide_Depends (E     : Entity_Id;
                                      Scope : Flow_Scope;
                                      Valid : in out Boolean)
   with Pre => Is_Subprogram (E) and then
               Has_Controlling_Formal_Or_Result (E);
   --  Enforce the rules of SRM 6.1.6

   --------------------------------------
   -- Has_Controlling_Formal_Or_Result --
   --------------------------------------

   function Has_Controlling_Formal_Or_Result (E : Entity_Id) return Boolean is
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
      Anc_Proof : Flow_Id_Sets.Set;
      Anc_Reads : Flow_Id_Sets.Set;
      Anc_Write : Flow_Id_Sets.Set;

      My_Proof : Flow_Id_Sets.Set;
      My_Reads : Flow_Id_Sets.Set;
      My_Write : Flow_Id_Sets.Set;

      Suppressed : Boolean;

      Ancestor : constant Flow_Id :=
        Direct_Mapping_Id (Overridden_Operation (E));

      function Mode (F : Flow_Id) return String;
      --  Given F, check if its a proof_in, input, in_out or output

      ----------
      -- Mode --
      ----------

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

         return
           (case Valid_Param_Mode (M) is
               when Mode_Proof  => "proof_in",
               when Mode_In     => "input",
               when Mode_In_Out => "in_out",
               when Mode_Out    => "output");
      end Mode;

   --  Start of processing for Check_Classwide_Global

   begin
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

      --  A Global or Global'Class aspect specification G2 is said to be a
      --  valid overriding of another such specification, G1, if the
      --  following conditions are met:

      --  each Input-mode item of G2 is an Input-mode or an In_Out-mode item
      --  of G1 or a direct or indirect constituent thereof; and
      for F of My_Proof loop
         if not (Anc_Proof.Contains (F) or else Anc_Reads.Contains (F)) then
            Error_Msg_Flow
              (E          => E,
               Msg        =>
                 "class-wide proof_in & must also be a " &
                 "class-wide (proof) input " &
                 "of overridden subprogram #",
               Severity   => Error_Kind,
               N          => E,
               Suppressed => Suppressed,
               F1         => F,
               F2         => Ancestor,
               SRM_Ref    => "6.1.6");
            if not Suppressed then
               Valid := False;
            end if;
         end if;
      end loop;

      for F of My_Reads loop
         if not Anc_Reads.Contains (F) then
            Error_Msg_Flow
              (E          => E,
               Msg        =>
                 "class-wide " & Mode (F) & " & must also be a " &
                 "class-wide input of overridden subprogram #",
               Severity   => Error_Kind,
               N          => E,
               Suppressed => Suppressed,
               F1         => F,
               F2         => Ancestor,
               SRM_Ref    => "6.1.6");
            if not Suppressed then
               Valid := False;
            end if;
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
                 "class-wide output of overridden subprogram #",
               Severity   => Error_Kind,
               N          => E,
               Suppressed => Suppressed,
               F1         => F,
               F2         => Ancestor,
               SRM_Ref    => "6.1.6");
            if not Suppressed then
               Valid := False;
            end if;
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
            if not (Anc_Reads.Contains (F_In)
                    or else Anc_Proof.Contains (F_In))
              and then (My_Reads.Contains (F_In)
                        or else My_Proof.Contains (F_In))
            then
               Error_Msg_Flow
                 (E          => E,
                  Msg        =>
                    "class-wide output & of overridden subprogram # " &
                    "must also be a class-wide output here",
                  Severity   => Error_Kind,
                  N          => E,
                  Suppressed => Suppressed,
                  F1         => F_Out,
                  F2         => Ancestor,
                  SRM_Ref    => "6.1.6");
               if not Suppressed then
                  Valid := False;
               end if;
            end if;
         end;
      end loop;

   end Check_Classwide_Global;

   -----------------------------
   -- Check_Classwide_Depends --
   -----------------------------

   procedure Check_Classwide_Depends (E     : Entity_Id;
                                      Scope : Flow_Scope;
                                      Valid : in out Boolean)
   is
      use type Flow_Id_Sets.Set;

      function Get_Or_Make_Depends (E         : Entity_Id;
                                    Classwide : Boolean)
                                    return Dependency_Maps.Map
      with Pre => Is_Subprogram (E);
      --  Obtain the dependency relation for E, or synthesize one

      -------------------------
      -- Get_Or_Make_Depends --
      -------------------------

      function Get_Or_Make_Depends (E         : Entity_Id;
                                    Classwide : Boolean)
                                    return Dependency_Maps.Map
      is
         M       : Dependency_Maps.Map;

         Void    : Flow_Id_Sets.Set;
         Outputs : Flow_Id_Sets.Set;
         Inputs  : Flow_Id_Sets.Set;
      begin
         if Has_Depends (E) then
            Get_Depends (Subprogram => E,
                         Scope      => Scope,
                         Classwide  => Classwide,
                         Depends    => M);
         else
            --  Assemble the final dependency from globals...
            declare
               Proof : Flow_Id_Sets.Set;
               Reads : Flow_Id_Sets.Set;
               Write : Flow_Id_Sets.Set;
            begin
               Get_Globals (Subprogram => E,
                            Scope      => Scope,
                            Classwide  => Classwide,
                            Proof_Ins  => Proof,
                            Reads      => Reads,
                            Writes     => Write);
               Void    := Change_Variant (Proof, Normal_Use);
               Inputs  := Change_Variant (Reads, Normal_Use);
               Outputs := Change_Variant (Write, Normal_Use);
            end;

            --  ... all parameters...
            for P of Get_Formals (E) loop
               declare
                  Formal : constant Flow_Id :=
                    Direct_Mapping_Id (Unique_Entity (P));
                  --  We do not need an In_View/Out_View here, so do not care

               begin
                  case Ekind (P) is
                     when E_In_Parameter     =>
                        Inputs.Include (Formal);

                     when E_Out_Parameter    =>
                        Outputs.Include (Formal);

                     when E_In_Out_Parameter =>
                        Inputs.Include (Formal);
                        Outputs.Include (Formal);

                     --  ??? this is never executed; and what are the "others"?
                     when others             =>
                        Inputs.Include (Formal);

                        if Ekind (E) /= E_Function then
                           Outputs.Include (Formal);
                        end if;
                  end case;
               end;
            end loop;

            --  ... and the function symbol if we're dealing with a function
            if Ekind (E) = E_Function then
               Outputs.Include (Direct_Mapping_Id (E));
            end if;

            M := Dependency_Maps.Empty_Map;
            for F of Outputs loop
               M.Include (F, Inputs);
            end loop;
            if not Void.Is_Empty then
               M.Include (Null_Flow_Id, Void);
            end if;
         end if;

         return M;
      end Get_Or_Make_Depends;

      Ancestor   : constant Flow_Id :=
        Direct_Mapping_Id (Overridden_Operation (E));

      Anc_Dep    : constant Dependency_Maps.Map :=
        Get_Or_Make_Depends (Overridden_Operation (E), True);
      My_Dep     : constant Dependency_Maps.Map :=
        Get_Or_Make_Depends (E, True);

      Suppressed : Boolean;

      My_To_Anc  : Flow_Id_Surjection.Map := Flow_Id_Surjection.Empty_Map;
      Anc_To_My  : Flow_Id_Surjection.Map := Flow_Id_Surjection.Empty_Map;
   begin
      --  The entities in the depends for E and its ancestor are different.
      --  We construct two maps that translate either way.
      declare
         Anc_Ptr : Node_Id := First_Formal (Overridden_Operation (E));
         My_Ptr  : Node_Id := First_Formal (E);
      begin
         while Present (Anc_Ptr) and Present (My_Ptr) loop
            My_To_Anc.Include (Direct_Mapping_Id (My_Ptr),
                               Direct_Mapping_Id (Anc_Ptr));
            Anc_To_My.Include (Direct_Mapping_Id (Anc_Ptr),
                               Direct_Mapping_Id (My_Ptr));
            Next_Formal (Anc_Ptr);
            Next_Formal (My_Ptr);
         end loop;
         if Ekind (E) = E_Function then
            My_To_Anc.Include (Direct_Mapping_Id (E),
                               Direct_Mapping_Id (Overridden_Operation (E)));
            Anc_To_My.Include (Direct_Mapping_Id (Overridden_Operation (E)),
                               Direct_Mapping_Id (E));
         end if;
         pragma Assert (Present (Anc_Ptr) = Present (My_Ptr));
      end;

      --  We now check that My_Dep is a strict subset of Anc_Dep

      for C in My_Dep.Iterate loop
         declare
            My_Output  : Flow_Id          renames Dependency_Maps.Key (C);
            My_Inputs  : Flow_Id_Sets.Set renames My_Dep (C);

            Anc_Inputs : Flow_Id_Sets.Set;
            Tmp        : Flow_Id_Sets.Set;
         begin
            --  We skip checking the null => blah dependency, since a) the
            --  ancestor might not have it, b) moving anything to it is OK
            --  (i.e. its fine if this one is a superset).
            if Present (My_Output) then
               Anc_Inputs := Anc_Dep ((if My_To_Anc.Contains (My_Output)
                                       then My_To_Anc (My_Output)
                                       else My_Output));
               Tmp := My_Inputs;
               for F of Anc_Inputs loop
                  Tmp.Exclude ((if Anc_To_My.Contains (F)
                                then Anc_To_My (F)
                                else F));
               end loop;
            else
               Tmp := Flow_Id_Sets.Empty_Set;
            end if;

            for F of To_Ordered_Flow_Id_Set (Tmp) loop
               Error_Msg_Flow
                 (E          => E,
                  Msg        =>
                    "class-wide dependency ""% => %"" is not a " &
                    "class-wide dependency of overridden subprogram #",
                  Severity   => Error_Kind,
                  N          => Search_Contract
                                  (E,
                                   Pragma_Depends,
                                   Get_Direct_Mapping_Id (My_Output),
                                   Get_Direct_Mapping_Id (F)),
                  Suppressed => Suppressed,
                  F1         => My_Output,
                  F2         => F,
                  F3         => Ancestor,
                  SRM_Ref    => "6.1.6");
               if not Suppressed then
                  Valid := False;
               end if;
            end loop;
         end;
      end loop;

   end Check_Classwide_Depends;

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
         if Present (Overridden_Operation (E)) then

            Check_Classwide_Global (E, Scope, Valid);

            if Valid then
               Check_Classwide_Depends (E, Scope, Valid);
            end if;

         --  This subprogram is not overriding, hence there can't be a problem
         --  currently. (Since we assume both global'class and depends'class
         --  are equal to their non-class-wide versions.)

         else
            null;
         end if;
      end if;
   end Check_Classwide_Contracts;

end Flow_Classwide;
