------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--          F L O W _ U T I L I T Y . I N I T I A L I Z A T I O N           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2014-2017, Altran UK Limited              --
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

with Aspects;          use Aspects;
with Nlists;           use Nlists;
with Sem_Type;         use Sem_Type;
with SPARK_Util;       use SPARK_Util;
with SPARK_Util.Types; use SPARK_Util.Types;
with Why;

package body Flow_Utility.Initialization is

   --------------------------------
   -- Get_Default_Initialization --
   --------------------------------

   function Get_Default_Initialization (F : Flow_Id) return Node_Id is
      function Get_Component_From_Aggregate (A : Node_Id;
                                             C : Node_Id)
                                             return Node_Id;
      --  If we have a record aggregate A like (X => Y, Z => W), this returns
      --  the value attached to component C, for example if C is Z this will
      --  return W.

      function Get_Simple_Default (E : Entity_Id) return Node_Id;
      --  Recursively look for simple default values given by Default_Value and
      --  Default_Component_Value.

      ----------------------------------
      -- Get_Component_From_Aggregate --
      ----------------------------------

      function Get_Component_From_Aggregate
        (A : Node_Id;
         C : Node_Id)
         return Node_Id
      is
         N : Node_Id;
      begin
         N := First (Component_Associations (A));
         while Present (N) loop
            case Nkind (N) is
               when N_Component_Association =>
                  if Entity (First (Choices (N))) = C then
                     return Expression (N);
                  end if;

               when others =>
                  raise Why.Unexpected_Node;
            end case;

            N := Next (N);
         end loop;

         --  So, we can't find the component we're looking for; this means
         --  we have some kind of discriminated type with a variant part;
         --  and we statically know some part is not present. We return
         --  Empty in this case to gracefully handle it (as flow analyis
         --  always initializes 'all' components on aggregate assignments).
         return Empty;
      end Get_Component_From_Aggregate;

      ------------------------
      -- Get_Simple_Default --
      ------------------------

      function Get_Simple_Default (E : Entity_Id) return Node_Id is
      begin
         if Has_Aspect (E, Aspect_Default_Value) then
            return Expression (Find_Aspect (E, Aspect_Default_Value));
         elsif Has_Aspect (E, Aspect_Default_Component_Value) then
            return Expression
              (Find_Aspect (E, Aspect_Default_Component_Value));
         else
            case Ekind (E) is
               when E_Array_Subtype =>
                  return Get_Simple_Default (Etype (E));

               when E_Array_Type =>
                  return Get_Simple_Default (Component_Type (E));

               when others =>
                  return Empty;
            end case;
         end if;
      end Get_Simple_Default;

      N       : Node_Id;
      Comp_Id : Positive;

   --  Start of processing for Get_Default_Initialization

   begin
      case F.Kind is
         when Direct_Mapping =>
            return Get_Simple_Default (Etype (Get_Direct_Mapping_Id (F)));

         when Record_Field =>
            --  If the Flow_Id represents the 'Hidden part of a record then we
            --  do not consider it to be initialized.
            if Is_Private_Part (F)
              or else Is_Extension (F)
              or else Is_Record_Tag (F)
            then
               return Empty;
            end if;

            --  We need to find the first one with a default initialization as
            --  that would overwrite any default initialization we might find
            --  later.
            Comp_Id := 1;
            for Comp of F.Component loop
               N := Expression (Parent (Comp));
               if Present (N) then
                  --  This is a field with a default initalization

                  --  We can try and untangle any record aggregates
                  while Comp_Id < Positive (F.Component.Length)
                    and then Nkind (N) = N_Aggregate
                  loop
                     Comp_Id := Comp_Id + 1;
                     N := Get_Component_From_Aggregate
                       (N,
                        F.Component (Comp_Id));
                  end loop;

                  return N;
               end if;

               Comp_Id := Comp_Id + 1;
            end loop;

            --  We need to check if the type itself is always initialized
            return Get_Simple_Default (Etype (F.Component.Last_Element));

         when Magic_String | Synthetic_Null_Export =>
            return Empty;

         when Null_Value =>
            raise Why.Unexpected_Node;
      end case;
   end Get_Default_Initialization;

   ----------------------------
   -- Is_Default_Initialized --
   ----------------------------

   function Is_Default_Initialized
     (F             : Flow_Id;
      Explicit_Only : Boolean := False)
      return Boolean
   is

      function Has_Full_Default_Initialization (E : Entity_Id) return Boolean;
      --  Returns True iff F has full default initialization

      ---------------------------------
      -- Has_Full_Default_Initialization --
      ---------------------------------

      function Has_Full_Default_Initialization (E : Entity_Id) return Boolean
      is
         Typ : Entity_Id;
      begin
         case Ekind (E) is
            when E_Abstract_State =>
               return False;

            when Type_Kind =>
               Typ := E;

            when others =>
               Typ := Etype (E);
         end case;

         return Default_Initialization (Typ, Explicit_Only) =
                  Full_Default_Initialization;
      end Has_Full_Default_Initialization;

   --  Start of processing for Is_Default_Initialized

   begin
      case F.Kind is
         when Direct_Mapping =>
            declare
               E : constant Entity_Id := Get_Direct_Mapping_Id (F);
            begin
               return Is_Imported (E)
                 or else In_Generic_Actual (E)
                 or else Has_Full_Default_Initialization (E);
            end;

         when Record_Field =>
            if In_Generic_Actual (Get_Direct_Mapping_Id (F)) then
               return True;
            end if;

            if Is_Discriminant (F) then
               return Present (Discriminant_Default_Value
                                 (F.Component.Last_Element));

            elsif Is_Record_Tag (F)
              or else Is_Imported (Get_Direct_Mapping_Id (F))
            then
               return True;

            else
               return Has_Full_Default_Initialization
                        (Get_Direct_Mapping_Id (F));
            end if;

         when Magic_String | Synthetic_Null_Export =>
            return False;

         when Null_Value =>
            raise Why.Unexpected_Node;
      end case;
   end Is_Default_Initialized;

end Flow_Utility.Initialization;
