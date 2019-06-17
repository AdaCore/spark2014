------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--          F L O W _ U T I L I T Y . I N I T I A L I Z A T I O N           --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2014-2019, Altran UK Limited                --
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

--  This package contains utilities related to the (default) initialization
--  of types and objects.

package Flow_Utility.Initialization is

   function Get_Default_Initialization (F : Flow_Id) return Node_Id
   with Pre  => F.Kind in Direct_Mapping | Record_Field,
        Post => (if Present (Get_Default_Initialization'Result)
                 then Nkind (Get_Default_Initialization'Result) in N_Subexpr);
   --  Get the default initialization expression for the given Flow_Id (this
   --  only really works for record fields and direct mappings; magic strings
   --  are assumed to not be default initialized).
   --  @param F is the Flow_Id whose initialization we look for
   --  @return the default initialization expression of F

   function Is_Default_Initialized
     (F          : Flow_Id;
      Scope      : Flow_Scope;
      Ignore_DIC : Boolean := False)
      return Boolean;
   --  Returns True if F is default initialized.
   --  @param F is the Flow_Id whose initialization we look for
   --  @param Scope is the Flow_Scope from where we are looking
   --  @param Ignore_DIC If True then ignore attribute Has_DIC for this type
   --  @return True iff F is fully default initialized

   --  The following type lists all possible kinds of default initialization
   --  that may apply to a type.

   type Default_Initialization_Kind is
     (No_Possible_Initialization,
      --  A type cannot possibly be initialized because it has no content, for
      --  example - a null record.

      Full_Default_Initialization,
      --  A type that combines the following types and content:
      --    * Access type
      --    * Array-of-scalars with specified Default_Component_Value
      --    * Array type with fully default initialized component type
      --    * Record or protected type with components that either have a
      --      default expression or their related types are fully default
      --      initialized.
      --    * Scalar type with specified Default_Value
      --    * Task type
      --    * Type extension of a type with full default initialization where
      --      the extension components are also fully default initialized.

      Mixed_Initialization,
      --  A type where some of its internals are fully default initialized and
      --  some are not.

      No_Default_Initialization
      --  A type where none of its content is fully default initialized
     );

   function Default_Initialization (Typ        : Entity_Id;
                                    Scope      : Flow_Scope;
                                    Ignore_DIC : Boolean := False)
                                    return Default_Initialization_Kind
   with Pre => Is_Type (Typ);
   --  Determine default initialization kind that applies to a particular type.
   --  Types defined in units with external axiomatization (such as formal
   --  containers) and private types are treated specially, so that they are
   --  either considered as having full default initialization, or no default
   --  initialization.
   --  @param Typ any type
   --  @param Scope is the Flow_Scope from where we are looking
   --  @param Ignore_DIC If True then do not consider attribute Has_DIC for
   --     this type.
   --  @return the Default_Initialization_Kind of Typ

end Flow_Utility.Initialization;
