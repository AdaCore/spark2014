------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--               G N A T 2 W H Y - B O R R O W _ C H E C K E R              --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2017-2021, AdaCore                     --
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

--  This package implements an ownership analysis for access types. The rules
--  that are enforced are defined in section 3.10 of the SPARK Reference
--  Manual.
--
--  A path is an abstraction of a name, of which all indices, slices (for
--  indexed components) and function calls have been abstracted and all
--  dereferences are made explicit. A path is the atomic element viewed by the
--  analysis, with the notion of prefixes and extensions of different paths.
--
--  The analysis explores the AST, and looks for different constructs
--  that may involve aliasing. These main constructs are assignments
--  (N_Assignment_Statement, N_Object_Declaration, ...), or calls
--  (N_Procedure_Call_Statement, N_Entry_Call_Statement, N_Function_Call).
--  The analysis checks the permissions of each construct and updates them
--  according to the SPARK RM. This can follow three main different types
--  of operations: move, borrow, and observe.

----------------------------
-- Deep and shallow types --
----------------------------

--  The analysis focuses on objects that can cause problems in terms of pointer
--  aliasing. These objects have types that are called deep. Deep types are
--  defined as being either types with an access part or class-wide types
--  (which may have an access part in a derived type).

----------
-- Move --
----------

--  Moves can happen at several points in the program: during assignment (and
--  any similar statement such as object declaration with initial value), or
--  during return statements.
--
--  The underlying concept consists of transferring the ownership of any path
--  on the right-hand side to the left-hand side. There are some details that
--  should be taken into account so as not to transfer paths that appear only
--  as intermediate results of a more complex expression.

--  More specifically, the SPARK RM defines moved expressions, and any moved
--  expression that points directly to a path is then checked and sees its
--  permissions updated accordingly.

------------
-- Borrow --
------------

--  Borrows can happen in subprogram calls. They consist of a temporary
--  transfer of ownership from a caller to a callee. Expressions that can be
--  borrowed can be found in either procedure or entry actual parameters, and
--  consist of parameters of mode either "out" or "in out", or parameters of
--  mode "in" that are of type nonconstant access-to-variable. We consider
--  global variables as implicit parameters to subprograms, with their mode
--  given by the Global contract associated to the subprogram. Note that the
--  analysis looks for such a Global contract mentioning any global variable
--  of deep type accessed directly in the subprogram, and it raises an error if
--  there is no Global contract, or if the Global contract does not mention the
--  variable.
--
--  A borrow of a parameter X is equivalent in terms of aliasing to moving
--  X'Access to the callee, and then assigning back X at the end of the call.
--
--  Borrowed parameters should have read-write permission (or write-only for
--  "out" parameters), and should all have read-write permission at the end
--  of the call (this guarantee is ensured by the callee).

-------------
-- Observe --
-------------

--  Observed parameters are all the other parameters that are not borrowed and
--  that may cause problems with aliasing. They are considered as being sent to
--  the callee with Read-Only permission, so that they can be aliased safely.
--  This is the only construct that allows aliasing that does not prevent
--  accessing the old path that is being aliased. However, this comes with
--  the restriction that those aliased path cannot be written in the callee.

--------------------
-- Implementation --
--------------------

--  The implementation is based on trees that represent the possible paths
--  in the source code. Those trees can be unbounded in depth, hence they are
--  represented using lazy data structures, whose laziness is handled manually.
--  Each time an identifier is declared, its path is added to the permission
--  environment as a tree with only one node, the declared identifier. Each
--  time a path is checked or updated, we look in the tree at the adequate
--  node, unfolding the tree whenever needed.

--  For this, each node has several variables that indicate whether it is
--  deep (Is_Node_Deep), what permission it has (Permission), and what is
--  the lowest permission of all its descendants (Children_Permission). After
--  unfolding the tree, we update the permissions of each node, deleting the
--  Children_Permission, and specifying new ones for the leaves of the unfolded
--  tree.

--  After assigning a path, the descendants of the assigned path are dumped
--  (and hence the tree is folded back), given that all descendants directly
--  get read-write permission, which can be specified using the node's
--  Children_Permission field.

with Types; use Types;

package Gnat2Why.Borrow_Checker is

   procedure Check_Entity (E : Entity_Id);
   --  The entry point of this package. It analyzes an entity and reports
   --  errors when there are violations of ownership rules.

   function Found_Permission_Error return Boolean;
   --  Return True if an error has been emitted during permission checking

end Gnat2Why.Borrow_Checker;
