------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        S P A R K _ A N N O T A T E                       --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                     Copyright (C) 2011-2019, AdaCore                     --
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
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Atree;      use Atree;
with Einfo;      use Einfo;
with SPARK_Util; use SPARK_Util;
with Types;      use Types;

package SPARK_Annotate is

   --  This package deals with justification of individual messages using
   --  pragma Annotate.

   --  The user can suppress check messages emitted by GNATprove by putting a
   --  pragma Annotate in the source code. An example is the following:

   --    return (X + Y) / (X - Y);
   --    pragma Annotate (GNATprove, False_Positive,
   --                     "divide by zero", "reviewed by John Smith");

   --  The pragma has the following form:
   --    pragma Annotate (GNATprove, Category, Pattern, Reason);

   --  where
   --    GNATprove   is a fixed identifier
   --    Category    is one of False_Positive or Intentional
   --    Pattern     is a string literal describing the pattern of the messages
   --                which shall be suppressed
   --    Reason      is a string literal providing a reason for the
   --                suppression.

   --  All arguments should be provided.

   --  The category has no impact on the behavior of the tool, but the idea
   --  is that False_Positive should be used to suppress checks that cannot
   --  occcur, but GNATprove was unable to detect this; Intentional indicates
   --  that the condition can occure but is not considered to be a bug.

   --  Pattern should be a substring of the GNATprove check message to be
   --  suppressed.

   --  Reason is any string that the user can use to provide a reason for the
   --  suppression. This reason may be present in a GNATprove report.

   --  Placement rules are as follows: in a statement list or declaration list,
   --  pragma Annotate applies to the preceding item in the list, ignoring
   --  other pragma Annotate. If there is no preceding item, the pragma applies
   --  to the enclosing entity. If the preceding item is a subprogram body, the
   --  pragma applies both to the body and the spec of the subprogram.

   --  This package also stores uses of pragma Annotate for Iterable_For_Proof
   --  and Inline_For_Proof. This uses are not documented as they are provided
   --  for internal use only.

   --  A pragma Annotate for Iterable_For_Proof has the following form:
   --    pragma Annotate (GNATprove, Iterable_For_Proof, Kind, Entity => E);

   --  where
   --    GNATprove            is a fixed identifier
   --    Iterable_For_Proof   is a fixed identifier
   --    Kind                 must be one of "Model" or "Contains"
   --    E                    is a function entity

   --  If Kind is "Model" then E must have the following signature:
   --    function Get_Model (C : Container_Type) return Model_Type;

   --  where Container_Type and Model_Type both have an Iterable aspect that
   --  allows for ... of quantification on compatible element types.

   --  When such an annotation is provided, for ... of quantification on a
   --  container C is translated as for ... of quantification on its model
   --  Get_Model (C) instead.

   --  If Kind is "Contains" then E must have the following signature:
   --    function Contains (C : Container_Type; X : Element) return Boolean;

   --  where Container_Type have an Iterable aspect that allows for ... of
   --  quantification on elements of type Element.

   --  When such an annotation is provided, for ... of quantification on a
   --  container C is translated in Why3 as quantification over elements
   --  using the provided Contains function.

   --  A pragma Annotate for Inline_For_Proof has the following form:
   --    pragma Annotate (GNATprove, Inline_For_Proof, Entity => E);

   --  where
   --    GNATprove           is a fixed identifier
   --    Inline_For_Proof    is a fixed identifier
   --    E                   is a function entity

   --  and E must either be an expression function or have the following
   --  signature:
   --    function E (...) return ... with
   --      Post => E'Result = Expr;

   --  where Expr must not contain any forward reference to entities defined
   --  after E.

   --  When such an annotation is provided, E is translated as a function
   --  definition in Why3 on which the label "inline" is set so that gnatwhy3
   --  inlines its definition for provers.

   --  A pragma Annotate for termination has the following form:
   --    pragma Annotate (GNATprove, Terminating, Entity => E);

   --  where
   --    GNATprove           is a fixed identifier
   --    Terminating         is a fixed identifier
   --    E                   is a subprogram or a package entity

   --  When such an annotation is provided for a subprogram E, it is assumed to
   --  terminate as far as proof is concerned. If it is provided for a package,
   --  then all the subprograms declared in this package are assumed to
   --  terminate.

   procedure Mark_Pragma_Annotate
     (N             : Node_Id;
      Preceding     : Node_Id;
      Consider_Next : Boolean)
     with Pre => Is_Pragma_Annotate_GNATprove (N) and Present (Preceding);
   --  Call this procedure to register a pragma Annotate. The "Preceding" node
   --  is the node in the tree to which this pragma refers to. If Consider_Next
   --  is true, "Preceding" must be part of a list, and the pragma will
   --  be considered to also apply to all "Next" declarations following
   --  "Preceding" which are not from source.

   type Annotate_Kind is (Intentional, False_Positive);

   type Annotated_Range is record
      Kind    : Annotate_Kind;       --  the kind of pragma Annotate
      Pattern : String_Id;           --  the message pattern
      Reason  : String_Id;           --  the user-provided reason for hiding
      First   : Source_Ptr;          --  first source pointer
      Last    : Source_Ptr;          --  last source pointer
      Prgma   : Node_Id;             --  the pragma which this range belongs to
   end record;

   procedure Check_Is_Annotated
     (Node  : Node_Id;
      Msg   : String;
      Check : Boolean;
      Found : out Boolean;
      Info  : out Annotated_Range);
   --  For a given node and a message string, search if there is a pragma
   --  Annotate that applies to the message for this node. If so, set Found to
   --  True and fill in the Info record. Otherwise, set Found to False and
   --  leave Info uninitialized.

   --  This procedure also marks the corresponding pragma as covering a check.
   --  If Check is True, the pragma is marked as covering a failing check,
   --  otherwise it is marked as covering a proved check.

   procedure Generate_Useless_Pragma_Annotate_Warnings;
   --  Should be called when all messages have been generated. Generates a
   --  warning for all pragma Annotate which do not correspond to a check,
   --  or which covers only proved checks.

   type Iterable_Kind is (Model, Contains);

   type Iterable_Annotation is record
      Kind   : Iterable_Kind;   --  the kind of Annotate Iterable_For_Proof
      Entity : Entity_Id;       --  the entity of the corresponding function
   end record;

   function Retrieve_Inline_Annotation (E : Entity_Id) return Node_Id;
   --  If a pragma Annotate Inline_For_Proof applies to E then returns the
   --  Ada expression that should be used instead of E.

   function Find_Inline_Pragma (E : Entity_Id) return Node_Id with
     Pre  => Present (Retrieve_Inline_Annotation (E)),
     Post => Is_Pragma_Annotate_GNATprove (Find_Inline_Pragma'Result);
   --  If a pragma Annotate Inline_For_Proof applies to E then returns this
   --  pragma. This is used to get better location when checking these pragmas.

   procedure Retrieve_Iterable_Annotation
     (Container_Type : Entity_Id;
      Found          : out Boolean;
      Info           : out Iterable_Annotation);
   --  For a given container type with Iterable aspect, search if there is a
   --  pragma Annotate Iterable_For_Proof that applies to type. If so, set
   --  Found to True and fill in the Info record. Otherwise, set Found to False
   --  and leave Info uninitialized.

   function Has_Might_Not_Return_Annotation (E : Entity_Id) return Boolean
   with Pre => Ekind (E) in Entry_Kind
                          | E_Function
                          | E_Package
                          | E_Procedure
                          | E_Task_Type,
        Post => (if Has_Might_Not_Return_Annotation'Result
                 then Ekind (E) = E_Procedure);
   --  Return True if a pragma Annotate Might_Not_Return applies to entity E

   function Has_Terminate_Annotation (E : Entity_Id) return Boolean;
   --  Return True if a pragma Annotate Terminating applies to the subprogram E

   function Scalar_Has_Init_By_Proof (E : Entity_Id) return Boolean
   with Pre => Is_Type (E);
   --  Return True if a pragma Init_By_Proof applies to the type E

   function Has_Pledge_Annotation (E : Entity_Id) return Boolean;
   --  Return True if the function E is a pledge function

end SPARK_Annotate;
