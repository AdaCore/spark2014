-- CA11021.A
--
--                             Grant of Unlimited Rights
--
--     Under contracts F33600-87-D-0337, F33600-84-D-0280, MDA903-79-C-0687,
--     F08630-91-C-0015, and DCA100-97-D-0025, the U.S. Government obtained
--     unlimited rights in the software and documentation contained herein.
--     Unlimited rights are defined in DFAR 252.227-7013(a)(19).  By making
--     this public release, the Government intends to confer upon all
--     recipients unlimited rights  equal to those held by the Government.
--     These rights include rights to use, duplicate, release or disclose the
--     released technical data and computer software in whole or in part, in
--     any manner and for any purpose whatsoever, and to have or permit others
--     to do so.
--
--                                    DISCLAIMER
--
--     ALL MATERIALS OR INFORMATION HEREIN RELEASED, MADE AVAILABLE OR
--     DISCLOSED ARE AS IS.  THE GOVERNMENT MAKES NO EXPRESS OR IMPLIED
--     WARRANTY AS TO ANY MATTER WHATSOEVER, INCLUDING THE CONDITIONS OF THE
--     SOFTWARE, DOCUMENTATION OR OTHER INFORMATION RELEASED, MADE AVAILABLE
--     OR DISCLOSED, OR THE OWNERSHIP, MERCHANTABILITY, OR FITNESS FOR A
--     PARTICULAR PURPOSE OF SAID MATERIAL.
--*
--
-- OBJECTIVE:
--      Check that body of the generic parent package can depend on one of
--      its own private generic children.
--
-- TEST DESCRIPTION:
--      A scenario is created that demonstrates the potential of adding a
--      public generic child during code maintenance without distubing a large
--      subsystem.  After child is added to the subsystem, a maintainer
--      decides to take advantage of the new functionality and rewrites
--      the parent's body.
--
--      Declare a generic package which declares high level operations for a
--      complex number abstraction.  Declare a private generic child package
--      of this package which defines low level complex operations. In the
--      parent body, instantiate the private child.  Use the low level
--      operation to complete the high level operation.
--
--      In the main program, instantiate the parent generic package.
--      Check that the operations in both packages perform as expected.
--
--
-- CHANGE HISTORY:
--      06 Dec 94   SAIC    ACVC 2.0
--
--!

generic               -- Complex number abstraction.
   type Int_Type is range <>;

package Parent is

   -- Simulate a generic complex number support package. Complex numbers
   -- are treated as coordinates in the Cartesian plane.

   type Complex_Type is private;

   Zero : constant Complex_Type;                      -- Real number (0,0).

   function Real_Part (Complex_No : Complex_Type)
     return Int_Type;

   function Imag_Part (Complex_No : Complex_Type)
     return Int_Type;

   function Complex (Real, Imag : Int_Type)
     return Complex_Type;

   -- High level operation for complex number.
   function "*" (Factor : Int_Type;
                 C      : Complex_Type) return Complex_Type;

   -- ... and other complicated ones.

private
   type Complex_Type is record
      Real : Int_Type;
      Imag : Int_Type;
   end record;

   Zero : constant Complex_Type := (Real => 0, Imag => 0);

end Parent;
