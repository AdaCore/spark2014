-- C392004.A
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
--      Check that subprograms inherited from tagged derivations, which are
--      subsequently redefined for the derived type, are available to the
--      package defining the new class via view conversion.  Check
--      that operations performed on objects using view conversion do not
--      affect the extended fields.  Check that visible operations not masked
--      by the deriving package remain available to the client, and do not
--      affect the extended fields.
--
-- TEST DESCRIPTION:
--      This test declares a tagged type, with a constructor operation,
--      derives a type from that tagged type, and declares a constructor
--      operation which masks the inherited operation.  It then tests
--      that the correct constructor is called, and that the extended
--      part of the derived type remains untouched as appropriate.
--
--
-- CHANGE HISTORY:
--      06 Dec 94   SAIC    ACVC 2.0
--      19 Dec 94   SAIC    Removed RM references from objective text.
--      04 Jan 94   SAIC    Fixed objective typo, removed dead code.
--
--!

with Report;

package C392004_1 is

  type Vehicle is tagged private;

  procedure Create ( The_Vehicle :    out Vehicle; TC_Flag : Natural );
  procedure Start  ( The_Vehicle : in out Vehicle );

private

  type Vehicle is tagged record
    Engine_On : Boolean;
  end record;

end C392004_1;
