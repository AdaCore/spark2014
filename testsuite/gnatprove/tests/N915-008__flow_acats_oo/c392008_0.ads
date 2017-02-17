-- C392008.A
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
--      Check that the use of a class-wide formal parameter allows for the
--      proper dispatching of objects to the appropriate implementation of
--      a primitive operation.  Check this for the case where the root tagged
--      type is defined in a package and the extended type is defined in a
--      dependent package.
--
-- TEST DESCRIPTION:
--      Declare a root tagged type, and some associated primitive operations,
--      in a visible library package.
--      Extend the root type in another visible library package, and override
--      one or more primitive operations, inheriting the other primitive
--      operations from the root type.
--      Derive from the extended type in yet another visible library package,
--      again overriding some primitive operations and inheriting others
--      (including some that the parent inherited).
--      Define subprograms with class-wide parameters, inside of which is a
--      call on a dispatching primitive operation.  These primitive
--      operations modify the objects of the specific class passed as actuals
--      to the class-wide formal parameter (class-wide formal parameter has
--      mode IN OUT).
--
-- The following hierarchy of tagged types and primitive operations is
-- utilized in this test:
--
--   package Bank
--      type Account (root)
--            |
--            | Operations
--            |     proc Deposit
--            |     proc Withdrawal
--            |     func Balance
--            |     proc Service_Charge
--            |     proc Add_Interest
--            |     proc Open
--            |
--   package Checking
--      type Account (extended from Bank.Account)
--            |
--            | Operations
--            |     proc Deposit         (inherited)
--            |     proc Withdrawal      (inherited)
--            |     func Balance         (inherited)
--            |     proc Service_Charge  (inherited)
--            |     proc Add_Interest    (inherited)
--            |     proc Open            (overridden)
--            |
--   package Interest_Checking
--      type Account (extended from Checking.Account)
--            |
--            | Operations
--            |     proc Deposit         (inherited twice - Bank.Acct.)
--            |     proc Withdrawal      (inherited twice - Bank.Acct.)
--            |     func Balance         (inherited twice - Bank.Acct.)
--            |     proc Service_Charge  (inherited twice - Bank.Acct.)
--            |     proc Add_Interest    (overridden)
--            |     proc Open            (overridden)
--            |
--
-- In this test, we are concerned with the following selection of dispatching
-- calls, accomplished with the use of a Bank.Account'Class IN OUT formal
-- parameter :
--
--                \ Type
--        Prim. Op \  Bank.Account  Checking.Account Interest_Checking.Account
--                  \---------------------------------------------------------

--   Service_Charge |      X                X                 X
--   Add_Interest   |      X                X                 X
--   Open           |      X                X                 X
--
--
--
-- The location of the declaration of the root and derivation of extended
-- types will be varied over a series of tests.  Locations of declaration
-- and derivation for a particular test are marked with an asterisk (*).
--
-- Root type:
--
--    *  Declared in package.
--       Declared in generic package.
--
-- Extended types:
--
--       Derived in parent location.
--       Derived in a nested package.
--       Derived in a nested subprogram.
--       Derived in a nested generic package.
--    *  Derived in a separate package.
--       Derived in a separate visible child package.
--       Derived in a separate private child package.
--
-- Primitive Operations:
--
--    *  Procedures with same parameter profile.
--       Procedures with different parameter profile.
--       Functions with same parameter profile.
--       Functions with different parameter profile.
--       Mixture of Procedures and Functions.
--
--
-- TEST FILES:
--      This test depends on the following foundation code:
--
--         C392008_0.A
--
--
-- CHANGE HISTORY:
--      06 Dec 94   SAIC    ACVC 2.0
--      20 Nov 95   SAIC    C392B04 became C392008 for ACVC 2.0.1
--
--!

----------------------------------------------------------------- C392008_0

package C392008_0 is           -- package Bank

  type Dollar_Amount is range -30_000..30_000;

   type Account is tagged
      record
        Current_Balance: Dollar_Amount;
      end record;

   -- Primitive operations.

   procedure Deposit        (A : in out Account;
                             X : in     Dollar_Amount);
   procedure Withdrawal     (A : in out Account;
                             X : in     Dollar_Amount);
   function  Balance        (A : in     Account) return Dollar_Amount;
   procedure Service_Charge (A : in out Account);
   procedure Add_Interest   (A : in out Account);
   procedure Open           (A : in out Account);

end C392008_0;
