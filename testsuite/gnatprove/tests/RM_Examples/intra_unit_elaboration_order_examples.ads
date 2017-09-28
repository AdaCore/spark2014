with Times_2;

package Intra_Unit_Elaboration_Order_Examples
  with Initializes => (X, Y)
is
   pragma Elaborate_Body;  --  Ensures body of package is elaborated
                           --  immediately after its declaration
   procedure P (I : in out Integer); --  P and hence Q are executable during
   procedure Q (J : in out Integer); --  elaboration as P is called in the
                                     --  package body

   X : Integer := Times_2 (10);  --  Not preelaborable
                                 --  The early call region begins here
                                 --  and extends into the package body because
                                 --  of the Elaborate_Body pragma.

   Y : Integer;

   procedure R (Z : in out Integer)
     with Post => Z = G (Z'Old); --  The call to G is allowed here as it is in
                                 --  the early call region

   procedure S (A : in out Integer)
     with Global => Y;           --  Global Y needs to be initialized.

   function F (I : Integer) return Integer;
   function G (J : Integer) return Integer is (2 * F (J));
   --  The call to F is allowed here as it is in
   --  early call region.
end Intra_Unit_Elaboration_Order_Examples;
