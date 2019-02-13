with Repro.A;

package Repro.B
is

   procedure Foo (Word : A.Word64) with
     Global => (In_Out => A.State),
     Pre    => A.Invariant,
     Post   => A.Invariant;

end Repro.B;
