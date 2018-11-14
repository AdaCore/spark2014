generic
package GP.GC is
   procedure Test with Global => null;
   --  This contract is intentionally wrong; it should be (In_Out => State)
end;
