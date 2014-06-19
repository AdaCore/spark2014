generic
  G : in out Integer;
package Gen is
   procedure Set (V : Integer) with
     Global => (Output => G),
     Post   => G = V;
   function Get return Integer with
     Global => (Input => G);
end Gen;
