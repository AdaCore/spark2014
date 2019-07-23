with Other;
package P.Priv.Pub is
private
   C : constant Integer := Other.V;
   --  Constant with variable input; it should be Part_Of a state declared in
   --  this package, which in turn should be Part_Of => P.State.
end;
