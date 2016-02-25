generic
   X : in out Integer;
package Gen2 is
   procedure Set (V : Integer)
   with Post => X = V;
end;
