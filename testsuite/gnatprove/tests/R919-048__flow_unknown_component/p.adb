with Other;

package body P with Refined_State => (State => Y) is
   Y : Integer := 0;

   procedure Main with Refined_Global => Y is
   begin
      Other.X.C := Y;
      --  Other.X should be listed in both Refined_Global and Global
   end;
end;
