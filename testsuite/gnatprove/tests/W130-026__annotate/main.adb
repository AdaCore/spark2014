with Library; use Library;

procedure Main with SPARK_Mode is
   X : aliased Boolean := True;
   function Flip (N : Integer; B : Boolean) return Boolean
   is (if N <= 0 then B else Flip (N - 1, not B))
     with Subprogram_Variant => (Decreases => (if N <= 0 then 0 else N));
begin
   declare
      U : not null access Boolean := X'Access;
   begin
      declare
         Y : not null access Boolean := U;
      begin
         for I in 0 .. 70 loop
            pragma Loop_Invariant (Flip (I, Y.all));
            pragma Loop_Invariant (At_End (U).all = At_End (Y).all);
            Y.all := not Y.all;
            Y := Y;
         end loop;
         pragma Assert (Flip (71, Y.all));
      end;
      pragma Assert (Flip (71, U.all));
   end;
   pragma Assert (Flip (71, X));
end Main;
