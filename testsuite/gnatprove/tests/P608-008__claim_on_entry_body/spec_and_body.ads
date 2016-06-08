package spec_and_body is

   X : Integer;

   task type TT is
      pragma Assert (X > 0);
   end;

   protected type PT is
      pragma Assert (X > 0);
   end;

end;
