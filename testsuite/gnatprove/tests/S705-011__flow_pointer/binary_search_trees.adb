package body Binary_Search_Trees is

   procedure Invalidate (Starting_At : not null Node_Access)
   is
   begin
      if Starting_At.Right /= null or else Starting_At.Left /= null then
         Starting_At.Right := null;
         Starting_At.Left  := null;
      else
         Dummy := not Dummy;
      end if;
   end Invalidate;

end Binary_Search_Trees;
