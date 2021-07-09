package Private_Type is
   type Private_Rec is private;

   Zero : constant Private_Rec;
private
   type Private_Rec is record
      A, B : Integer;
   end record;

   Zero : constant Private_Rec := (0, 0);
end Private_Type;
