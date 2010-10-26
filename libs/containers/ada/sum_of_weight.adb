function Sum_Of_Weight (L : DLL.List) return Integer is
   Res : Integer := 0;
   Cu : DLL.Cursor := DLL.First(L);
begin
   while DLL.Has_Element(Cu) loop
      Res := Res + Weight(DLL.Element(Cu));
      DLL.Next(Cu);
   end loop;
   return Res;
end Sum_Of_Weight;
