pragma SPARK_Mode;
procedure Update_Lists_Recursive (Source, Target : in out List; Key : Character) is
   First : List renames Source;
begin
   if First /= null then
      if First.Key = Key then
         declare
            Saved_First : List := First;
         begin
            -- remove First from Source list
            Source := Saved_First.Next;
            -- prepend First at head of Target list
            Saved_First.Next := Target;
            Target := Saved_First;
            -- continue recursively
            Update_Lists_Recursive (Source, Target, Key);
         end;
     else
        -- keep First in Source list
        Update_Lists_Recursive (First.Next, Target, Key);
     end if;
   end if;
end Update_Lists_Recursive;
